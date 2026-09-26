"""
Source-level control-flow deflattening for ironbrew1's VM (the VM's own Luau
source is flattened; the payload bytecode is a separate layer).

Shape (both schemes seen so far):

    <key init>; S = <transition>
    while true do / while S ~= X do / repeat ... until false
        if S == EXIT then break end
        if S < c1 then if S >= c2 then ... if S == c3 then <block> <transition> continue ...

A transition updates the control variables (the state S plus "key"
variables, e.g. `ed = (ed * 12) + c; ed = ed % 4096; ea = eb[ed + K] or
ec(a, b, c)` or `e, bg = bh[2613] + bg * 4, (bg * -7 - 455) % 4096`). They
are pure functions of constants, constant tables and the control variables
(the `eb[...] or ec(...)` table is a cache of ec's result), so a small
interpreter follows (S, keys) pairs through the dispatch: every reachable
pair is one original basic block. Branches on real values fork.

Result: each flattened loop becomes a Graph node (labeled blocks with
gotos) in the AST; `render` prints it as pseudo-Luau with `goto`.

    python -m obfuscators.ironbrew1.deflatten file.lua > out.lua   (from deobf/)
"""
import math
import sys

MAXNODES = 20000


class NotConst(Exception):
    pass


NIL = None


def lkey(loc):
    """identity of an AstLocal"""
    return (loc["name"], loc.get("location"))


# ---------------------------------------------------------------------------
# constant folding (sample3 writes numbers as `(891 + 33)`)

def _num(v):
    return {"type": "AstExprConstantNumber", "value": v}


def arith(op, a, b):
    if not isinstance(a, (int, float)) or isinstance(a, bool) or not isinstance(b, (int, float)) or isinstance(b, bool):
        raise NotConst(op)
    if op == "Add":
        return a + b
    if op == "Sub":
        return a - b
    if op == "Mul":
        return a * b
    if op == "Div":
        if b == 0:
            raise NotConst("div0")
        r = a / b
        return int(r) if r == int(r) and abs(r) < 2 ** 53 else r
    if op == "FloorDiv":
        if b == 0:
            raise NotConst("div0")
        return math.floor(a / b) if isinstance(a, float) or isinstance(b, float) else a // b
    if op == "Mod":
        if b == 0:
            raise NotConst("mod0")
        return a - math.floor(a / b) * b if isinstance(a, float) or isinstance(b, float) else a % b
    if op == "Pow":
        return a ** b
    raise NotConst(op)


def fold(e):
    """Fold pure numeric subexpressions in place (returns the new node)."""
    if isinstance(e, list):
        for i, x in enumerate(e):
            e[i] = fold(x)
        return e
    if not isinstance(e, dict):
        return e
    for k, v in list(e.items()):
        if isinstance(v, (dict, list)) and k not in ("local", "location"):
            e[k] = fold(v)
    t = e.get("type")
    if t == "AstExprGroup" and e["expr"]["type"] == "AstExprConstantNumber":
        return e["expr"]
    if t == "AstExprUnary" and e["op"] == "Minus" and e["expr"]["type"] == "AstExprConstantNumber":
        return _num(-e["expr"]["value"])
    if (t == "AstExprBinary" and e["left"]["type"] == "AstExprConstantNumber"
            and e["right"]["type"] == "AstExprConstantNumber"):
        try:
            return _num(arith(e["op"], e["left"]["value"], e["right"]["value"]))
        except NotConst:
            return e
    return e


# ---------------------------------------------------------------------------
# AST helpers

def children_blocks(s):
    """statement lists directly inside statement s (not in function bodies)"""
    t = s["type"]
    if t == "AstStatBlock":
        yield s["body"]
    elif t == "AstStatIf":
        yield s["thenbody"]["body"]
        e = s.get("elsebody")
        if e is not None:
            if e["type"] == "AstStatIf":
                yield [e]
            else:
                yield e["body"]
    elif t in ("AstStatWhile", "AstStatRepeat", "AstStatFor", "AstStatForIn"):
        yield s["body"]["body"]


def walk_exprs(n):
    """every dict node below n, not descending into function bodies"""
    st = [n]
    while st:
        x = st.pop()
        if isinstance(x, list):
            st += x
            continue
        if not isinstance(x, dict):
            continue
        yield x
        if x.get("type") == "AstExprFunction":
            continue
        for k, v in x.items():
            if k in ("local", "location"):
                continue
            if isinstance(v, (dict, list)):
                st.append(v)


def locals_read(n):
    return {lkey(x["local"]) for x in walk_exprs(n) if x.get("type") == "AstExprLocal"}


def assign_targets(s):
    t = s["type"]
    if t == "AstStatAssign":
        return s["vars"]
    if t == "AstStatCompoundAssign":
        return [s["var"]]
    return []


def target_locals(s):
    """locals written by statement s (None if it writes something else too)"""
    t = s["type"]
    if t == "AstStatLocal":
        return {lkey(v) for v in s["vars"]}
    out = set()
    for v in assign_targets(s):
        if v["type"] != "AstExprLocal":
            return None
        out.add(lkey(v["local"]))
    return out if out else None


def is_loop(s):
    return s["type"] in ("AstStatWhile", "AstStatRepeat")


# ---------------------------------------------------------------------------
# statics of a function: constant tables, control functions, cache tables

class Statics:
    def __init__(self, fbody):
        assigns = {}      # local -> [rhs]
        index_written = set()

        def scan(n):
            for x in walk_all(n):
                t = x.get("type")
                if t == "AstStatLocal":
                    if not x["values"]:
                        continue      # `local a, b, c`: a declaration, not an assignment
                    for i, v in enumerate(x["vars"]):
                        assigns.setdefault(lkey(v), []).append(x["values"][i] if i < len(x["values"]) else None)
                elif t in ("AstStatAssign", "AstStatCompoundAssign"):
                    tv = x["vars"] if t == "AstStatAssign" else [x["var"]]
                    vals = x["values"] if t == "AstStatAssign" else [None]
                    for i, v in enumerate(tv):
                        if v["type"] == "AstExprLocal":
                            assigns.setdefault(lkey(v["local"]), []).append(vals[i] if i < len(vals) else None)
                        elif v["type"] == "AstExprIndexExpr" and v["expr"]["type"] == "AstExprLocal":
                            index_written.add(lkey(v["expr"]["local"]))
                elif t == "AstStatLocalFunction":
                    assigns.setdefault(lkey(x["name"]), []).append(x["func"])
        scan(fbody)
        self.tables = {}
        self.funcs = {}
        for k, rhs in assigns.items():
            if len(rhs) != 1 or rhs[0] is None:
                continue
            r = rhs[0]
            if r["type"] == "AstExprFunction":
                self.funcs[k] = r
            elif r["type"] == "AstExprTable" and k not in index_written:
                tab = const_table(r)
                if tab is not None:
                    self.tables[k] = tab


def walk_all(n):
    """every dict node below n, including function bodies"""
    st = [n]
    while st:
        x = st.pop()
        if isinstance(x, list):
            st += x
        elif isinstance(x, dict):
            yield x
            for k, v in x.items():
                if k not in ("local", "location") and isinstance(v, (dict, list)):
                    st.append(v)


def const_table(e):
    out = {}
    n = 0
    for it in e["items"]:
        v = fold(it["value"])
        if v["type"] != "AstExprConstantNumber":
            return None
        if it["kind"] == "item":
            n += 1
            out[n] = v["value"]
        elif it["kind"] == "general":
            k = fold(it["key"])
            if k["type"] != "AstExprConstantNumber":
                return None
            out[k["value"]] = v["value"]
        else:
            return None
    return out


# ---------------------------------------------------------------------------
# the control-slice interpreter

class Return(Exception):
    def __init__(self, v):
        self.v = v


class Interp:
    def __init__(self, statics, cv):
        self.st = statics
        self.cv = cv            # control variables (local keys)
        self.used = set()       # statics touched (tables, functions)

    def ev(self, e, env, frame=None):
        t = e["type"]
        if t == "AstExprConstantNumber":
            return e["value"]
        if t == "AstExprConstantNil":
            return NIL
        if t == "AstExprConstantBool":
            return e["value"]
        if t == "AstExprConstantString":
            return ("str", e["value"])
        if t == "AstExprGroup":
            return self.ev(e["expr"], env, frame)
        if t == "AstExprLocal":
            k = lkey(e["local"])
            if frame is not None and k in frame:
                return frame[k]
            if k in env:
                return env[k]
            if k in self.st.tables:
                self.used.add(k)
                return ("tab", k)
            if k in self.st.funcs:
                self.used.add(k)
                return ("fn", k)
            raise NotConst("local " + k[0])
        if t == "AstExprUnary":
            v = self.ev(e["expr"], env, frame)
            if e["op"] == "Minus":
                if not isinstance(v, (int, float)) or isinstance(v, bool):
                    raise NotConst("unm")
                return -v
            if e["op"] == "Not":
                return v is NIL or v is False
            raise NotConst("len")
        if t == "AstExprBinary":
            op = e["op"]
            if op == "Or":
                l = self.ev_cached(e["left"], env, frame)
                if l is not NIL and l is not False:
                    return l
                return self.ev(e["right"], env, frame)
            if op == "And":
                l = self.ev(e["left"], env, frame)
                if l is NIL or l is False:
                    return l
                return self.ev(e["right"], env, frame)
            a = self.ev(e["left"], env, frame)
            b = self.ev(e["right"], env, frame)
            if op == "CompareEq":
                return a == b and type(a) is type(b) or (a is NIL and b is NIL)
            if op == "CompareNe":
                return not (a == b and type(a) is type(b) or (a is NIL and b is NIL))
            if op in ("CompareLt", "CompareLe", "CompareGt", "CompareGe"):
                if not isinstance(a, (int, float)) or not isinstance(b, (int, float)):
                    raise NotConst("cmp")
                return {"CompareLt": a < b, "CompareLe": a <= b, "CompareGt": a > b, "CompareGe": a >= b}[op]
            return arith(op, a, b)
        if t == "AstExprIndexExpr":
            base = self.ev(e["expr"], env, frame)
            idx = self.ev(e["index"], env, frame)
            if isinstance(base, tuple) and base[0] == "tab":
                return self.st.tables[base[1]].get(idx, NIL)
            raise NotConst("index")
        if t == "AstExprCall":
            f = self.ev(e["func"], env, frame)
            if not (isinstance(f, tuple) and f[0] == "fn"):
                raise NotConst("call")
            args = [self.ev(a, env, frame) for a in e["args"]]
            return self.call(self.st.funcs[f[1]], args, env)
        raise NotConst(t)

    def ev_cached(self, e, env, frame):
        """`cache[k] or f(...)`: the cache only ever holds f's result -> miss"""
        if (e["type"] == "AstExprIndexExpr" and e["expr"]["type"] == "AstExprLocal"
                and lkey(e["expr"]["local"]) not in self.st.tables
                and lkey(e["expr"]["local"]) not in env):
            return NIL
        return self.ev(e, env, frame)

    def call(self, fn, args, env):
        frame = {}
        for i, a in enumerate(fn["args"]):
            frame[lkey(a)] = args[i] if i < len(args) else NIL
        try:
            self.exec(fn["body"]["body"], env, frame)
        except Return as r:
            return r.v
        return NIL

    def exec(self, stmts, env, frame):
        for s in stmts:
            t = s["type"]
            if t == "AstStatLocal":
                vals = [self.ev(v, env, frame) for v in s["values"]]
                for i, v in enumerate(s["vars"]):
                    frame[lkey(v)] = vals[i] if i < len(vals) else NIL
            elif t == "AstStatAssign":
                vals = [self.ev(v, env, frame) for v in s["values"]]
                for i, v in enumerate(s["vars"]):
                    val = vals[i] if i < len(vals) else NIL
                    if v["type"] == "AstExprLocal":
                        k = lkey(v["local"])
                        if k in frame:
                            frame[k] = val
                        elif k in env:
                            env[k] = val
                        else:
                            raise NotConst("write " + k[0])
                    # index writes: the result cache, ignored
            elif t == "AstStatIf":
                c = self.ev(s["condition"], env, frame)
                if c is not NIL and c is not False:
                    self.exec(s["thenbody"]["body"], env, frame)
                elif s.get("elsebody") is not None:
                    e = s["elsebody"]
                    self.exec([e] if e["type"] == "AstStatIf" else e["body"], env, frame)
            elif t == "AstStatReturn":
                raise Return(self.ev(s["list"][0], env, frame) if s["list"] else NIL)
            else:
                raise NotConst("stmt " + t)

    def assign(self, s, env):
        """run control statement s on env (a copy is made by the caller)"""
        t = s["type"]
        if t == "AstStatCompoundAssign":
            k = lkey(s["var"]["local"])
            env[k] = arith(s["op"], env.get(k, NIL), self.ev(s["value"], env))
            return
        vals = [self.ev(v, env) for v in s["values"]]
        tv = s["vars"]
        for i, v in enumerate(tv):
            env[lkey(v if t == "AstStatLocal" else v["local"])] = vals[i] if i < len(vals) else NIL


# ---------------------------------------------------------------------------
# finding flattened loops

def state_var(loop):
    """the local a loop dispatches on (most `== const` tests), or None"""
    counts = {}
    for x in walk_exprs(loop["body"]):
        if x.get("type") == "AstExprBinary" and x["op"] in ("CompareEq", "CompareNe", "CompareLt", "CompareGe",
                                                           "CompareLe", "CompareGt"):
            l, r = fold(x["left"]), fold(x["right"])
            if l["type"] == "AstExprLocal" and r["type"] == "AstExprConstantNumber":
                k = lkey(l["local"])
                counts[k] = counts.get(k, 0) + 1
    if not counts:
        return None
    k, n = max(counts.items(), key=lambda kv: kv[1])
    return k if n >= 3 else None


def loop_stmts(loop):
    """statements at the loop's own level (for CV analysis)"""
    out = []
    st = [loop["body"]["body"]]
    while st:
        lst = st.pop()
        for s in lst:
            out.append(s)
            if s["type"] in ("AstStatIf", "AstStatBlock"):
                st += list(children_blocks(s))
    return out


def control_vars(loop, S, pre):
    stmts = [s for s in loop_stmts(loop) + pre if not (s["type"] == "AstStatLocal" and not s["values"])]
    assigned = set()
    nonnum = set()      # locals holding tables/functions: statics or caches, never control values
    for s in stmts:
        tl = target_locals(s)
        if tl:
            assigned |= tl
            vals = s.get("values") or []
            tv = s.get("vars") or []
            for i, v in enumerate(tv):
                if i < len(vals) and vals[i]["type"] in ("AstExprTable", "AstExprFunction"):
                    nonnum.add(lkey(v if s["type"] == "AstStatLocal" else v["local"]))
    assigned -= nonnum
    cv = {S}
    changed = True
    while changed:
        changed = False
        for s in stmts:
            tl = target_locals(s)
            if not tl or not (tl & cv):
                continue
            new = (tl | (locals_read(s) & assigned)) - cv
            if new:
                cv |= new
                changed = True
    return cv


# ---------------------------------------------------------------------------
# the walk

class Graph:
    """a deflattened loop: nodes {id: Tree}, entry id"""

    def __init__(self):
        self.nodes = {}
        self.entry = None
        self.keyid = {}
        self.warnings = []


class Tree:
    """statements then a tail: ('goto', id) | ('exit',) | ('ret',) | ('if', cond, Tree, Tree)"""

    def __init__(self, stmts, tail):
        self.stmts, self.tail = stmts, tail


class Deflattener:
    def __init__(self):
        self.graphs = 0
        self.warnings = []

    # block-level driver -----------------------------------------------------
    def function(self, fn, statics_scope=None):
        fn["body"]["body"] = self.block(fn["body"]["body"], Statics(fn["body"]))
        return fn

    def block(self, stmts, statics):
        out = []
        i = 0
        while i < len(stmts):
            s = stmts[i]
            if is_loop(s):
                S = state_var(s)
                if S is not None:
                    g, drop = self.loop(s, S, stmts[:i], statics)
                    if g is not None:
                        out = [x for x in out if id(x) not in drop]
                        out.append({"type": "Graph", "graph": g})
                        i += 1
                        continue
            out.append(self.real(s, statics))
            i += 1
        return out

    def real(self, s, statics):
        """a statement kept as is: deflatten functions and blocks inside it"""
        for x in walk_exprs(s):
            if x.get("type") == "AstExprFunction":
                self.function(x)
        t = s["type"]
        if t == "AstStatLocalFunction":
            self.function(s["func"])
        if t == "AstStatBlock":
            s["body"] = self.block(s["body"], statics)
        elif t == "AstStatIf":
            s["thenbody"]["body"] = self.block(s["thenbody"]["body"], statics)
            e = s.get("elsebody")
            if e is not None:
                if e["type"] == "AstStatIf":
                    s["elsebody"] = self.real(e, statics)
                else:
                    e["body"] = self.block(e["body"], statics)
        elif t in ("AstStatWhile", "AstStatRepeat", "AstStatFor", "AstStatForIn"):
            s["body"]["body"] = self.block(s["body"]["body"], statics)
        return s

    # one flattened loop ---------------------------------------------------------
    def loop(self, loop, S, before, statics):
        # nested functions are deflattened while this loop is walked: keep
        # the walk's state per loop
        saved = [getattr(self, a, None) for a in ("cv", "it", "loopnode", "statics", "node_id")]
        try:
            return self._loop(loop, S, before, statics)
        finally:
            self.cv, self.it, self.loopnode, self.statics, self.node_id = saved

    def _loop(self, loop, S, before, statics):
        cv = control_vars(loop, S, before)
        it = Interp(statics, cv)
        env = {}
        drop = set()
        # the control statements before the loop set up the entry state
        for s in before:
            tl = target_locals(s)
            if tl and tl <= cv:
                try:
                    it.assign(s, env)
                    drop.add(id(s))
                except NotConst:
                    pass
        if S not in env:
            return None, set()
        g = Graph()
        self.cv = cv
        self.it = it
        self.loopnode = loop
        self.statics = statics
        todo = []

        def node_id(env):
            k = tuple(sorted((a[0], a[1], env.get(a)) for a in cv))
            nid = g.keyid.get(k)
            if nid is None:
                nid = len(g.keyid) + 1
                g.keyid[k] = nid
                todo.append((nid, dict(env)))
            return nid
        self.node_id = node_id
        head = self.head(env)
        if head[0] == "exit":
            return None, set()
        g.entry = head[1]
        while todo:
            nid, env = todo.pop()
            if len(g.keyid) > MAXNODES:
                self.warnings.append("state explosion in loop over " + S[0])
                return None, set()
            g.nodes[nid] = self.run(list(loop["body"]["body"]), env)
        # support definitions (cache table, transition function, constant
        # tables) are dropped if nothing else reads them
        self.graphs += 1
        return g, drop

    def head(self, env):
        """loop condition check with this env -> ('goto', id) | ('exit',)"""
        loop = self.loopnode
        if loop["type"] == "AstStatWhile":
            c = self.it.ev(loop["condition"], env)
            if c is NIL or c is False:
                return ("exit",)
        return ("goto", self.node_id(env))

    def tail_next(self, env):
        loop = self.loopnode
        if loop["type"] == "AstStatRepeat":
            c = self.it.ev(loop["condition"], env)
            if c is not NIL and c is not False:
                return ("exit",)
        return self.head(env)

    def is_control(self, s):
        tl = target_locals(s)
        return bool(tl) and tl <= self.cv

    def has_control(self, stmts):
        for s in stmts:
            if self.is_control(s) or s["type"] in ("AstStatContinue", "AstStatBreak"):
                return True
            if s["type"] in ("AstStatIf", "AstStatBlock"):
                if any(self.has_control(b) for b in children_blocks(s)):
                    return True
        return False

    def run(self, stmts, env):
        out = []
        i = 0
        while i < len(stmts):
            s = stmts[i]
            t = s["type"]
            if self.is_control(s):
                env = dict(env)
                try:
                    self.it.assign(s, env)
                except NotConst as ex:
                    self.warnings.append("control statement not evaluable (%s)" % ex)
                    out.append(s)
                i += 1
                continue
            if t == "AstStatIf":
                try:
                    c = self.it.ev(s["condition"], env)
                    known = True
                except NotConst:
                    known = False
                rest = stmts[i + 1:]
                if known:
                    if c is not NIL and c is not False:
                        branch = s["thenbody"]["body"]
                    else:
                        e = s.get("elsebody")
                        branch = [] if e is None else ([e] if e["type"] == "AstStatIf" else e["body"])
                    stmts = list(branch) + rest
                    i = 0
                    continue
                branches = [s["thenbody"]["body"]]
                e = s.get("elsebody")
                branches.append([] if e is None else ([e] if e["type"] == "AstStatIf" else e["body"]))
                if not self.has_control(branches[0]) and not self.has_control(branches[1]):
                    out.append(self.real(s, self.statics))
                    i += 1
                    continue
                a = self.run(list(branches[0]) + rest, dict(env))
                b = self.run(list(branches[1]) + rest, dict(env))
                return Tree(out, ("if", s["condition"], a, b))
            if t == "AstStatBlock":
                stmts = list(s["body"]) + stmts[i + 1:]
                i = 0
                continue
            if t == "AstStatContinue":
                return Tree(out, self.tail_next(env))
            if t == "AstStatBreak":
                return Tree(out, ("exit",))
            if t == "AstStatReturn":
                out.append(self.real(s, self.statics))
                return Tree(out, ("ret",))
            out.append(self.real(s, self.statics))
            i += 1
        return Tree(out, self.tail_next(env))


# ---------------------------------------------------------------------------
# printing (pseudo-Luau with goto; single-predecessor blocks are inlined)

def render(root):
    import luauast

    class P(luauast.Printer):
        def stat(self, s, depth):
            if s["type"] == "Graph":
                self.graph(s["graph"], depth)
            else:
                super().stat(s, depth)

        def graph(self, g, depth):
            preds = {}

            def count(tree):
                tl = tree.tail
                if tl[0] == "goto":
                    preds[tl[1]] = preds.get(tl[1], 0) + 1
                elif tl[0] == "if":
                    count(tl[2])
                    count(tl[3])
            preds[g.entry] = 1
            for t in g.nodes.values():
                count(t)
            shown = set()
            order = []
            seen = set()
            st = [g.entry]
            # label order: DFS from the entry
            while st:
                n = st.pop()
                if n in seen:
                    continue
                seen.add(n)
                order.append(n)
                succ = []

                def sc(tree):
                    tl = tree.tail
                    if tl[0] == "goto":
                        succ.append(tl[1])
                    elif tl[0] == "if":
                        sc(tl[2])
                        sc(tl[3])
                sc(g.nodes[n])
                st += reversed(succ)
            self.emit(depth, "-- deflattened (%d blocks)" % len(g.nodes))
            for n in order:
                if n in shown:
                    continue
                if n != g.entry and preds.get(n, 0) == 1:
                    continue      # printed inline where it is reached
                self.emit(depth, "::L%d::" % n)
                self.tree(g, g.nodes[n], depth, preds, shown, {n})
            self.emit(depth, "::exit::")

        def tree(self, g, tree, depth, preds, shown, chain):
            for s in tree.stmts:
                self.stat(s, depth)
            tl = tree.tail
            if tl[0] == "goto":
                n = tl[1]
                if preds.get(n, 0) == 1 and n != g.entry and n not in chain:
                    shown.add(n)
                    self.tree(g, g.nodes[n], depth, preds, shown, chain | {n})
                else:
                    self.emit(depth, "goto L%d" % n)
            elif tl[0] == "exit":
                self.emit(depth, "goto exit")
            elif tl[0] == "if":
                self.emit(depth, "if " + self.expr(tl[1], depth) + " then")
                self.tree(g, tl[2], depth + 1, preds, shown, chain)
                self.emit(depth, "else")
                self.tree(g, tl[3], depth + 1, preds, shown, chain)
                self.emit(depth, "end")
    p = P()
    p.block(root, 0)
    return "\n".join(p.lines)


def deflatten_source(src):
    import luauast
    root = fold(luauast.parse(src))
    d = Deflattener()
    # the whole chunk acts as one function
    root["body"] = d.block(root["body"], Statics(root))
    return root, d


def main():
    import os
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
    import backend
    src = open(sys.argv[1], encoding="latin-1").read()

    def go():
        root, d = deflatten_source(src)
        text = render(root)
        return text, d
    text, d = backend.run_big_stack(go)
    sys.stdout.buffer.write((text + "\n").encode("latin-1"))
    print("[*] %d flattened loops, %d warnings" % (d.graphs, len(d.warnings)), file=sys.stderr)
    for w in sorted(set(d.warnings))[:20]:
        print("    " + w, file=sys.stderr)


if __name__ == "__main__":
    main()
