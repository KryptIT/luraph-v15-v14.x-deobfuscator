"""
for loops of the ironbrew1 walk, rewritten into the shape the shared loop
recognizer knows (loops.try_numeric / try_generic: the VM's hidden loop
state as Pseudo slots, set by a prep in the one predecessor outside the
loop). The VM keeps that state in registers; the handlers are matched by
the IR they produce, not by opcode (opcodes are shuffled per build):

  numeric   prep  R[a] = R[a] - R[a+2]            (then a jump to the loop op)
            loop  x = R[a] + R[a+2]; R[a] = x
                  if x <= R[a+1] then R[v] = x -> body  else -> exit
  generic   loop  t = R[a](R[a+1], R[a+2])
                  if t[1] ~= nil then R[a+2] = t[1]; R[a+3] = t[1]; R[a+4] = t[2] ... -> body
                  else -> exit

A loop is rewritten only when all of its parts match (one entry
predecessor, prep found): a half rewrite would change what the code does.
"""
from ir import Assign, CallStmt, Node, Next, GenIter
from luasym import Reg, Bin, Const, TempVal, Pseudo, Multi


def _leaves(node, out, path=()):
    if node is None:
        return
    if node.cond is not None:
        _leaves(node.then, out, path + (node,))
        _leaves(node.els, out, path + (node,))
    else:
        out.append((node, path))


def _is_reg(e, n=None):
    return isinstance(e, Reg) and (n is None or e.n == n)


def _succ_keys(node):
    lv = []
    _leaves(node, lv)
    return [x.outcome.state.key() for x, _ in lv if isinstance(x.outcome, Next)]


class Graph:
    def __init__(self, order):
        self.nodes = dict(order)
        self.preds = {}         # key -> [(pred key, leaf node)]
        for k, n in order:
            lv = []
            _leaves(n, lv)
            for leaf, _ in lv:
                if isinstance(leaf.outcome, Next):
                    self.preds.setdefault(leaf.outcome.state.key(), []).append((k, leaf))
        self.entry = order[0][0] if order else None
        self._idom = None

    def idom(self):
        """immediate dominators (Cooper, Harvey, Kennedy) over the walk graph"""
        if self._idom is not None:
            return self._idom
        # reverse postorder from the entry
        post, seen = [], set()
        st = [(self.entry, iter(_succ_keys(self.nodes[self.entry])))] if self.entry in self.nodes else []
        if st:
            seen.add(self.entry)
        while st:
            k, it = st[-1]
            for s in it:
                if s not in seen and s in self.nodes:
                    seen.add(s)
                    st.append((s, iter(_succ_keys(self.nodes[s]))))
                    break
            else:
                post.append(k)
                st.pop()
        rpo = list(reversed(post))
        num = {k: i for i, k in enumerate(rpo)}
        idom = {self.entry: self.entry} if rpo else {}

        def meet(a, b):
            while a != b:
                while num[a] > num[b]:
                    a = idom[a]
                while num[b] > num[a]:
                    b = idom[b]
            return a
        changed = True
        while changed:
            changed = False
            for k in rpo[1:]:
                ps = [p for p, _ in self.preds.get(k, []) if p in idom]
                if not ps:
                    continue
                new = ps[0]
                for p in ps[1:]:
                    new = meet(p, new)
                if idom.get(k) != new:
                    idom[k] = new
                    changed = True
        self._idom = idom
        return idom

    def dominates(self, a, b):
        idom = self.idom()
        if b not in idom:
            return False
        while True:
            if b == a:
                return True
            nb = idom[b]
            if nb == b:
                return False
            b = nb

    def entry_preds(self, hk):
        """(entry preds, back-edge preds) of loop header hk: a back edge
        comes from a node the header dominates"""
        ent, back = [], []
        for k, lf in self.preds.get(hk, []):
            (back if self.dominates(hk, k) else ent).append((k, lf))
        return ent, back


def _numeric_header(n):
    """(a, v, prefix length) of a FORLOOP node, or None"""
    c = n.cond
    if not (isinstance(c, Bin) and c.op == "CompareLe") or n.then is None or n.els is None:
        return None
    st = n.stmts
    if len(st) >= 2 and isinstance(st[-1], Assign) and _is_reg(st[-1].target) and _is_reg(st[-1].value) \
            and isinstance(st[-2], Assign) and _is_reg(st[-2].target, st[-1].value.n):
        a, x, add, cut = st[-1].target.n, st[-1].value, st[-2].value, 2
    elif len(st) >= 1 and isinstance(st[-1], Assign) and _is_reg(st[-1].target):
        a = st[-1].target.n
        x, add, cut = Reg(a), st[-1].value, 1
    else:
        return None
    if not (isinstance(add, Bin) and add.op == "Add" and _is_reg(add.a, a) and _is_reg(add.b, a + 2)):
        return None
    if not (_is_reg(c.a, x.n) and _is_reg(c.b, a + 1)):
        return None
    t, e = n.then, n.els
    if t.cond is not None or e.cond is not None or e.stmts or not isinstance(t.outcome, Next) \
            or not isinstance(e.outcome, Next):
        return None
    if len(t.stmts) != 1 or not isinstance(t.stmts[0], Assign) or not _is_reg(t.stmts[0].target) \
            or not _is_reg(t.stmts[0].value, x.n):
        return None
    return a, t.stmts[0].target.n, cut


def _find_prep_sub(g, pk, leaf, a, hk):
    """the FORPREP statement `R[a] = R[a] - R[a+2]` on the way into the loop:
    in the entry leaf, or earlier through nodes that only jump. Returns
    (statement list, index) or None."""
    seen = set()
    while True:
        for i in range(len(leaf.stmts) - 1, -1, -1):
            s = leaf.stmts[i]
            if isinstance(s, Assign) and _is_reg(s.target, a):
                v = s.value
                if isinstance(v, Bin) and v.op == "Sub" and _is_reg(v.a, a) and _is_reg(v.b, a + 2):
                    return leaf.stmts, i
                return None
            if isinstance(s, Assign) and _is_reg(s.target) and s.target.n in (a + 1, a + 2):
                return None
            if not isinstance(s, Assign):
                return None
        # nothing here: a node that only jumps, reached from one place
        n = g.nodes.get(pk)
        if n is None or n is not leaf or n.stmts or pk in seen:
            return None
        seen.add(pk)
        ps = g.preds.get(pk, [])
        if len(ps) != 1:
            return None
        pk, leaf = ps[0]


def rewrite_numeric(g, hk, n):
    m = _numeric_header(n)
    if m is None:
        return False
    a, v, cut = m
    ent, back = g.entry_preds(hk)
    if len(ent) != 1 or not back:
        return False
    pk, leaf = ent[0]
    found = _find_prep_sub(g, pk, leaf, a, hk)
    if found is None:
        return False
    lst, i = found
    pa, pl, pz = Pseudo("fa", a), Pseudo("fl", a), Pseudo("fz", a)
    del lst[i]
    leaf.stmts += [Assign(pz, Reg(a + 2)), Assign(pl, Reg(a + 1)), Assign(pa, Bin("Sub", Reg(a), pz))]
    body, exit_ = n.then.outcome, n.els.outcome
    n.stmts = n.stmts[:-cut] + [Assign(pa, Bin("Add", pa, pz))]
    n.cond = Bin("CompareLe", pz, Const(0))

    def side(op):
        return Node([], cond=Bin(op, pa, pl), then=Node([Assign(Reg(v), pa)], outcome=body),
                    els=Node([], outcome=exit_))
    n.then, n.els = side("CompareGe"), side("CompareLe")
    return True


def _generic_header(n):
    """(a, call, [(var register, result index)]) of a TFORLOOP node, or None"""
    if not n.stmts or not isinstance(n.stmts[-1], CallStmt) or n.then is None or n.els is None:
        return None
    call = n.stmts[-1]
    if not _is_reg(call.fn) or call.args.tail is not None or len(call.args.items) != 2:
        return None
    a = call.fn.n
    if not (_is_reg(call.args.items[0], a + 1) and _is_reg(call.args.items[1], a + 2)):
        return None
    c = n.cond
    if not (isinstance(c, Bin) and c.op == "CompareNe" and isinstance(c.a, TempVal) and c.a.t == call.t
            and c.a.i == 1 and isinstance(c.b, Const) and c.b.v is None):
        return None
    t, e = n.then, n.els
    if t.cond is not None or e.cond is not None or e.stmts or not isinstance(t.outcome, Next) \
            or not isinstance(e.outcome, Next):
        return None
    vars_ = []
    ctl = False
    for s in t.stmts:
        if not (isinstance(s, Assign) and _is_reg(s.target) and isinstance(s.value, TempVal)
                and s.value.t == call.t):
            return None
        if s.target.n == a + 2 and s.value.i == 1 and not ctl:
            ctl = True
            continue
        vars_.append((s.target.n, s.value.i))
    vars_.sort()
    if not vars_ or [r for r, _ in vars_] != list(range(a + 3, a + 3 + len(vars_))) or \
            [i for _, i in vars_] != list(range(1, len(vars_) + 1)):
        return None
    return a, call, vars_


def rewrite_generic(g, hk, n):
    m = _generic_header(n)
    if m is None:
        return False
    a, call, vars_ = m
    ent, back = g.entry_preds(hk)
    if len(ent) != 1 or not back:
        return False
    pk, leaf = ent[0]
    it = Pseudo("ga", a)
    leaf.stmts.append(Assign(it, GenIter(Multi([None, Reg(a), Reg(a + 1), Reg(a + 2)]))))
    t2 = call.t + "g"
    n.stmts[-1] = CallStmt(t2, it, Multi([]))
    n.cond = TempVal(t2, 1)
    n.then.stmts = [Assign(Reg(r), TempVal(t2, i + 1)) for r, i in vars_]
    return True


class _Key:
    """a Next target made here (a node split off another one)"""

    def __init__(self, key):
        self._k = key

    def key(self, link=None):
        return self._k


def rewrite_counting(g, hk, n, order):
    """a fused numeric loop (a counting `while` inside one handler, devirt's
    LV registers): `while x <= y do <body>; x = x + z end`"""
    c = n.cond
    if n.stmts or not (isinstance(c, Bin) and c.op == "CompareLe" and _is_reg(c.a) and _is_reg(c.b)):
        return False
    t, e = n.then, n.els
    if t is None or e is None or t.cond is not None or not isinstance(t.outcome, Next) or \
            t.outcome.state.key() != hk or not t.stmts:
        return False
    x, y = c.a.n, c.b.n
    inc = t.stmts[-1]
    if not (isinstance(inc, Assign) and _is_reg(inc.target, x) and isinstance(inc.value, Bin)
            and inc.value.op == "Add" and _is_reg(inc.value.a, x) and _is_reg(inc.value.b)):
        return False
    z = inc.value.b.n
    if z in (x, y):
        return False
    ent, back = g.entry_preds(hk)
    if len(ent) != 1 or [k for k, _ in back] != [hk]:
        return False
    _, leaf = ent[0]
    d = x
    pa, pl, pz = Pseudo("fa", d), Pseudo("fl", d), Pseudo("fz", d)
    leaf.stmts += [Assign(pz, Reg(z)), Assign(pl, Reg(y)), Assign(pa, Bin("Sub", Reg(x), pz))]
    bk, xk = ("S", hk[1], "body", hk), ("S", hk[1], "exit", hk)
    order.append((bk, Node(t.stmts[:-1], outcome=t.outcome)))
    order.append((xk, e))
    n.stmts = [Assign(pa, Bin("Add", pa, pz))]
    n.cond = Bin("CompareLe", pz, Const(0))

    def side(op):
        return Node([], cond=Bin(op, pa, pl), then=Node([Assign(Reg(x), pa)], outcome=Next(_Key(bk))),
                    els=Node([], outcome=Next(_Key(xk))))
    n.then, n.els = side("CompareGe"), side("CompareLe")
    return True


LV_BASE, HLOC_BASE = 600000, 700000      # (devirt's register ranges: fused-loop and handler locals)


def _call_iterators(order, g):
    """a generic for prep whose f, s, ctl are results 1..3 of one call
    (directly, or through registers set from it earlier: in the same block
    or the instructions before it on a straight path): the prep takes the
    call's results (`for k in s:gmatch(p)`). The copies into the loop's
    iterator registers go (compiled code never reads those registers but
    through the loop), and so do copies of them into a fused loop's
    handler-local registers."""
    from luasym import TempTail

    def before(key, leaf, i):
        """(statement list, statement) before position i of leaf, newest
        first, back along single predecessors that are plain blocks"""
        stmts, k, hops = leaf.stmts, key, 0
        upto = i
        while True:
            for j in range(upto - 1, -1, -1):
                yield stmts, stmts[j]
            ps = g.preds.get(k, [])
            if len(ps) != 1 or hops > 8:
                return
            k, pl = ps[0]
            pn = g.nodes.get(k)
            if pn is None or pn is not pl:
                return
            stmts, upto, hops = pl.stmts, len(pl.stmts), hops + 1

    for key, n in order:
        lv = []
        _leaves(n, lv)
        for leaf, _ in lv:
            st = leaf.stmts
            for i, s in enumerate(list(st)):
                if not (isinstance(s, Assign) and isinstance(s.target, Pseudo) and isinstance(s.value, GenIter)):
                    continue
                args = s.value.args
                if args is None or args.tail is not None or len(args.items) != 4:
                    continue
                src, drop = [], []
                regs = [x.n for x in args.items[1:] if isinstance(x, Reg)]
                for x in args.items[1:]:
                    if isinstance(x, Reg):
                        for lst, y in before(key, leaf, st.index(s)):
                            if isinstance(y, Assign) and _is_reg(y.target, x.n):
                                drop.append((lst, y))
                                x = y.value
                                break
                            if isinstance(y, Assign) and isinstance(y.target, Reg) \
                                    and LV_BASE <= y.target.n < HLOC_BASE and _is_reg(y.value) \
                                    and y.value.n in regs:
                                drop.append((lst, y))       # a fused loop's copy of an iterator register
                    src.append(x)
                if all(isinstance(x, TempVal) for x in src) and len({x.t for x in src}) == 1 \
                        and [x.i for x in src] == [1, 2, 3]:
                    s.value = GenIter(Multi([None], TempTail(src[0].t)))
                    for lst, y in drop:
                        for j, z in enumerate(lst):
                            if z is y:
                                del lst[j]
                                break


def order_branches(order):
    """A branch between two instructions: `then` goes to the lower pc. The
    compiler lays out an if's blocks in source order (then-part first), the
    VM's jump instructions test either way (`if not x then goto L`); lower
    pc first gives the author's shape (`if bad then kick() return end`,
    `if ok then ... return r end return d`). Exact: the condition is negated."""
    from structure import negate
    for _, n in order:
        st = [n]
        while st:
            x = st.pop()
            if x is None or x.cond is None:
                continue
            t, e = x.then, x.els
            if t is not None and e is not None and t.cond is None and e.cond is None \
                    and not t.stmts and not e.stmts \
                    and isinstance(t.outcome, Next) and isinstance(e.outcome, Next):
                tp = getattr(t.outcome.state, "pc", None)
                ep = getattr(e.outcome.state, "pc", None)
                if isinstance(tp, int) and isinstance(ep, int) and tp > ep \
                        and not any(isinstance(y, Pseudo) for y in _walk_expr(x.cond)):
                    x.cond = negate(x.cond)
                    x.then, x.els = e, t
                continue
            st += [t, e]


def _walk_expr(e):
    st = [e]
    while st:
        y = st.pop()
        yield y
        if hasattr(y, "__dict__"):
            st += [v for v in vars(y).values() if hasattr(v, "__dict__")]


def rewrite(order):
    """rewrite the for loops of one walk in place; returns (numeric, generic) counts"""
    g = Graph(order)
    nn = ng = 0
    for hk, n in list(order):
        if rewrite_numeric(g, hk, n) or rewrite_counting(g, hk, n, order):
            nn += 1
        elif rewrite_generic(g, hk, n):
            ng += 1
    _call_iterators(order, g)
    order_branches(order)
    return nn, ng
