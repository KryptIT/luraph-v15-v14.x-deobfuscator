"""
Expression cleanup and Luau rendering for the devirtualizer.

  simplify_blocks(blocks)  per basic block: calls materialized into temps are
                           folded back into their single use; registers that
                           are defined and used once (and dead afterwards) are
                           inlined when nothing with side effects sits between
                           definition and use. Liveness is computed on the CFG.
  Renderer                 structured AST -> Luau text.
"""
import math
import re
import unicodedata

import luasym as S
from luasym import (Const, Reg, Pseudo, Global, Upval, Index, Bin, Un, IfExp, TempVal, Vararg, ClosureExpr,  # noqa: F401
                    Multi, TempTail, VarargTail, SymList, TailCount, NewTable, Expr)
import structure as ST

LUA_KEYWORDS = {"and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in", "local",
                "nil", "not", "or", "repeat", "return", "then", "true", "until", "while", "continue"}

BINOPS = {"Add": ("+", 6), "Sub": ("-", 6), "Mul": ("*", 7), "Div": ("/", 7), "FloorDiv": ("//", 7),
          "Mod": ("%", 7), "Pow": ("^", 10), "Concat": ("..", 5),
          "CompareEq": ("==", 3), "CompareNe": ("~=", 3), "CompareLt": ("<", 3), "CompareLe": ("<=", 3),
          "CompareGt": (">", 3), "CompareGe": (">=", 3), "And": ("and", 2), "Or": ("or", 1)}
RIGHT_ASSOC = {"Concat", "Pow"}
COMPOUND = {"Add", "Sub", "Mul", "Div", "FloorDiv", "Mod", "Pow", "Concat"}
FLIPPED = {"CompareLt": "CompareGt", "CompareLe": "CompareGe"}


# --------------------------------------------------------------------------
# generic expression helpers

_LEAF_TYPES = set()     # types children() found no sub-expressions in (leaves: Reg, Const, ...)


def children(e):
    """Sub-expressions of an IR expression (for walking)."""
    if type(e) in _LEAF_TYPES:
        return []
    if isinstance(e, (Index,)):
        return [e.obj, e.key]
    if isinstance(e, Bin):
        return [e.a, e.b]
    if isinstance(e, Un):
        return [e.a]
    if isinstance(e, IfExp):
        return [e.c, e.a, e.b]
    if isinstance(e, CallE):
        return [e.fn] + list(e.args.items) + ([TailRef(e.args.tail)] if e.args.tail is not None else [])
    if isinstance(e, SymList):
        return list(e.items) + ([TailRef(e.tail)] if e.tail is not None else [])
    if isinstance(e, TailRef):
        return [e.tail.call] if isinstance(e.tail, InlineTail) else []
    if isinstance(e, NewTableE):
        out = []
        for k, v in e.items:
            if k is not None:
                out.append(k)
            out.append(v)
        if e.tail is not None:
            out.append(TailRef(e.tail))
        return out
    if isinstance(e, GenIterE):
        return list(e.args)
    if isinstance(e, ClosureExpr):
        # captured registers are uses (by reference or by value)
        out = []
        for u in e.upvals:
            if type(u).__name__ == "MaybeBox":
                out.append(Reg(u.reg))
            elif isinstance(u, S.LTable) and any(type(v).__name__ == "RegFile" for v in u.h.values()):
                out += [Reg(v) for v in u.h.values() if isinstance(v, int)][:1]
            elif isinstance(u, Reg):
                out.append(u)
        return out
    _LEAF_TYPES.add(type(e))
    return []


def map_expr(e, fn):
    """Rebuild an expression bottom-up; fn(node) may return a replacement."""
    r = fn(e)
    if r is not None:
        return r
    if isinstance(e, Index):
        return Index(map_expr(e.obj, fn), map_expr(e.key, fn))
    if isinstance(e, Bin):
        return Bin(e.op, map_expr(e.a, fn), map_expr(e.b, fn))
    if isinstance(e, Un):
        return Un(e.op, map_expr(e.a, fn))
    if isinstance(e, IfExp):
        return IfExp(map_expr(e.c, fn), map_expr(e.a, fn), map_expr(e.b, fn))
    if isinstance(e, CallE):
        return CallE(map_expr(e.fn, fn), map_multi(e.args, fn), e.method)
    if isinstance(e, NewTableE):
        return NewTableE([(map_expr(k, fn) if k is not None else None, map_expr(v, fn)) for k, v in e.items],
                         map_tail(e.tail, fn))
    if isinstance(e, GenIterE):
        return GenIterE([map_expr(a, fn) for a in e.args])
    if isinstance(e, TailRef) and isinstance(e.tail, InlineTail):
        return TailRef(InlineTail(map_expr(e.tail.call, fn)))
    return e


def map_multi(m, fn):
    return Multi([map_expr(x, fn) for x in m.items], map_tail(m.tail, fn))


def map_tail(t, fn):
    if t is None:
        return None
    r = fn(TailRef(t))
    if isinstance(r, TailRef):
        return r.tail
    if isinstance(t, InlineTail):
        return InlineTail(map_expr(t.call, fn))
    return t


class TailRef(Expr):
    """Wrapper so tails can be visited/replaced like expressions."""

    def __init__(self, tail):
        self.tail = tail


class InlineTail:
    """A multret tail that is a call expression inlined in place (f(a, g()))."""

    def __init__(self, call):
        self.call = call


class CallE(Expr):
    pure = False

    def __init__(self, fn, args, method=None):
        self.fn, self.args, self.method = fn, args, method


class NewTableE(Expr):
    def __init__(self, items, tail=None):
        self.items, self.tail = items, tail


class GenIterE(Expr):
    def __init__(self, args):
        self.args = args


class FuncE(Expr):
    """A lifted child function: rendered text (list of lines, already indented relative)."""

    def __init__(self, lines):
        self.lines = lines


class LocalName(Expr):
    def __init__(self, name):
        self.name = name


def walk(e):
    st = [e]
    while st:
        x = st.pop()
        if x is None:
            continue
        yield x
        st += children(x)


def regs_read(e):
    return [x.n for x in walk(e) if isinstance(x, Reg)]


def temps_read(e):
    out = []
    for x in walk(e):
        if isinstance(x, TempVal):
            out.append(x.t)
        elif isinstance(x, TailRef) and isinstance(x.tail, TempTail):
            out.append(x.tail.t)
    return out


def has_side_effects(e):
    return any(isinstance(x, CallE) for x in walk(e))


def expr_key(e):
    """Structural identity (for comparing expressions)."""
    if e is None:
        return "nil"
    if isinstance(e, Const):
        return "K" + repr(e.v)
    if isinstance(e, Reg):
        return "R%d" % e.n
    if isinstance(e, Upval):
        return "U%d" % e.idx
    if isinstance(e, Global):
        return "G" + e.name
    if isinstance(e, LocalName):
        return "L" + e.name
    if isinstance(e, Index):
        return "I(%s,%s)" % (expr_key(e.obj), expr_key(e.key))
    return "X%d" % id(e)


# --------------------------------------------------------------------------
# statements used after simplification (besides devirt.Assign etc.)

class AssignS:
    """targets = values (targets: list of lvalue exprs; values: Multi)."""

    def __init__(self, targets, values):
        self.targets, self.values = targets, values


class CallS:
    def __init__(self, call):
        self.call = call


class SetListS:
    def __init__(self, tbl, start, values):
        self.tbl, self.start, self.values = tbl, start, values


class LocalS:
    def __init__(self, names, values):
        self.names, self.values = names, values


class CloseS:
    """End of a captured local's scope (Luraph's close-upvalue op)."""

    def __init__(self, reg):
        self.reg = reg


class CommentS:
    def __init__(self, text):
        self.text = text


def convert_stmts(stmts, D):
    """devirt IR statements -> AssignS/CallS with CallE expressions."""
    out = []
    for st in stmts:
        if isinstance(st, D.CallStmt):
            out.append(TempDef(st.t, CallE(conv(st.fn, D), conv_multi(st.args, D))))
        elif isinstance(st, D.SetList):
            out.append(SetListS(conv(st.tbl, D), st.start, conv_multi(st.values, D)))
        elif isinstance(st, D.Close):
            out.append(CloseS(st.reg))
        elif isinstance(st, D.ForPrep):
            st.exprs[:] = [conv(x, D) for x in st.exprs]
            out.append(ForPrepS(st.exprs))
        elif isinstance(st, D.Assign):
            v = st.value
            if isinstance(v, SymList) and not isinstance(st.target, Reg):
                # `t[k] = {f()}` (LPH_JIT code): a real table constructor
                v = NewTableE([(None, conv(x, D)) for x in v.items], conv_tail(v.tail))
                out.append(AssignS([conv(st.target, D)], Multi([v])))
                continue
            if isinstance(v, SymList):
                # a packed multret list kept in a register: the consumer
                # already refers to its contents; keep a readable fallback
                v = CallE(Global("table.pack"), Multi([conv(x, D) for x in v.items], conv_tail(v.tail)))
                a = AssignS([conv(st.target, D)], Multi([v]))
                a.pack = True
                out.append(a)
                continue
            out.append(AssignS([conv(st.target, D)], Multi([conv(v, D)])))
        else:
            out.append(CommentS("unknown statement %r" % (st,)))
    return out


class ForPrepS:
    """Evaluates a for header's expressions (a loops.LoopExprs list shared with
    the header, which renders them). Renders nothing itself."""

    def __init__(self, exprs):
        self.exprs = exprs


class TempDef:
    """t := call (all results)."""

    def __init__(self, t, call):
        self.t, self.call = t, call


def conv(e, D):
    if isinstance(e, D.GenIter):
        return GenIterE([conv(x, D) for x in e.args.items] if e.args is not None else [])
    if isinstance(e, S.NewTable):
        # (items: an LPH_JIT table constructor, devirt special_set)
        return NewTableE([(conv(k, D) if k is not None else None, conv(v, D)) for k, v in e.items])
    if isinstance(e, Index):
        return Index(conv(e.obj, D), conv(e.key, D))
    if isinstance(e, Bin):
        return Bin(e.op, conv(e.a, D), conv(e.b, D))
    if isinstance(e, Un):
        return Un(e.op, conv(e.a, D))
    if e is None:
        return Const(None)
    return e


def conv_multi(m, D):
    return Multi([conv(x, D) if not isinstance(x, SymList) else x for x in m.items], conv_tail(m.tail))


def conv_tail(t):
    return t


# --------------------------------------------------------------------------
# liveness + folding

def stmt_uses(st):
    """(regs read, temps read) by a statement (lvalue sub-expressions count as reads)."""
    regs, temps = [], []
    for e in _stmt_exprs(st):
        regs += regs_read(e)
        temps += temps_read(e)
    return regs, temps


def stmt_regs(st):
    """The registers a statement reads (stmt_uses without the temps)."""
    return {x.n for e in _stmt_exprs(st) for x in walk(e) if isinstance(x, Reg)}


def _stmt_exprs(st):
    exprs = []
    if isinstance(st, AssignS):
        for t in st.targets:
            if not isinstance(t, (Reg, Pseudo)):
                exprs.append(t)
        exprs += list(st.values.items)
        if st.values.tail is not None:
            exprs.append(TailRef(st.values.tail))
    elif isinstance(st, TempDef):
        exprs.append(st.call)
    elif isinstance(st, CallS):
        exprs.append(st.call)
    elif isinstance(st, SetListS):
        exprs.append(st.tbl)
        exprs += list(st.values.items)
        if st.values.tail is not None:
            exprs.append(TailRef(st.values.tail))
    elif isinstance(st, ForPrepS):
        exprs += list(st.exprs)
    return exprs


def stmt_defs(st):
    if isinstance(st, AssignS):
        return [t.n for t in st.targets if isinstance(t, Reg)]
    return []


def term_uses(b):
    exprs = []
    # (for headers: their expressions are uses of the ForPrepS before the loop)
    if b.kind == "cond":
        exprs.append(b.cond)
    elif b.kind == "ret" and b.values is not None:
        exprs += list(b.values.items)
        if b.values.tail is not None:
            exprs.append(TailRef(b.values.tail))
    regs, temps = [], []
    for e in exprs:
        regs += regs_read(e)
        temps += temps_read(e)
    return regs, temps


def liveness(blocks):
    """live-out register sets per block."""
    use, defs = {}, {}
    for b in blocks.values():
        u, d = set(), set()
        for st in b.stmts:
            u |= stmt_regs(st) - d
            d |= set(stmt_defs(st))
        r, _ = term_uses(b)
        u |= set(r) - d
        if b.kind == "for":
            d.add(b.values[0])
        elif b.kind == "forin":
            d |= set(b.values[0])
        use[b.id], defs[b.id] = u, d
    live_in = {bid: set() for bid in blocks}
    live_out = {bid: set() for bid in blocks}
    changed = True
    order = list(blocks)
    while changed:
        changed = False
        for bid in reversed(order):
            b = blocks[bid]
            out = set()
            for s in b.succ:
                out |= live_in.get(s, set())
            inn = use[bid] | (out - defs[bid])
            if out != live_out[bid] or inn != live_in[bid]:
                live_out[bid], live_in[bid] = out, inn
                changed = True
    return live_out


def movable(e):
    """Can this expression be evaluated later than written (no reads of mutable state)?"""
    for x in walk(e):
        if isinstance(x, (CallE, Index, Global, Upval, Vararg, TempVal, GenIterE, TailRef)):
            return False
    return True


def simplify_block(b, live_out, temp_uses_total, open_in=frozenset()):
    st = b.stmts
    # --- temps: fold `t := call` into its uses
    out = []
    i = 0
    while i < len(st):
        s = st[i]
        if isinstance(s, TempDef):
            n_uses = temp_uses_total.get(s.t, 0)
            if n_uses == 0:
                out.append(CallS(s.call))
                i += 1
                continue
            # consecutive `rX = T[1]; rY = T[2] ...` (all uses of t)
            j = i + 1
            targets = []
            while j < len(st) and isinstance(st[j], AssignS) and len(st[j].targets) == 1 and \
                    len(st[j].values.items) == 1 and st[j].values.tail is None and \
                    isinstance(st[j].values.items[0], TempVal) and st[j].values.items[0].t == s.t and \
                    st[j].values.items[0].i == len(targets) + 1:
                targets.append(st[j].targets[0])
                j += 1
            if targets and len(targets) == n_uses:
                # one target takes the first value: a plain expression (inlinable)
                out.append(AssignS(targets, Multi([s.call]) if len(targets) == 1
                                   else Multi([], InlineTail(s.call))))
                i = j
                continue
            # single use as a tail / single value in a later statement of this block
            if n_uses == 1:
                k = i + 1
                blocked = False
                inputs = set(regs_read(s.call))
                while k < len(st):
                    _, ts = stmt_uses(st[k])
                    if s.t in ts:
                        break
                    if inputs & set(stmt_defs(st[k])):
                        # the call would read a register after it was overwritten
                        blocked = True
                    elif isinstance(st[k], (CloseS, CommentS)) or fresh_table_store(st, k):
                        pass
                    elif not isinstance(st[k], AssignS) or \
                            any(not isinstance(t, (Reg, Pseudo)) for t in st[k].targets) \
                            or any(has_side_effects(v) for v in st[k].values.items):
                        blocked = True
                    k += 1
                if k < len(st) and not blocked and not call_before(st[k], b, is_temp(s.t)) \
                        and not truncated_use(st[k], b, lambda x: isinstance(x, TempVal) and x.t == s.t):
                    st[k] = subst_temp(st[k], s.t, s.call)
                    i += 1
                    continue
                if k == len(st) and not blocked:
                    _, ts = term_uses(b)
                    if s.t in ts and not call_before(None, b, is_temp(s.t)):
                        b.cond = replace_temp(b.cond, s.t, s.call) if b.cond is not None else None
                        if b.kind == "ret" and b.values is not None:
                            b.values = replace_temp_multi(b.values, s.t, s.call)
                        i += 1
                        continue
            out.append(s)
            i += 1
            continue
        out.append(s)
        i += 1
    b.stmts = out
    # --- registers: inline single-use definitions (one forward sweep per
    # round; per-statement uses/defs memoized: this is the lifter's hot loop)
    memo = {}

    def ud(x):
        m = memo.get(id(x))
        if m is None or m[0] is not x:
            u = stmt_uses(x)[0]
            m = memo[id(x)] = (x, u, stmt_defs(x))
        return m[1], m[2]
    ud.memo = memo

    changed = True
    while changed:
        changed = False
        st = b.stmts
        opened = set(open_in)       # open registers before st[i]
        i = 0
        while i < len(st):
            s = st[i]
            if inline_def(b, st, i, live_out, opened, ud):
                changed = True
                continue
            open_step(s, b, opened)
            i += 1


def inline_def(b, st, i, live_out, opened, ud):
    """Inline `r = val` (st[i]) into its single use if that is safe; True if done."""
    s = st[i]
    if not (isinstance(s, AssignS) and len(s.targets) == 1 and isinstance(s.targets[0], Reg)
            and len(s.values.items) == 1 and s.values.tail is None):
        return False
    r = s.targets[0].n
    val = s.values.items[0]
    if isinstance(val, FuncE) or r in opened:
        return False
    if isinstance(val, ClosureExpr):
        # a closure moves into its use only from right before it (by-value
        # captures read registers at creation), and never when it
        # captures its own variable (recursive local function)
        if r in regs_read(val):
            return False
        nxt = st[i + 1] if i + 1 < len(st) else None
        if nxt is not None and r not in ud(nxt)[0]:
            return False
        # never as the callee: `(function(...) <body> end)(args)` hides a named helper
        if nxt is not None and any(isinstance(x, CallE) and isinstance(x.fn, Reg) and x.fn.n == r
                                   for x in stmt_eval_order(nxt, None)):
            return False
    # find the next use / redefinition
    uses = 0
    use_at = None
    redefined = False
    for k in range(i + 1, len(st)):
        ru, dk = ud(st[k])
        c = ru.count(r)
        if c:
            uses += c
            if use_at is None:
                use_at = k
            elif k != use_at:
                return False        # used in two statements
            if uses > 2:
                return False
        if r in dk:
            redefined = True
            break
    else:
        tr, _ = term_uses(b)
        if r in tr:
            uses += tr.count(r)
            if use_at is None:
                use_at = "term"
            else:
                return False
    if uses == 2 and use_at != "term" and method_self(st[use_at], r):
        uses = 1     # obj:m(...) reads its object once (NAMECALL), even a call result
    if uses != 1 or use_at is None:
        return False
    # a closure capturing r needs the variable itself (no expression to inline into)
    if captures_reg(st[use_at] if use_at != "term" else None, b, r):
        return False
    if not redefined and r in live_out:
        return False
    # anything between definition and use that could change what `val` reads?
    stop = len(st) if use_at == "term" else use_at
    deps = set(regs_read(val))
    mov = movable(val)
    for k in range(i + 1, stop):
        if deps & set(ud(st[k])[1]):
            return False
        if not mov and not pure_stmt(st[k]):
            return False
    if use_at != "term" and not prefix_ok(val) and r in target_regs(st[use_at]):
        return False
    if expands(val) and truncated_use(st[use_at] if use_at != "term" else None, b, r):
        return False        # f((g())) reads worse than a named local
    # inside the using statement, nothing with side effects may run before
    # the register is read (the value would move after it)
    if not mov and call_before(st[use_at] if use_at != "term" else None, b, r):
        return False
    if use_at == "term":
        if b.cond is not None:
            b.cond = replace_reg(b.cond, r, val)
        if b.kind == "ret" and b.values is not None:
            b.values = replace_reg_multi(b.values, r, val)
    else:
        old = st[use_at]
        st[use_at] = subst_reg(old, r, val)
        if st[use_at] is old:
            ud.memo.pop(id(old), None)      # updated in place (ForPrepS): stale memo
    del st[i]
    return True


def truncated_use(st, b, hit):
    """Is the value `hit` (a register number, or a predicate on expressions)
    the last value of an argument list / array items in st (the block's
    terminator for None), where a call would need truncation parentheses
    (`f((g()))`)? Returns are left out: `return (s:gsub(...))` is idiomatic."""
    if not callable(hit):
        r = hit
        hit = lambda x: isinstance(x, Reg) and x.n == r     # noqa: E731

    def last_hit(m):
        return m is not None and m.tail is None and bool(m.items) and hit(m.items[-1])
    for e in stmt_eval_order(st, b):
        if isinstance(e, CallE) and last_hit(e.args):
            return True
        if isinstance(e, NewTableE) and e.tail is None and e.items and e.items[-1][0] is None \
                and hit(e.items[-1][1]):
            return True
    return isinstance(st, SetListS) and last_hit(st.values)


def eval_order(e, out):
    """Post-order list of sub-expressions in Luau evaluation order."""
    if e is None:
        return
    if isinstance(e, TailRef):
        if isinstance(e.tail, InlineTail):
            eval_order(e.tail.call, out)
    elif isinstance(e, Index):
        eval_order(e.obj, out)
        eval_order(e.key, out)
    elif isinstance(e, Bin):
        eval_order(e.a, out)
        eval_order(e.b, out)
    elif isinstance(e, Un):
        eval_order(e.a, out)
    elif isinstance(e, IfExp):
        eval_order(e.c, out)
        eval_order(e.a, out)
        eval_order(e.b, out)
    elif isinstance(e, CallE):
        eval_order(e.fn, out)
        for x in e.args.items:
            eval_order(x, out)
        if e.args.tail is not None:
            eval_order(TailRef(e.args.tail), out)
    elif isinstance(e, NewTableE):
        for k, v in e.items:
            eval_order(k, out)
            eval_order(v, out)
        if e.tail is not None:
            eval_order(TailRef(e.tail), out)
    elif isinstance(e, SymList):
        for x in e.items:
            eval_order(x, out)
    out.append(e)


def stmt_eval_order(st, b):
    out = []
    if st is None:
        if b.cond is not None:
            eval_order(b.cond, out)
        if b.kind == "ret" and b.values is not None:
            for x in b.values.items:
                eval_order(x, out)
            if b.values.tail is not None:
                eval_order(TailRef(b.values.tail), out)
    elif isinstance(st, AssignS):
        for t in st.targets:
            if isinstance(t, Index):
                eval_order(t.obj, out)
                eval_order(t.key, out)
        for x in st.values.items:
            eval_order(x, out)
        if st.values.tail is not None:
            eval_order(TailRef(st.values.tail), out)
    elif isinstance(st, (CallS, TempDef)):
        eval_order(st.call, out)
    elif isinstance(st, SetListS):
        eval_order(st.tbl, out)
        for x in st.values.items:
            eval_order(x, out)
        if st.values.tail is not None:
            eval_order(TailRef(st.values.tail), out)
    elif isinstance(st, ForPrepS):
        for x in st.exprs:
            eval_order(x, out)
    return out


def call_before(st, b, r):
    """Does a call finish (or a closure get created) before register r is read
    (r: a register number, or a predicate on expressions)?"""
    hit = r if callable(r) else (lambda x: isinstance(x, Reg) and x.n == r)
    for x in stmt_eval_order(st, b):
        if hit(x):
            return False
        if isinstance(x, (CallE, ClosureExpr)):
            return True
    return False


def is_temp(t):
    def hit(x):
        return (isinstance(x, TempVal) and x.t == t) or             (isinstance(x, TailRef) and isinstance(x.tail, TempTail) and x.tail.t == t)
    return hit


def stable_path(e):
    """Expressions that give the same value when read twice in a row."""
    if isinstance(e, (Reg, Const, Global, Upval, LocalName)):
        return True
    return isinstance(e, Index) and isinstance(e.key, Const) and stable_path(e.obj)


def method_self(st, r):
    """Does the statement contain a method call r:name(...) (r as object and first argument)?"""
    exprs = stmt_eval_order(st, None) if st is not None else []
    for x in exprs:
        if isinstance(x, CallE) and isinstance(x.fn, Index) and isinstance(x.fn.obj, Reg) and x.fn.obj.n == r                 and x.args.items and isinstance(x.args.items[0], Reg) and x.args.items[0].n == r                 and isinstance(x.fn.key, Const) and isinstance(x.fn.key.v, bytes):
            return True
    return False


def ref_captures(exprs):
    out = set()
    for x in exprs:
        if isinstance(x, ClosureExpr):
            for u in x.upvals:
                if type(u).__name__ == "MaybeBox":
                    out.add(u.reg)
                elif isinstance(u, S.LTable) and any(type(v).__name__ == "RegFile" for v in u.h.values()):
                    out |= {v for v in u.h.values() if isinstance(v, int)}
            # registers the closure reads through a captured frame
            out |= set(getattr(x, "frame_regs", ()))
    return out


def open_step(st, b, cur):
    """Open (captured by reference, not closed yet) registers after a statement."""
    if isinstance(st, CloseS):
        cur.discard(st.reg)
    else:
        cur |= ref_captures(stmt_eval_order(st, b))


def open_registers(blocks):
    """Registers open at each block entry. While a register is open, closures
    read it through their box whenever they run: every assignment matters."""
    preds = {bid: [] for bid in blocks}
    for b in blocks.values():
        for x in b.succ:
            if x in preds:
                preds[x].append(b.id)
    inn = {bid: set() for bid in blocks}
    out = {bid: set() for bid in blocks}
    changed = True
    while changed:
        changed = False
        for b in blocks.values():
            cur = set()
            for p in preds[b.id]:
                cur |= out[p]
            inn[b.id] = set(cur)
            for st in b.stmts:
                open_step(st, b, cur)
            cur |= ref_captures(stmt_eval_order(None, b))
            if cur != out[b.id]:
                out[b.id] = cur
                changed = True
    return inn


def open_before(b, i, open_in):
    cur = set(open_in)
    for st in b.stmts[:i]:
        open_step(st, b, cur)
    return cur


def copy_propagate(b, live_out, open_in=frozenset()):
    """`rX = rY` / `rX = constant` (Luraph moves values through scratch
    registers): use the source directly while neither is reassigned."""
    st = b.stmts
    i = 0
    opened = set(open_in)       # open registers before st[i]
    # registers each statement reads (the scans below are quadratic; changed
    # statements are replaced by new objects, never mutated here)
    memo = {}

    def reads(x):
        e = memo.get(id(x))
        if e is None or e[0] is not x:
            e = memo[id(x)] = (x, stmt_regs(x))
        return e[1]

    def advance():
        open_step(st[i], b, opened)
        return i + 1
    while i < len(st):
        s = st[i]
        if not (isinstance(s, AssignS) and len(s.targets) == 1 and isinstance(s.targets[0], Reg)
                and len(s.values.items) == 1 and s.values.tail is None
                and isinstance(s.values.items[0], (Reg, Const, Upval)) and not getattr(s, "jump", False)):
            i = advance()
            continue
        r = s.targets[0].n
        val = s.values.items[0]
        src = val.n if isinstance(val, Reg) else None
        if r in opened or src in opened:
            i = advance()
            continue
        if src == r:
            del st[i]
            continue
        uses = []
        ok = True
        end = None
        for k in range(i + 1, len(st)):
            if r in reads(st[k]):
                if captures_reg(st[k], b, r) or (isinstance(val, Const) and r in target_regs(st[k])):
                    ok = False
                    break
                uses.append(k)
            d = stmt_defs(st[k])
            if r in d:
                end = k
                break
            if src is not None and src in d:
                # later uses would see the new source value
                for k2 in range(k + 1, len(st)):
                    if r in reads(st[k2]):
                        ok = False
                        break
                    if r in stmt_defs(st[k2]):
                        end = k2
                        break
                if ok and end is None:
                    tr, _ = term_uses(b)
                    if r in tr or r in live_out:
                        ok = False
                end = end if end is not None else len(st)
                break
        else:
            tr, _ = term_uses(b)
            if r in live_out:
                ok = False
            elif r in tr:
                if captures_reg(None, b, r):
                    ok = False
                else:
                    uses.append("term")
        if ok and uses and isinstance(val, Upval):
            # an upvalue can change under any call: only when nothing between
            # here and the last use runs code
            last = max(k for k in uses if k != "term") if any(k != "term" for k in uses) else len(st) - 1
            if "term" in uses:
                last = len(st) - 1
            if any(not pure_stmt(st[k]) and not fresh_table_store(st, k) for k in range(i + 1, last)) or \
                    any(k != "term" and call_before(st[k], b, r) for k in uses):
                ok = False
        if not ok or not uses:
            i = advance()
            continue
        for k in uses:
            if k == "term":
                if b.cond is not None:
                    b.cond = replace_reg(b.cond, r, val)
                if b.kind == "ret" and b.values is not None:
                    b.values = replace_reg_multi(b.values, r, val)
            else:
                st[k] = subst_reg(st[k], r, val)
        del st[i]


def fresh_table_store(st, k):
    """st[k] is `t[const] = <pure>` into a table built in this block that
    nothing else has seen yet (a table constructor in progress): no call can
    observe it, so a call may move across it."""
    s = st[k]
    if not (isinstance(s, AssignS) and len(s.targets) == 1 and isinstance(s.targets[0], Index)
            and isinstance(s.targets[0].obj, Reg) and isinstance(s.targets[0].key, Const)
            and len(s.values.items) == 1 and s.values.tail is None and movable(s.values.items[0])):
        return False
    r = s.targets[0].obj.n
    for j in range(k - 1, -1, -1):
        p = st[j]
        if r in stmt_defs(p):
            return (isinstance(p, AssignS) and len(p.targets) == 1 and len(p.values.items) == 1
                    and isinstance(p.values.items[0], NewTableE))
        if r in stmt_regs(p):
            # only other stores into it
            if not (isinstance(p, AssignS) and len(p.targets) == 1 and isinstance(p.targets[0], Index)
                    and isinstance(p.targets[0].obj, Reg) and p.targets[0].obj.n == r
                    and r not in regs_read(p.targets[0].key)
                    and all(r not in regs_read(v) for v in p.values.items)):
                return False
    return False


def fold_iterator_call(b, live_out):
    """`f, s, c = pairs(t)` before a generic for's ForPrepS(f, s, c): the call
    goes into the loop header (`for k, v in pairs(t) do`). Pure register
    moves in between are fine when they don't touch the call's inputs."""
    st = b.stmts
    i = 0
    while i < len(st):
        s = st[i]
        if not (isinstance(s, AssignS) and not s.values.items and isinstance(s.values.tail, InlineTail)
                and len(s.targets) >= 2 and all(isinstance(t, Reg) for t in s.targets)):
            i += 1
            continue
        regs = {t.n for t in s.targets}
        reads = set(regs_read(s.values.tail.call))
        j = i + 1
        while j < len(st) and not isinstance(st[j], ForPrepS) and pure_stmt(st[j])                 and not (set(stmt_defs(st[j])) & (reads | regs)) and not (stmt_regs(st[j]) & regs):
            j += 1
        p = st[j] if j < len(st) else None
        if isinstance(p, ForPrepS) and len(s.targets) == len(p.exprs)                 and all(isinstance(e, Reg) and e.n == t.n for e, t in zip(p.exprs, s.targets)):
            later = set()
            for x in st[j + 1:]:
                later |= stmt_regs(x)
            later |= set(term_uses(b)[0])
            if not (regs & (later | set(live_out))):
                p.exprs[:] = [TailRef(s.values.tail)]
                del st[i]
                continue
        i += 1


def drop_dead_packs(b, live_out):
    """Luraph keeps every multi-value result list in a register (table.pack);
    consumers read the values directly, so most of these are never read.
    Also drops dead closures of evaluated decryptor calls."""
    live = set(live_out) | set(term_uses(b)[0])
    keep = []
    for st in reversed(b.stmts):
        if getattr(st, "pack", False) and isinstance(st.targets[0], Reg) and st.targets[0].n not in live:
            continue
        if isinstance(st, AssignS) and len(st.targets) == 1 and isinstance(st.targets[0], Reg)                 and len(st.values.items) == 1 and getattr(st.values.items[0], "frame_evaluated", False)                 and st.targets[0].n not in live:
            continue    # a string decryptor whose calls were all evaluated (devirt.frame_call)
        live -= set(stmt_defs(st))
        live |= stmt_regs(st)
        keep.append(st)
    b.stmts = keep[::-1]


def captures_reg(st, b, r):
    """Does the statement (or, st None, the block terminator) capture register r in a closure?"""
    if st is None:
        exprs = [b.cond] if b.cond is not None else []
        if b.values is not None and hasattr(b.values, "items"):
            exprs += list(b.values.items)
    else:
        exprs = []
        if isinstance(st, AssignS):
            exprs = list(st.targets) + list(st.values.items)
        elif isinstance(st, (CallS, TempDef)):
            exprs = [st.call]
        elif isinstance(st, SetListS):
            exprs = [st.tbl] + list(st.values.items)
        if getattr(st, "values", None) is not None and getattr(st.values, "tail", None) is not None:
            exprs.append(TailRef(st.values.tail))
    for e in exprs:
        for x in walk(e):
            if isinstance(x, ClosureExpr) and r in [c.n for c in children(x)]:
                return True
    return False


def prefix_ok(e):
    """Can stand before `.x` / `[k]` / `(...)` in a statement without parentheses?"""
    return isinstance(e, (Reg, Global, Upval, Index, CallE, LocalName))


def target_regs(st):
    if isinstance(st, AssignS):
        out = []
        for t in st.targets:
            if not isinstance(t, (Reg, Pseudo)):
                out += regs_read(t)
        return out
    if isinstance(st, SetListS):
        return regs_read(st.tbl)
    if isinstance(st, CallS):
        return regs_read(st.call.fn) if isinstance(st.call, CallE) else []
    return []


def pure_stmt(st):
    """Statement that cannot change globals/tables/upvalues (register moves only)."""
    if isinstance(st, (CloseS, CommentS)):
        return True
    return isinstance(st, AssignS) and all(isinstance(t, (Reg, Pseudo)) for t in st.targets) and \
        not any(has_side_effects(v) for v in st.values.items) and \
        not (st.values.tail is not None and isinstance(st.values.tail, InlineTail))


def replace_reg(e, r, val):
    return S_map(e, lambda x: val if isinstance(x, Reg) and x.n == r else None)


def S_map(e, fn):
    return map_expr(e, fn)


def replace_reg_multi(m, r, val):
    return map_multi(m, lambda x: val if isinstance(x, Reg) and x.n == r else None)


def replace_temp(e, t, call):
    def fn(x):
        if isinstance(x, TempVal) and x.t == t:
            return call if x.i == 1 else Index(CallE(Global("table.pack"), Multi([], InlineTail(call))), Const(x.i))
        if isinstance(x, TailRef) and isinstance(x.tail, TempTail) and x.tail.t == t:
            if x.tail.start == 1:
                return TailRef(InlineTail(call))
            return TailRef(InlineTail(CallE(Global("select"), Multi([Const(x.tail.start)], InlineTail(call)))))
        return None
    return map_expr(e, fn)


def expand_tail_items(items, t, call):
    return [replace_temp(x, t, call) for x in items]


def replace_temp_multi(m, t, call):
    items = [replace_temp(x, t, call) for x in m.items]
    tail = m.tail
    if tail is not None:
        r = replace_temp(TailRef(tail), t, call)
        tail = r.tail if isinstance(r, TailRef) else tail
    return Multi(items, tail)


def subst_temp(st, t, call):
    return map_stmt(st, lambda e: replace_temp(e, t, call), lambda m: replace_temp_multi(m, t, call))


def subst_reg(st, r, val):
    return map_stmt(st, lambda e: replace_reg(e, r, val), lambda m: replace_reg_multi(m, r, val))


def map_stmt(st, fe, fm):
    if isinstance(st, AssignS):
        tg = [t if isinstance(t, (Reg, Pseudo)) else fe(t) for t in st.targets]
        return AssignS(tg, fm(st.values))
    if isinstance(st, TempDef):
        return TempDef(st.t, fe(st.call))
    if isinstance(st, CallS):
        return CallS(fe(st.call))
    if isinstance(st, SetListS):
        return SetListS(fe(st.tbl), st.start, fm(st.values))
    if isinstance(st, ForPrepS):
        # the list is shared with the loop header: update in place
        st.exprs[:] = [fe(x) for x in st.exprs]
        return st
    return st


def count_temp_uses(blocks):
    cnt = {}
    for b in blocks.values():
        for st in b.stmts:
            _, ts = stmt_uses(st)
            for t in ts:
                cnt[t] = cnt.get(t, 0) + 1
        _, ts = term_uses(b)
        for t in ts:
            cnt[t] = cnt.get(t, 0) + 1
    return cnt


FOLD_ARITH = ("Add", "Sub", "Mul", "Div", "FloorDiv", "Mod", "Pow")


def _num(e):
    return isinstance(e, Const) and isinstance(e.v, (int, float)) and not isinstance(e.v, bool)


def _fold_node(x):
    """One constant folding step (children already folded), or None."""
    if isinstance(x, Bin) and x.op in FOLD_ARITH and _num(x.a) and _num(x.b):
        a, b = x.a.v, x.b.v
        if any(isinstance(v, int) and abs(v) >= 2 ** 53 for v in (a, b)):
            return None
        try:
            r = S.arith(x.op, a, b)
        except (OverflowError, ZeroDivisionError, S.Unsupported):
            return None
        if isinstance(r, float) and not math.isfinite(r):
            return None
        if isinstance(r, int) and abs(r) >= 2 ** 53:
            return None
        return Const(r)
    if isinstance(x, CallE) and x.method is None and isinstance(x.fn, Global) and x.fn.name.startswith("bit32.")             and x.fn.name in S.CONCRETE and x.args.tail is None and x.args.items             and all(_num(a) and float(a.v).is_integer() and abs(a.v) < 2 ** 53 for a in x.args.items):
        try:
            return Const(S.CONCRETE[x.fn.name](*[int(a.v) for a in x.args.items]))
        except (ValueError, TypeError, OverflowError, IndexError, S.Unsupported):
            return None
    if isinstance(x, Index) and isinstance(x.obj, CallE) and isinstance(x.obj.fn, Global)             and x.obj.fn.name == "table.pack" and x.obj.args.tail is None and isinstance(x.key, Const)             and isinstance(x.key.v, int) and not isinstance(x.key.v, bool)             and all(isinstance(a, Const) for a in x.obj.args.items):
        items = x.obj.args.items
        return items[x.key.v - 1] if 1 <= x.key.v <= len(items) else Const(None)
    return None


def _has_foldable(e):
    return any(_fold_node(x) is not None for x in walk(e))


def fold_constants(e):
    """Arithmetic and bit32 calls on constants, bottom-up (Luraph's number
    encryption builds constants from long chains of them)."""
    if e is None or not _has_foldable(e):
        return e

    def fn(x):
        if x is e or not isinstance(x, (Bin, CallE, Index, Un, IfExp, NewTableE)):
            return None
        return fold_constants(x)
    e = map_expr(e, fn)
    r = _fold_node(e)
    return r if r is not None else e


def fold_constants_block(b):
    """Fold constants in a block. True if anything changed."""
    changed = False
    out = []
    for st in b.stmts:
        if any(_has_foldable(x) for x in stmt_exprs(st)):
            st = map_stmt(st, fold_constants, lambda m: Multi([fold_constants(x) for x in m.items], m.tail))
            changed = True
        out.append(st)
    b.stmts = out
    if b.cond is not None and _has_foldable(b.cond):
        b.cond, changed = fold_constants(b.cond), True
    if b.kind == "ret" and b.values is not None and any(_has_foldable(x) for x in b.values.items):
        b.values, changed = Multi([fold_constants(x) for x in b.values.items], b.values.tail), True
    return changed


def fold_const_temps(blocks):
    """t := <constant call> whose uses are all single values: the constant."""
    consts = {}
    for b in blocks.values():
        for st in b.stmts:
            if isinstance(st, TempDef):
                r = st.call if isinstance(st.call, Const) else _fold_node(st.call)
                if r is not None:
                    consts[st.t] = r
    if not consts:
        return False
    # temps used through a multret tail keep their call
    for b in blocks.values():
        for st in b.stmts:
            for e in stmt_exprs(st):
                for x in walk(e):
                    if isinstance(x, TailRef) and isinstance(x.tail, TempTail):
                        consts.pop(x.tail.t, None)
        for e in term_exprs(b):
            for x in walk(e):
                if isinstance(x, TailRef) and isinstance(x.tail, TempTail):
                    consts.pop(x.tail.t, None)
            if isinstance(e, Multi) and isinstance(e.tail, TempTail):
                consts.pop(e.tail.t, None)
    for b in blocks.values():
        for st in b.stmts:
            if isinstance(st, (AssignS, SetListS)) and isinstance(st.values.tail, TempTail):
                consts.pop(st.values.tail.t, None)
    if not consts:
        return False

    def fn(x):
        if isinstance(x, TempVal) and x.t in consts:
            return consts[x.t] if x.i == 1 else Const(None)
        return None
    for b in blocks.values():
        b.stmts = [map_stmt(st, lambda e: map_expr(e, fn), lambda m: map_multi(m, fn))
                   for st in b.stmts if not (isinstance(st, TempDef) and st.t in consts)]
        if b.cond is not None:
            b.cond = map_expr(b.cond, fn)
        if b.kind == "ret" and b.values is not None:
            b.values = map_multi(b.values, fn)
    return True


def stmt_exprs(st):
    if isinstance(st, AssignS):
        return list(st.targets) + list(st.values.items)
    if isinstance(st, (TempDef, CallS)):
        return [st.call]
    if isinstance(st, SetListS):
        return [st.tbl] + list(st.values.items)
    if isinstance(st, ForPrepS):
        return list(st.exprs)
    return []


def term_exprs(b):
    out = []
    if b.cond is not None:
        out.append(b.cond)
    if b.kind == "ret" and b.values is not None:
        out += list(b.values.items)
        out.append(b.values)
    return out


def simplify_blocks(blocks, D):
    for b in blocks.values():
        b.stmts = convert_stmts(b.stmts, D)
        if b.cond is not None:
            b.cond = conv(b.cond, D)
        if b.kind == "ret" and b.values is not None:
            b.values = conv_multi(b.values, D)
    for i in range(12):
        if i >= 3:
            # only continue while constant folding opens up more folding
            changed = fold_const_temps(blocks)
            for b in blocks.values():
                changed |= fold_constants_block(b)
            if not changed:
                break
        live_out = liveness(blocks)
        for b in blocks.values():
            drop_dead_packs(b, live_out[b.id])
        tu = count_temp_uses(blocks)
        opened = open_registers(blocks)
        for b in blocks.values():
            copy_propagate(b, live_out[b.id], opened[b.id])
            simplify_block(b, live_out[b.id], tu, opened[b.id])
            fold_iterator_call(b, live_out[b.id])
    drop_redundant_stores(blocks)
    # table constructors: r = {} followed by r[k] = v / setlist. Nested
    # tables need several rounds: an inner constructor is built in a temp
    # register and only inlined into the outer store by simplify_block.
    for _ in range(8):
        changed = False
        for b in blocks.values():
            changed |= fold_tables(b)
        live_out = liveness(blocks)
        opened = open_registers(blocks)
        for b in blocks.values():
            copy_propagate(b, live_out[b.id], opened[b.id])
            simplify_block(b, live_out[b.id], count_temp_uses(blocks), opened[b.id])
        if not changed:
            break


def drop_redundant_stores(blocks):
    """`r = K` where r already holds the constant K on every path (Luraph
    repeats a flag store inside the branch after it): drop the second store.
    Registers a closure captures are left alone (it may change them)."""
    captured = set()
    for b in blocks.values():
        for st in b.stmts:
            captured |= ref_captures(stmt_eval_order(st, b))
        captured |= ref_captures(stmt_eval_order(None, b))

    def const_store(st):
        if isinstance(st, AssignS) and len(st.targets) == 1 and isinstance(st.targets[0], Reg) \
                and len(st.values.items) == 1 and st.values.tail is None \
                and isinstance(st.values.items[0], Const) and not getattr(st, "jump", False):
            v = st.values.items[0].v
            # type in the key: True == 1 and 0 == -0.0 in Python, not in Luau
            return st.targets[0].n, (type(v).__name__, repr(v))
        return None

    def step(st, facts):
        for d in stmt_defs(st):
            facts.pop(d, None)
        cs = const_store(st)
        if cs is not None:
            facts[cs[0]] = cs[1]

    def term_kill(b, facts):
        if b.kind == "for":
            facts.pop(b.values[0], None)
        elif b.kind == "forin":
            for r in b.values[0]:
                facts.pop(r, None)

    preds = {bid: [] for bid in blocks}
    for b in blocks.values():
        for x in b.succ:
            if x in preds:
                preds[x].append(b.id)
    out = {}                    # None = not reached yet (top)
    inn = {}
    changed = True
    while changed:
        changed = False
        for b in blocks.values():
            ps = [out.get(p) for p in preds[b.id]]
            ps = [p for p in ps if p is not None]
            if not preds[b.id]:
                cur = {}
            elif not ps:
                continue
            else:
                cur = dict(ps[0])
                for p in ps[1:]:
                    cur = {k: v for k, v in cur.items() if p.get(k) == v}
            inn[b.id] = dict(cur)
            for st in b.stmts:
                step(st, cur)
            term_kill(b, cur)
            if out.get(b.id) != cur:
                out[b.id] = cur
                changed = True
    for b in blocks.values():
        if b.id not in inn:
            continue
        cur = dict(inn[b.id])
        keep = []
        for st in b.stmts:
            cs = const_store(st)
            if cs is not None and cs[0] not in captured and cur.get(cs[0]) == cs[1]:
                continue
            step(st, cur)
            keep.append(st)
        b.stmts = keep


def fold_tables(b):
    """`t = {}` followed by `t[k] = v` / setlist -> one table constructor.
    Pure register moves may sit in between (Luraph loads the item functions
    into registers there) as long as they don't touch the table or what the
    items read: the constructor then takes the place of the last store."""
    st = b.stmts
    changed = False
    i = 0
    while i < len(st):
        s = st[i]
        if isinstance(s, AssignS) and len(s.targets) == 1 and isinstance(s.targets[0], Reg) and                 len(s.values.items) == 1 and isinstance(s.values.items[0], NewTableE):
            r = s.targets[0].n
            tbl = s.values.items[0]
            j = i + 1
            last = None             # index of the last store folded in
            consumed = []
            item_reads = set()
            pending = []            # intermediate statements (kept, before the constructor)
            while j < len(st):
                n = st[j]
                if isinstance(n, AssignS) and len(n.targets) == 1 and isinstance(n.targets[0], Index) and                         isinstance(n.targets[0].obj, Reg) and n.targets[0].obj.n == r and                         len(n.values.items) == 1 and n.values.tail is None and                         r not in regs_read(n.values.items[0]) and r not in regs_read(n.targets[0].key):
                    key = n.targets[0].key
                    if isinstance(key, Const) and key.v == count_array(tbl) + 1 and not isinstance(key.v, bool)                             and not any(isinstance(k, Const) and k.v == key.v for k, _ in tbl.items):
                        key = None      # next array slot: positional item
                    tbl.items.append((key, n.values.items[0]))
                    item_reads |= set(regs_read(n.values.items[0])) | set(regs_read(n.targets[0].key))
                    consumed.append(j)
                    last = j
                    j += 1
                    continue
                if isinstance(n, SetListS) and isinstance(n.tbl, Reg) and n.tbl.n == r and                         n.start == count_array(tbl) + 1:
                    for v in n.values.items:
                        tbl.items.append((None, v))
                        item_reads |= set(regs_read(v))
                    tbl.tail = n.values.tail
                    consumed.append(j)
                    last = j
                    j += 1
                    if n.values.tail is not None:
                        break
                    continue
                if pure_stmt(n) and isinstance(n, AssignS) and r not in stmt_regs(n)                         and r not in stmt_defs(n) and not (set(stmt_defs(n)) & item_reads):
                    pending.append(n)
                    j += 1
                    continue
                break
            if last is not None:
                # constructor at the last store; intermediates stay before it
                keep = [x for k2, x in enumerate(st[i + 1:last + 1], i + 1) if k2 not in consumed]
                st[i:last + 1] = keep + [s]
                i += len(keep)
                changed = True
        i += 1
    return changed


def count_array(tbl):
    return sum(1 for k, v in tbl.items if k is None)


# --------------------------------------------------------------------------
# rendering

IDENT = re.compile(r"^[A-Za-z_][A-Za-z_0-9]*$")
# a table constructor longer than this (plus its indent) is written one field per line
TABLE_WIDTH = 100


def expands(e):
    """Would this expression give several values in a multi-value position?"""
    if isinstance(e, CallE):
        return True
    return isinstance(e, Vararg)


def f32_short(x):
    """The shortest decimal that rounds to the same float32 as x (x a float32 value)."""
    import struct
    if not isinstance(x, (int, float)) or x != x or math.isinf(x):
        return x
    try:
        f = struct.unpack("<f", struct.pack("<f", x))[0]
    except OverflowError:
        return x
    if f != x:
        return x
    for d in range(1, 10):
        y = float("%.*g" % (d, x))
        if struct.unpack("<f", struct.pack("<f", y))[0] == f:
            return int(y) if y.is_integer() and abs(y) < 2 ** 53 else y
    return x


class Renderer:
    def __init__(self, names=None):
        self.names = names or {}

    def reg(self, n):
        if isinstance(n, LocalName):
            return n.name
        return self.names.get(n, "r%d" % n)

    def const(self, v):
        if v is None:
            return "nil"
        if v is True:
            return "true"
        if v is False:
            return "false"
        if isinstance(v, bytes):
            return quote(v)
        if isinstance(v, (int, float)):
            s = S.fmt_num(v)
            if s == "inf":
                return "math.huge"
            if s == "-inf":
                return "-math.huge"
            if s == "nan":
                return "(0/0)"
            if abs(v) >= 1e9 and float(v).is_integer():
                # 1e9, 2.5e10 rather than a row of zeros
                t = "%.3g" % v
                if "e" in t and float(t) == v:
                    m, x = t.split("e")
                    return "%se%d" % (m, int(x))
            return s
        return repr(v)

    def expr(self, e, prec=0):
        t = self.expr_raw(e, prec)
        return t

    def expr_raw(self, e, prec):
        if e is None:
            return "nil"
        if isinstance(e, Const):
            s = self.const(e.v)
            if s.startswith("-") and prec > 8:
                return "(" + s + ")"
            return s
        if isinstance(e, Reg):
            return self.reg(e.n)
        if isinstance(e, LocalName):
            return e.name
        if isinstance(e, Pseudo):
            return "%s_%d" % (e.name, e.depth)
        if isinstance(e, Global):
            # Luau has no _ENV: the environment of a Luraph script is getfenv()
            return "getfenv()" if e.name == "_ENV" else e.name
        if isinstance(e, Upval):
            return self.names.get(("up", e.idx), "upv%d" % e.idx if isinstance(e.idx, int)
                                  else "upv%d_%d" % e.idx)
        if isinstance(e, Vararg):
            return "..." if e.i == 1 else "select(%d, ...)" % e.i
        if isinstance(e, Index):
            k = e.key
            if isinstance(e.obj, Global) and e.obj.name == "_ENV" and isinstance(k, Const) \
                    and isinstance(k.v, bytes):
                name = k.v.decode("latin-1")
                if IDENT.match(name) and name not in LUA_KEYWORDS:
                    return name         # getfenv().x is the global x
            obj = self.prefix(e.obj)
            if isinstance(k, Const) and isinstance(k.v, bytes):
                name = k.v.decode("latin-1")
                if IDENT.match(name) and name not in LUA_KEYWORDS:
                    return "%s.%s" % (obj, name)
            return "%s[%s]" % (obj, self.expr(k))
        if isinstance(e, Bin) and e.op in FLIPPED and isinstance(e.a, Const) and not isinstance(e.b, Const):
            # the VM only has < and <=: `0 < x` was `x > 0` (constants: no evaluation order)
            return self.expr_raw(Bin(FLIPPED[e.op], e.b, e.a), prec)
        if isinstance(e, Bin):
            op, p = BINOPS[e.op]
            ra = p + 1 if e.op in RIGHT_ASSOC else p
            la = p if e.op not in RIGHT_ASSOC else p + 1
            s = "%s %s %s" % (self.expr(e.a, la), op, self.expr(e.b, ra if e.op not in RIGHT_ASSOC else p))
            return "(" + s + ")" if p < prec else s
        if isinstance(e, Un):
            if e.op == "Not":
                s = "not " + self.expr(e.a, 8)
            elif e.op == "Minus":
                s = "-" + self.expr(e.a, 8)
            else:
                s = "#" + self.expr(e.a, 8)
            return "(" + s + ")" if prec > 8 else s
        if isinstance(e, IfExp):
            s = "if %s then %s else %s" % (self.expr(e.c), self.expr(e.a), self.expr(e.b))
            return "(" + s + ")" if prec > 0 else s
        if isinstance(e, CallE):
            return self.call(e)
        if isinstance(e, NewTableE):
            return self.table(e)
        if isinstance(e, ClosureExpr):
            return "function(...) --[[ closure %r ]] end" % (e.proto,)
        if isinstance(e, FuncE):
            ind = getattr(self, "cur_ind", "")
            return "\n".join([e.lines[0]] + [ind + l for l in e.lines[1:]])
        if isinstance(e, GenIterE):
            return "geniter(%s)" % ", ".join(self.expr(a) for a in e.args)
        if isinstance(e, TempVal):
            return "t%s[%d]" % (e.t, e.i)
        if isinstance(e, TailCount):
            return "select(\"#\", %s)" % self.tail(e.tail)
        if isinstance(e, TailRef):
            return self.tail(e.tail)
        if isinstance(e, SymList):
            return "table.pack(%s)" % self.multi(Multi(e.items, e.tail))
        if type(e).__name__ == "Opaque":
            return e.src or "nil --[[ %s ]]" % e.kind
        if type(e).__name__ == "Vec":
            # Luau folds Vector3.new(constants) into one vector constant (float32
            # components: the shortest decimal for each, 9e9 rather than 8999999488)
            xyz = [f32_short(x) for x in e.xyz]
            if all(x == 0 for x in xyz):
                return "Vector3.zero"
            if all(x == 1 for x in xyz):
                return "Vector3.one"
            return "Vector3.new(%s)" % ", ".join(self.const(x) for x in xyz)
        if type(e).__name__ == "Missing":
            return "nil --[[ constant not decoded ]]"
        return "--[[?%s]]" % type(e).__name__

    def prefix(self, e):
        """Expression usable before `.x`, `[k]`, `(args)`, `:m()`."""
        s = self.expr(e, 11)
        if isinstance(e, (Reg, Global, Upval, Index, CallE, LocalName, Pseudo)) or \
                (isinstance(e, Const) is False and s.startswith("(")):
            return s
        return "(" + s + ")"

    def call(self, e):
        fn, args = e.fn, e.args
        # obj:method(...) when the first argument is the object the function was read from
        if isinstance(fn, Index) and isinstance(fn.key, Const) and isinstance(fn.key.v, bytes) and args.items:
            same = expr_key(args.items[0]) == expr_key(fn.obj) and not expr_key(fn.obj).startswith("X")
            obj_text = None
            if not same and type(args.items[0]) is type(fn.obj):
                # an object expression inlined into both slots of a NAMECALL
                # (evaluated once by the VM): same text -> method call
                obj_text = self.prefix(fn.obj)
                same = self.prefix(args.items[0]) == obj_text
            name = fn.key.v.decode("latin-1")
            if same and IDENT.match(name) and name not in LUA_KEYWORDS:
                rest = Multi(args.items[1:], args.tail)
                return "%s:%s(%s)" % (obj_text or self.prefix(fn.obj), name, self.multi(rest))
        return "%s(%s)" % (self.prefix(fn), self.multi(args))

    def tail(self, t):
        if isinstance(t, InlineTail):
            return self.expr(t.call)
        if isinstance(t, TempTail):
            return "table.unpack(t%s, %d, t%s.n)" % (t.t, t.start, t.t)
        if isinstance(t, VarargTail):
            return "..." if t.start == 1 else "select(%d, ...)" % t.start
        return "--[[tail?]]"

    def multi(self, m, trunc=True):
        """An expression list. A call or `...` in the last position would
        expand to all its values; as an item it means the first value only,
        so it gets parentheses (trunc=False: the context truncates anyway)."""
        parts = [self.expr(x) for x in m.items]
        if m.tail is not None:
            parts.append(self.tail(m.tail))
        elif parts and trunc and expands(m.items[-1]):
            parts[-1] = "(" + parts[-1] + ")"
        return ", ".join(parts)

    def table(self, t):
        """One line when it fits (TABLE_WIDTH columns at the statement's
        indent), else one field per line with a trailing comma, as are
        tables holding a function among other fields (`{ Name = ...,
        Callback = function ... end }`). Items render one level deeper,
        so nested tables and function bodies indent under the field."""
        if not t.items and t.tail is None:
            return "{}"
        ind = getattr(self, "cur_ind", "")
        self.cur_ind = ind + "\t"
        try:
            parts = self.table_items(t)
        finally:
            self.cur_ind = ind
        one = "{ " + ", ".join(parts) + " }"
        if not any("\n" in p for p in parts) and 4 * len(ind) + len(one) <= TABLE_WIDTH:
            return one
        if len(parts) == 1 and t.tail is None and isinstance(t.items[0][1], FuncE):
            # a single function item: keep `{ function() ... end }`
            return "{ " + ", ".join(self.table_items(t)) + " }"
        return "{\n" + "".join(ind + "\t" + p + ",\n" for p in parts) + ind + "}"

    def table_items(self, t):
        parts = []
        for i, (k, v) in enumerate(t.items):
            if k is None:
                last = i == len(t.items) - 1 and t.tail is None
                parts.append("(%s)" % self.expr(v) if last and expands(v) else self.expr(v))
            elif isinstance(k, Const) and isinstance(k.v, bytes) and IDENT.match(k.v.decode("latin-1")) \
                    and k.v.decode("latin-1") not in LUA_KEYWORDS:
                parts.append("%s = %s" % (k.v.decode("latin-1"), self.expr(v)))
            else:
                parts.append("[%s] = %s" % (self.expr(k), self.expr(v)))
        if t.tail is not None:
            parts.append(self.tail(t.tail))
        return parts

    # statements
    def block(self, stmts, ind):
        out = []
        for st in stmts:
            # nested functions render as one multi-line string: keep physical lines
            lines = self.stmt(st, ind)
            if out and lines and lines[0][len(ind):].startswith("("):
                # `(f)(x)` after a statement would continue it as a call
                lines[0] = ind + ";" + lines[0][len(ind):]
            for x in lines:
                out += x.split("\n")
        return out

    def stmt(self, st, ind):
        self.cur_ind = ind
        if isinstance(st, AssignS):
            # extra targets would take further values of a trailing call
            vals = self.multi(st.values, trunc=len(st.targets) > len(st.values.items))
            tg = ", ".join(self.lvalue(t) for t in st.targets)
            if getattr(st, "is_local", False):
                return [ind + "local %s = %s" % (tg, vals)]
            # x = x + y  ->  x += y (a plain variable: nothing is evaluated twice)
            v = st.values.items[0] if len(st.values.items) == 1 and st.values.tail is None else None
            if len(st.targets) == 1 and isinstance(st.targets[0], (LocalName, Reg, Upval)) \
                    and isinstance(v, Bin) and v.op in COMPOUND and type(v.a) is type(st.targets[0]) \
                    and self.expr(v.a) == tg:
                op, p = BINOPS[v.op]
                return [ind + "%s %s= %s" % (tg, op, self.expr(v.b))]
            return [ind + "%s = %s" % (tg, vals)]
        if isinstance(st, CallS):
            return [ind + self.expr(st.call)]
        if isinstance(st, TempDef):
            return [ind + "local t%s = table.pack(%s)" % (st.t, self.expr(st.call))]
        if isinstance(st, SetListS):
            # tbl[start], tbl[start+1], ... = values (the values are evaluated once)
            if st.values.tail is None:
                tg = ", ".join("%s[%d]" % (self.prefix(st.tbl), st.start + k) for k in range(len(st.values.items)))
                return [ind + "%s = %s" % (tg, self.multi(st.values, trunc=False))] if tg else []
            return [ind + "do", ind + "\tlocal values = table.pack(%s)" % self.multi(st.values),
                    ind + "\ttable.move(values, 1, values.n, %d, %s)" % (st.start, self.expr(st.tbl)), ind + "end"]
        if isinstance(st, LocalS):
            if st.values is None:
                return [ind + "local " + ", ".join(st.names)]
            return [ind + "local %s = %s" % (", ".join(st.names), self.multi(st.values))]
        if isinstance(st, CommentS):
            return [ind + "-- " + st.text] if st.text else []
        if isinstance(st, (CloseS, ForPrepS)):
            return []
        if type(st).__name__ == "DoBlock":
            return [ind + "do"] + self.block(st.body, ind + "	") + [ind + "end"]
        if isinstance(st, ST.SIf):
            return self.if_stmt(st, ind)
        if isinstance(st, ST.SLoop):
            return self.loop(st, ind)
        if isinstance(st, ST.SBreak):
            return [ind + "break"]
        if isinstance(st, ST.SContinue):
            return [ind + "continue"]
        if isinstance(st, ST.SReturn):
            if st.values is None or (not st.values.items and st.values.tail is None):
                return [ind + "return"]
            return [ind + "return " + self.multi(st.values)]
        if isinstance(st, ST.SCrash):
            return [ind + "LPH_CRASH()"]
        if isinstance(st, ST.SError):
            return [ind + "error(\"devirt: %s\")" % st.msg.replace("\\", "\\\\").replace("\"", "'")]
        if isinstance(st, ST.SGotoState):
            # a jump the structurer could not express (e.g. a two-level break):
            # fail loudly instead of silently running on
            return [ind + "error(\"devirt: unstructured jump to block_%s\") -- goto block_%s" % (st.target, st.target)]
        return [ind + "-- ?? %s" % type(st).__name__]

    def lvalue(self, t):
        if isinstance(t, Index):
            return self.expr(t)
        return self.expr(t)

    def if_stmt(self, st, ind):
        out = [ind + "if %s then" % self.expr(st.cond)]
        out += self.block(st.then, ind + "\t")
        els = st.els
        while len(els) == 1 and isinstance(els[0], ST.SIf):
            e = els[0]
            out.append(ind + "elseif %s then" % self.expr(e.cond))
            out += self.block(e.then, ind + "\t")
            els = e.els
        if els:
            out.append(ind + "else")
            out += self.block(els, ind + "\t")
        out.append(ind + "end")
        return out

    def loop(self, st, ind):
        if st.kind == "for":
            v, (a, b, c) = st.forinfo
            head = "for %s = %s, %s" % (self.reg(v), self.expr(a), self.expr(b))
            if not (isinstance(c, Const) and c.v == 1):
                head += ", " + self.expr(c)
            return [ind + head + " do"] + self.block(st.body, ind + "\t") + [ind + "end"]
        if st.kind == "forin":
            vs, it = st.forinfo
            return [ind + "for %s in %s do" % (", ".join(self.reg(v) for v in vs),
                                               ", ".join(self.expr(x) for x in it))] + \
                self.block(st.body, ind + "\t") + [ind + "end"]
        if st.kind == "whilecond":
            return [ind + "while %s do" % self.expr(st.cond)] + self.block(st.body, ind + "\t") + [ind + "end"]
        if st.kind == "repeat":
            return [ind + "repeat"] + self.block(st.body, ind + "\t") + [ind + "until %s" % self.expr(st.cond)]
        return [ind + "while true do"] + self.block(st.body, ind + "\t") + [ind + "end"]


def _utf8_at(b, i):
    """The character of a valid UTF-8 sequence starting at b[i] (multi-byte only), else None."""
    c = b[i]
    n = 2 if 0xC2 <= c <= 0xDF else 3 if 0xE0 <= c <= 0xEF else 4 if 0xF0 <= c <= 0xF4 else 0
    if not n:
        return None
    try:
        return bytes(b[i:i + n]).decode("utf-8")    # rejects overlongs, surrogates, short tails
    except UnicodeDecodeError:
        return None


def _visible(ch, prev, nxt):
    """Printable as a literal: no controls, format chars (except a ZWJ inside
    an emoji sequence: prev/next are non-ASCII), separators other than " ",
    unassigned or private use."""
    if ch == "\u200d":
        return prev and nxt
    return unicodedata.category(ch)[0] not in "CZ"


# newline inside a long string: a private-use code point (quote never writes
# one literally), so re-indenting nested function lines can't reach the
# string's content; backend.polish turns it back into "\n"
LONG_NL = "\ue000"


def long_string(b):
    """[==[...]==] for multi-line text (embedded source, JSON, ASCII art), else None."""
    if b.count(b"\n") < 2 or len(b) < 60 or b"\r" in b:
        return None
    try:
        s = bytes(b).decode("utf-8")
    except UnicodeDecodeError:
        return None
    for i, ch in enumerate(s):
        if ch in "\n\t" or " " <= ch < "\x7f":
            continue
        if ch < "\x80" or not _visible(ch, i > 0 and s[i - 1] >= "\x80",
                                        i + 1 < len(s) and s[i + 1] >= "\x80"):
            return None
    n = 0
    while True:
        close = "]" + "=" * n + "]"
        if (s + close).find(close) == len(s):
            break
        n += 1
    # a newline right after the opening bracket is skipped: keep a leading one
    body = ("\n" + s if s.startswith("\n") else s).replace("\n", LONG_NL)
    return "[" + "=" * n + "[" + body + close


def quote(b):
    ls = long_string(b)
    if ls is not None:
        return ls
    out = ['"']
    i = 0
    while i < len(b):
        c = b[i]
        if c >= 0x80:
            ch = _utf8_at(b, i)
            if ch is not None:
                n = len(ch.encode("utf-8"))
                out.append(ch if _visible(ch, i > 0 and b[i - 1] >= 0x80, i + n < len(b) and b[i + n] >= 0x80)
                           else "\\u{%X}" % ord(ch))
                i += n
                continue
        if c == 34:
            out.append('\\"')
        elif c == 92:
            out.append("\\\\")
        elif c == 10:
            out.append("\\n")
        elif c == 13:
            out.append("\\r")
        elif c == 9:
            out.append("\\t")
        elif 32 <= c < 127:
            out.append(chr(c))
        elif i + 1 < len(b) and 48 <= b[i + 1] <= 57:
            out.append("\\%03d" % c)    # "\2" then "69" would read as "\269"
        else:
            out.append("\\%d" % c)
        i += 1
    out.append('"')
    return "".join(out)
