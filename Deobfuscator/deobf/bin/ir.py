"""
Shared lifter IR: what a devirtualizer front end produces per instruction
and what the back end (backend.py -> structure.py, loops.py, codegen.py,
variables.py, idioms.py) consumes. Expressions are luasym's (Const, Reg,
Global, Index, Bin, Un, ClosureExpr, ...); statements and outcomes are here.

The back end gets the IR as a module parameter `D` (D.Assign, D.CallStmt,
D.fmt_expr, ...): pass this module, or a front-end module that re-exports it.
"""
import luasym as S
from luasym import (LTable, Expr, Const, Reg, Pseudo, Global, Upval, Index, Bin, Un, IfExp, TempVal,  # noqa: F401
                    Vararg, ClosureExpr, Multi, TempTail, VarargTail, SymList, TailCount, RegFile, UpContainer)


class IRStmt:
    pass


class Assign(IRStmt):
    def __init__(self, target, value):
        self.target, self.value = target, value


class CallStmt(IRStmt):
    """temp t := fn(args...) (all results)."""

    def __init__(self, t, fn, args):
        self.t, self.fn, self.args = t, fn, args


class SetList(IRStmt):
    """tbl[start], tbl[start+1], ... = values (a table constructor's multret tail)."""

    def __init__(self, tbl, start, values):
        self.tbl, self.start, self.values = tbl, start, values


class GenIter(Expr):
    """State of a generic for loop (coroutine-driven in Luraph)."""

    def __init__(self, args):
        self.args = args


class Outcome:
    pass


class Next(Outcome):
    def __init__(self, state):
        self.state = state


class Ret(Outcome):
    def __init__(self, values):
        self.values = values


class Crash(Outcome):
    """LPH_CRASH(): the path never continues."""


class Node:
    """IR tree of one instruction: stmts, then either a branch or an outcome."""

    def __init__(self, stmts, cond=None, then=None, els=None, outcome=None):
        self.stmts, self.cond, self.then, self.els, self.outcome = stmts, cond, then, els, outcome


class ForPrep(IRStmt):
    """Evaluation of a for header's expressions (loops.LoopExprs), before the loop."""

    def __init__(self, exprs):
        self.exprs = exprs


class Close(IRStmt):
    def __init__(self, reg):
        self.reg = reg


class Opaque(Expr):
    """An engine value (datatype/proxy) constant; src = how the trace writes it."""

    def __init__(self, kind, src=""):
        self.kind, self.src = kind, src


class Vec(Expr):
    """A vector constant (Luau folds Vector3.new(constants) into one)."""

    def __init__(self, xyz):
        self.xyz = xyz


class Missing(Expr):
    """A lazily decoded constant that was not decoded yet (requested)."""

    def __init__(self, slot):
        self.slot = slot


def fmt_expr(e):
    if e is None:
        return "nil"
    if isinstance(e, Const):
        return fmt_const(e.v)
    if isinstance(e, Reg):
        return "r%d" % e.n
    if isinstance(e, Pseudo):
        return "%s_%d" % (e.name, e.depth)
    if isinstance(e, Global):
        return e.name
    if isinstance(e, Upval):
        return "up%d" % e.idx
    if isinstance(e, Index):
        return "%s[%s]" % (fmt_expr(e.obj), fmt_expr(e.key))
    if isinstance(e, Bin):
        return "(%s %s %s)" % (fmt_expr(e.a), e.op, fmt_expr(e.b))
    if isinstance(e, Un):
        return "(%s %s)" % (e.op, fmt_expr(e.a))
    if isinstance(e, IfExp):
        return "(if %s then %s else %s)" % (fmt_expr(e.c), fmt_expr(e.a), fmt_expr(e.b))
    if isinstance(e, TempVal):
        return "T%s[%d]" % (e.t, e.i)
    if isinstance(e, Vararg):
        return "vararg[%d]" % e.i
    if isinstance(e, TailCount):
        return "#(%s)" % fmt_tail(e.tail)
    if isinstance(e, ClosureExpr):
        return "closure(%r, ups=%s)" % (e.proto, [fmt_any(u) for u in e.upvals])
    if isinstance(e, GenIter):
        return "geniter(%s)" % fmt_multi(e.args)
    if isinstance(e, S.NewTable):
        return "{}"
    if isinstance(e, Missing):
        return "MISSING[%s]" % e.slot
    if isinstance(e, Opaque):
        return e.src or ("<%s>" % e.kind)
    if isinstance(e, Vec):
        return "vector(%s)" % ", ".join(S.fmt_num(x) for x in e.xyz)
    if isinstance(e, SymList):
        return "pack(%s)" % fmt_multi(Multi(e.items, e.tail))
    return repr(e)


def fmt_any(v):
    if isinstance(v, (Expr, SymList)) or v is None:
        return fmt_expr(v)
    if isinstance(v, LTable):
        return "{%s}" % ", ".join("%r=%s" % (k, fmt_any(x)) for k, x in v.h.items())
    if isinstance(v, RegFile):
        return "REGS"
    if isinstance(v, UpContainer):
        return "UPC%d" % v.idx
    return fmt_const(v) if isinstance(v, (bool, int, float, bytes)) else repr(v)


def fmt_tail(t):
    if isinstance(t, TempTail):
        return "T%s[%d...]" % (t.t, t.start)
    if isinstance(t, VarargTail):
        return "vararg[%d...]" % t.start
    return repr(t)


def fmt_multi(m):
    parts = [fmt_any(x) for x in m.items]
    if m.tail is not None:
        parts.append(fmt_tail(m.tail))
    return ", ".join(parts)


def fmt_const(v):
    if v is None:
        return "nil"
    if v is True:
        return "true"
    if v is False:
        return "false"
    if isinstance(v, bytes):
        return '"%s"' % "".join(chr(c) if 32 <= c < 127 and c not in (34, 92) else "\%d" % c for c in v)
    if isinstance(v, (int, float)):
        return S.fmt_num(v)
    return repr(v)


def fmt_stmt(s):
    if isinstance(s, SetList):
        return "%s[%d...] = %s" % (fmt_expr(s.tbl), s.start, fmt_multi(s.values))
    if isinstance(s, Assign):
        return "%s = %s" % (fmt_expr(s.target), fmt_expr(s.value))
    if isinstance(s, CallStmt):
        return "T%s = %s(%s)" % (s.t, fmt_expr(s.fn), fmt_multi(s.args))
    return repr(s)


def fmt_node(n, ind=""):
    out = [ind + fmt_stmt(s) for s in n.stmts]
    if n.cond is not None:
        out.append(ind + "if %s then" % fmt_expr(n.cond))
        if n.then:
            out += fmt_node(n.then, ind + "  ")
        out.append(ind + "else")
        if n.els:
            out += fmt_node(n.els, ind + "  ")
        out.append(ind + "end")
    elif isinstance(n.outcome, Next):
        s = n.outcome.state
        out.append(ind + "-> %s:%s" % (s.mode, s.pc))
    elif isinstance(n.outcome, Ret):
        out.append(ind + "return " + fmt_multi(n.outcome.values))
    elif isinstance(n.outcome, Crash):
        out.append(ind + "LPH_CRASH()")
    return out
