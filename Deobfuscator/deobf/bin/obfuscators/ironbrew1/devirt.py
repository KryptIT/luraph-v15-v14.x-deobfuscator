"""
ironbrew1 devirtualizer: lifts the VM functions captured by capture.luau
(*.ibdump.json) back into Luau with real control flow. The IR and the back
end are shared (ir.py, backend.py); Luraph's devirt.py is the model.

    python -m obfuscators.ironbrew1.devirt <src> <dump.json> [--raw N | --out FILE]   (from deobf/)

How it works (no opcode table: handlers are randomized per build):
  * capture.luau records, for every proto, the locals visible where the
    closure maker returns the interpreter (decoded instruction arrays,
    constants, field keys, helpers), keyed by declaration location.
  * For every instruction, luasym runs one iteration of the interpreter's
    `while true do` loop with those values concrete and the registers
    symbolic. The interpreter's own locals (pc, argument stack pointer,
    open-upvalue lists, ...) are carried between instructions as the walk
    state; a branch on a symbolic value forks the run.
  * VM mechanics get symbolic stand-ins: the register table (RegFile), the
    argument stack (values copied into stack registers), multiple results
    (a count `Lin` = known + #tail and one `Spread` slot holding the tail),
    boxed captured locals (`{v}` tables: BoxRef), upvalue lists (UpList).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))     # deobf/: the shared modules
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

import backend  # noqa: E402
import ir  # noqa: E402
import luasym as S  # noqa: E402
from luasym import (LTable, Builtin, LuaFunc, Buf, Unsupported, Expr, Const, Reg, Pseudo, Global,  # noqa: E402
                    Upval, Index, Bin, Un, TempVal, Vararg, ClosureExpr, Multi, TempTail,
                    VarargTail, SymList, TailCount, RegFile, EnvTable, Scope,
                    BreakSig, ReturnSig, ContinueSig, is_sym)
from ir import (Assign, CallStmt, SetList, GenIter, Next, Ret, Node, Close, Opaque, Vec,  # noqa: E402
                fmt_expr, fmt_any, fmt_multi)
from obfuscators.ironbrew1 import instrument, forloops  # noqa: E402

STACK_BASE = 1000000      # argument stack slot k -> Reg(STACK_BASE * n + k) (n: which stack table)
OVL_BASE = 800000         # a symbolic value stored into a VM table (T[id] = x) -> Reg(OVL_BASE + n)
LOC_BASE = 900000         # interpreter locals holding a symbolic value -> Reg(LOC_BASE + i)
HLOC_BASE = 700000        # handler locals holding a mutable symbolic value -> Reg(HLOC_BASE + i)
LV_BASE = 600000          # handler locals of a fused loop (a loop inside one handler) -> Reg(LV_BASE + i)
BOX_BASE = 500000         # captured locals (boxes) -> Reg(BOX_BASE + i), one per box creation site
MAX_STATES = 60000        # instruction states per function
MAX_RESTARTS = 64


# --------------------------------------------------------------------------
# values

class FuncRef:
    """A Lua function of the VM source (a helper registered by __IBF)."""
    __slots__ = ("loc", "node")

    def __init__(self, loc, node):
        self.loc, self.node = loc, node

    def __repr__(self):
        return "Fn@%s" % self.loc


ENV = EnvTable()


class Stored:
    """A value stored into a table built here: its IR form (a register read
    at the store) and its value then, if known (reads fold to it)."""
    __slots__ = ("expr", "const")

    def __init__(self, expr, const):
        self.expr, self.const = expr, const

    def __repr__(self):
        return "Stored(%r)" % (self.const,)


def _unstore(v):
    return v.const if isinstance(v, Stored) else v


class InsProxy:
    """P[pc] of an instruction proxy table (capture.luau `proxies`): its
    fields are instruction pc's operands, so `P[pc][k] = x` rewrites an
    operand (the obfuscator stores return addresses into a shared jump)"""
    __slots__ = ("fields", "pc")

    def __init__(self, fields, pc):
        self.fields, self.pc = fields, pc

    def __repr__(self):
        return "InsProxy(%r)" % (self.pc,)


class BoxTable(LTable):
    """`{R[a]}` in a handler: a box for a captured local (reg_write)"""


class KnownGlobal(Global):
    """A global the VM cached (its registry held the value at the end of the
    run): known to be truthy."""


class Lin(Expr):
    """A count / index c + #tail (multiple results of unknown length)."""

    def __init__(self, c, tail):
        self.c, self.tail = c, tail

    def __repr__(self):
        return "Lin(%d,%s)" % (self.c, ir.fmt_tail(self.tail))

    def as_expr(self):
        tc = TailCount(self.tail)
        return tc if self.c == 0 else Bin("Add", tc, Const(self.c))


class SpreadIdx(Expr):
    """The loop variable of a loop up to a Lin bound, in its one symbolic
    iteration: the indices `start` .. end (the tail part)."""

    def __init__(self, start):
        self.start = start

    def __repr__(self):
        return "SpreadIdx(%d)" % self.start


class Spread:
    """Values from here to the end (the tail of a multiple result), stored in
    one slot."""
    __slots__ = ("m",)

    def __init__(self, m):
        self.m = m

    def __repr__(self):
        return "Spread(%s)" % fmt_multi(self.m)


class BoxRef:
    """A box table `{v}` of a captured local: [1] is the variable `target`
    (Reg or Upval)."""
    __slots__ = ("target",)

    def __init__(self, target):
        self.target = target

    def __repr__(self):
        return "Box(%s)" % fmt_expr(self.target)


class MaybeBox:
    """A by-reference capture of parent register `reg` (the back end knows
    this class by name: variables.closure_regs)."""

    def __init__(self, reg):
        self.reg = reg

    def __repr__(self):
        return "box r%d" % self.reg


class UpList:
    """The upvalue list of the function being lifted: kinds[i] is "box" for a
    captured variable (hb[i][1] is the variable), else a plain value."""

    def __init__(self, kinds=None):
        self.kinds = kinds or {}

    def __repr__(self):
        return "UpList"


class VMClosure:
    """A function value the dump could not name: a closure the VM made (its
    runtime functions kept in VM tables). Calls of it are VM bookkeeping."""

    def __repr__(self):
        return "VMClosure"


VMCLOSURE = VMClosure()


class GenIterRef:
    """coroutine.wrap(function() for ... in f, s, c do yield(true, ...) end end)."""

    def __init__(self, args):
        self.args = args


def _hashlike(name):
    """the VM's run-once globals (`_9efad081ef4a9a8debc47add`)"""
    import re
    return re.fullmatch(rb"_[0-9a-f]{12,}", name) is not None


VMGLOBAL = LTable(tid="VMG")
NOFOLD = object()


class _Truthy:
    def __repr__(self):
        return "TRUTHY"


TRUTHY = _Truthy()  # fval: a value known to be truthy (a standard global), nothing more


class _Lost:
    """a register whose VM value did not survive a merge: fine to move or to
    park in a VM table (junk does both), an error where script code needs it"""

    def __init__(self, reg):
        self.reg = reg

    def __repr__(self):
        return "LOST(%s)" % self.reg

    def fail(self):
        raise Unsupported("register %s lost its VM value at a merge" % self.reg)


class _Taint:
    def __repr__(self):
        return "TAINT"


TAINT = _Taint()    # key marking a table built here that holds VM objects (no IR form)


class _TblId:
    def __repr__(self):
        return "TBLID"


TBLID = _TblId()    # key: which IR constructor made a table built here (dead-table removal)

# globals that exist in every Roblox script environment (a branch on one is decided)
STD_GLOBALS = frozenset("""assert collectgarbage error getfenv getmetatable ipairs load loadstring newproxy next
pairs pcall print rawequal rawget rawlen rawset require select setfenv setmetatable tonumber tostring type
typeof unpack xpcall bit32 coroutine debug math os string table utf8 buffer task vector game workspace
script Enum Instance Vector3 Vector2 CFrame Color3 UDim UDim2 BrickColor Ray Region3 TweenInfo
NumberRange NumberSequence ColorSequence Random DateTime tick time wait delay spawn warn shared _G
plugin elapsedTime settings UserSettings Rect Path2DControlPoint Font Axes Faces PhysicalProperties
Region3int16 Vector3int16 Vector2int16 NumberSequenceKeypoint ColorSequenceKeypoint PathWaypoint
RaycastParams OverlapParams SharedTable FloatCurveKey RotationCurveKey CatalogSearchParams
DockWidgetPluginGuiInfo Content gcinfo stats""".split())


def _copy_fresh(v, memo):
    """per-run copies of tables the VM code builds in scratch registers"""
    if not isinstance(v, LTable) or v.tid is not None:
        return v
    c = memo.get(id(v))
    if c is None:
        c = memo[id(v)] = LTable()
        c.h = {_copy_fresh(k, memo): _copy_fresh(x, memo) for k, x in v.h.items()}
    return c


def _multikey(m):
    """a pending multiple result in a state key: its shape, not which call
    made it (results are read right after their call; a key per call would
    keep loops from converging)"""
    t = m.tail
    return (len(m.items), None if t is None else "call" if isinstance(t, TempTail) else ir.fmt_tail(t))


def _keyval(v, open_=None):
    if v is None or isinstance(v, (bool, int, float, bytes, str)):
        return v
    if isinstance(v, Lin):
        return ("Lin", v.c, _multikey(Multi([], v.tail)))
    if isinstance(v, Expr):
        return "E:" + fmt_expr(v) if not isinstance(v, SpreadIdx) else repr(v)
    if isinstance(v, Stored):
        return "Stored(%s)" % (_keyval(v.const, open_),)
    if isinstance(v, Spread):
        return ("Spread", _multikey(v.m))
    if isinstance(v, (BoxRef, FuncRef, UpList)):
        return repr(v)
    if isinstance(v, LTable) and v.tid is None and not getattr(v, "fixed", False):
        # (tables built here can hold themselves: `t[k] = t`)
        open_ = open_ or []
        if any(x is v for x in open_):
            return "^%d" % next(i for i, x in enumerate(reversed(open_)) if x is v)
        open_.append(v)
        try:
            return "{%s}" % ",".join(sorted("%s=%s" % (_keyval(k, open_) if isinstance(k, LTable) else repr(k),
                                                       _keyval(x, open_)) for k, x in v.h.items()))
        finally:
            open_.pop()
    if isinstance(v, (LTable, RegFile, SymList, Multi, GenIterRef)):
        return "obj%d" % id(v)
    return repr(v)


# --------------------------------------------------------------------------
# the dump

class Dump:
    def __init__(self, d, funcs):
        self.raw = d
        self.funcs = funcs            # AST location -> function node
        self.strings = [bytes.fromhex(x) for x in d.get("strings", [])]
        raw = d["tables"]
        # tables whose metatable has __index = the script's environment: the
        # VM's globals table (setmetatable({}, {__index = getfenv()}))
        env_mt = set()
        for tid, t in raw.items():
            for k, v in t["e"]:
                if isinstance(k, dict) and k.get("s") == "5f5f696e646578" and isinstance(v, dict) and v.get("env"):
                    env_mt.add(int(tid))
        self.env_tids = {int(tid) for tid, t in raw.items()
                         if isinstance(t.get("mt"), dict) and t["mt"].get("t") in env_mt}
        self.tables = {int(tid): LTable(tid=int(tid)) for tid in raw}
        for tid, t in raw.items():
            lt = self.tables[int(tid)]
            for k, v in t["e"]:
                kk = self.val(k)
                if isinstance(kk, float) and kk == int(kk):
                    kk = int(kk)
                lt.h[kk] = self.val(v)
        self.env_vals = {}
        for tid in self.env_tids:
            for k, v in self.tables[tid].h.items():
                self.env_vals.setdefault(k, v)
        self.caps = []
        self.proxy_fields = {}      # id(proxy table) -> {field key: operand array}
        for c in d["caps"]:
            self.caps.append({"mk": c["mk"], "params": [self.val(x) for x in c["params"]],
                              "vars": {k: self.val(v) for k, v in c["vars"].items()}})
            for px in c.get("proxies", ()):
                P = self.val(px["t"])
                fields = {}
                for k, t in px["map"]:
                    k, t = self.val(k), self.val(t)
                    if isinstance(t, LTable):
                        fields[S.norm_key(k)] = t
                if isinstance(P, LTable) and fields:
                    self.proxy_fields[id(P)] = fields
        self.cap_of = {}
        for i, c in enumerate(self.caps):
            p = c["params"][0]
            if isinstance(p, LTable):
                self.cap_of.setdefault(id(p), i)

    def val(self, v):
        if v is None or isinstance(v, (bool, int, float)):
            return S.fix_int(v) if isinstance(v, float) else v
        if "t" in v:
            if v["t"] in self.env_tids:
                return ENV
            return self.tables[v["t"]]
        if "s" in v:
            return bytes.fromhex(v["s"])
        if "S" in v:
            return self.strings[v["S"] - 1]
        if "n" in v:
            return {"nan": float("nan"), "inf": float("inf"), "-inf": float("-inf")}[v["n"]]
        if "f" in v:
            return FuncRef(v["f"], self.funcs.get(v["f"]))
        if "c" in v:
            return VMCLOSURE if v["c"] == "?" else Builtin(v["c"])
        if "g" in v:
            return KnownGlobal(v["g"])
        if v.get("env"):
            return ENV
        if "v" in v:
            return Vec(tuple(v["v"]))
        if "b" in v:
            return Buf(bytes.fromhex(v["b"]))
        if "u" in v:
            return Opaque(v["u"], "nil --[[ %s ]]" % v["u"])
        raise ValueError(v)


# --------------------------------------------------------------------------
# source model

def ast_functions(root):
    out = {}
    for n in instrument.iter_nodes(root):
        if n.get("type") == "AstExprFunction":
            out[n["location"]] = n
    return out


class VMModel:
    """One closure maker and its interpreter function."""

    def __init__(self, maker, interp):
        self.maker, self.interp = maker, interp
        self.loop = instrument.dispatch_loop(interp)
        body = interp["body"]["body"]
        i = next(k for k, s in enumerate(body) if s is self.loop)
        self.prologue = body[:i]
        self.after = body[i + 1:]
        self.loop_body = self.loop["body"]["body"]
        first = self.loop_body[0]["values"][0]
        if first["index"]["type"] != "AstExprLocal":
            raise Unsupported("dispatch loop does not index by a local pc")
        self.pc_decl = first["index"]["local"]["location"]
        self.params = [a["location"] for a in maker["args"]]
        # interpreter-level locals: declared in the prologue
        self.ilocals = []
        for s in self.prologue:
            if s["type"] == "AstStatLocal":
                self.ilocals += [v["location"] for v in s["vars"]]
            elif s["type"] == "AstStatLocalFunction":
                self.ilocals.append(s["name"]["location"])
        self.iloc_index = {k: i for i, k in enumerate(self.ilocals)}
        # results helper `local function f(t, ...) local n = select("#", ...) ...`
        self.results_fns = set()
        self.results_top = {}   # id(results helper) -> interpreter local it sets to the count
        for s in self.prologue:
            if s["type"] == "AstStatLocalFunction" and _is_results_fn(s["func"]):
                self.results_fns.add(id(s["func"]))
                top = _results_top(s["func"])
                if top is not None:
                    self.results_top[id(s["func"])] = top


def _is_results_fn(fn):
    if not fn.get("vararg") or len(fn["args"]) != 1:
        return False
    b = fn["body"]["body"]
    if not b or b[0]["type"] != "AstStatLocal" or len(b[0]["values"]) != 1:
        return False
    v = b[0]["values"][0]
    if v["type"] != "AstExprCall" or len(v["args"]) != 2:
        return False
    a0, a1 = v["args"]
    return a0["type"] == "AstExprConstantString" and a0["value"] == "#" and a1["type"] == "AstExprVarargs"


def _results_top(fn):
    """the outer local the results helper sets to the count (`df = n`)"""
    b = fn["body"]["body"]
    n = b[0]["vars"][0]["location"]
    for st in b:
        if st["type"] == "AstStatAssign" and len(st["vars"]) == 1 and st["vars"][0]["type"] == "AstExprLocal" \
                and len(st["values"]) == 1 and st["values"][0]["type"] == "AstExprLocal" \
                and st["values"][0]["local"]["location"] == n:
            return st["vars"][0]["local"]["location"]
    return None


def _is_geniter_fn(fn):
    """function() for a, b, ... in f, s, c do yield(true, a, b, ...) end end -> True"""
    if not isinstance(fn, dict) or fn.get("type") != "AstExprFunction" or fn["args"]:
        return False
    b = fn["body"]["body"]
    if len(b) != 1 or b[0]["type"] != "AstStatForIn" or len(b[0]["values"]) != 3:
        return False
    inner = b[0]["body"]["body"]
    return len(inner) == 1 and inner[0]["type"] == "AstStatExpr"


# --------------------------------------------------------------------------
# the symbolic interpreter, with the VM-mechanics rules

class IBInterp(S.Interp):
    def getvar(self, scope, local):
        key = local["location"]
        s = scope.lookup(key)
        if s is None:
            raise Unsupported("unbound local %s@%s" % (local["name"], key))
        if s is self.L.iscope:
            self.L.note_read(key)
        return s.vars[key]

    def setvar(self, scope, local, v):
        key = local["location"]
        s = scope.lookup(key)
        if s is None:
            raise Unsupported("assign to unbound local %s" % local["name"])
        if key in self.L.lv_active and s is not self.L.iscope:
            r = Reg(LV_BASE + self.L.lv_active[key])
            self.L.emit(Assign(r, self.L.value_of(v)))
            s.vars[key] = r
            return
        if s is self.L.iscope:
            self.L.note_write(key)
            v = self.L.local_value(key, v)
        elif s is not self.L.cscope:
            v = self.L.hold(key, v, s)
        s.vars[key] = v

    def table_ctor(self, node, scope):
        items = node["items"]
        if len(items) == 1 and items[0]["kind"] == "item" and items[0]["value"]["type"] == "AstExprIndexExpr":
            ix = items[0]["value"]
            if isinstance(self.eval(ix["expr"], scope), RegFile):
                # `{R[a]}`: a box for a captured local, also while it still
                # holds nil (h[1] = None marks the slot)
                tb = BoxTable()
                v = self.eval(ix, scope)
                tb.h[1] = v.first() if isinstance(v, Multi) else v
                return tb
        return S.Interp.table_ctor(self, node, scope)

    def binop(self, op, a, b):
        for x in (a, b):
            if isinstance(x, _Lost):
                x.fail()
        return S.Interp.binop(self, op, a, b)

    def eval(self, node, scope):
        if node["type"] == "AstExprBinary" and node["op"] == "And":
            e = _truthy_test(node)
            if e is not None:
                # `(x ~= nil) and (x ~= false)`: the VM's test of x's truth
                v = self.eval(e, scope)
                if isinstance(v, Multi):
                    v = v.first()
                if isinstance(v, Expr) and not isinstance(v, (Lin, SpreadIdx)):
                    return Un("Not", Un("Not", v))
                if isinstance(v, _Lost):
                    v.fail()
                return v is not None and v is not False
        return S.Interp.eval(self, node, scope)

    def unop(self, op, a):
        if isinstance(a, _Lost):
            a.fail()
        if op == "Len" and isinstance(a, LTable) and a.tid is None and not isinstance(a, BoxTable) \
                and id(a) not in self.L.results:
            # `#t` of a script table in a register stays `#t` (its length is
            # known here, but the script reads it; the obfuscator's scratch
            # tables have no register and fold)
            h = self.L.home_of(a)
            if h is not None:
                self.L.prog.used_table(a)
                return Un("Len", Reg(h))
        return S.Interp.unop(self, op, a)

    loop_sub = None     # the fused loop whose head this run starts at (its AST location)

    def exec_stmt(self, st, scope):
        t = st["type"]
        if t in ("AstStatWhile", "AstStatForIn", "AstStatFor") and not self.L.in_prologue:
            if self.loop_sub is not None and self.loop_sub == st["location"]:
                return self.loop_head(st, scope)
            kind = self.fused_loop(st, scope)
            if kind is not None:
                return self.loop_enter(st, scope, kind)
        if st["type"] == "AstStatLocal" and not self.L.in_prologue:
            self.steps += 1
            vals = self.eval_list(st["values"], scope, len(st["vars"]))
            for v, x in zip(st["vars"], vals):
                scope.vars[v["location"]] = self.L.hold(v["location"], x, scope)
            return
        if st["type"] != "AstStatFor":
            return S.Interp.exec_stmt(self, st, scope)
        self.steps += 1
        a = self.eval(st["from"], scope)
        b = self.eval(st["to"], scope)
        c = self.eval(st["step"], scope) if st.get("step") else 1
        if isinstance(b, Lin) or isinstance(a, Lin):
            return self.lin_for(st, scope, a, b, c)
        if is_sym(a) or is_sym(b) or is_sym(c):
            raise Unsupported("numeric for with symbolic bounds")
        i = a
        n = 0
        while (c > 0 and i <= b) or (c <= 0 and i >= b):
            n += 1
            if n > 1000000:
                raise Unsupported("for loop limit")
            inner = Scope(scope)
            inner.vars[st["var"]["location"]] = i
            try:
                self.exec_block(st["body"]["body"], inner)
            except BreakSig:
                break
            except ContinueSig:
                pass
            i = S.fix_int(i + c)

    # ---- fused loops: a loop inside one handler that runs on script values
    # (`for k, v in R[a], R[a+1], R[a+2] do R[a+3], R[a+4] = k, v; <op> end`)
    # is a loop of the output, not something to run here. The run ends at
    # the loop (LoopSig); the loop head is a state of its own (State.sub),
    # whose runs replay the handler up to the loop with the output dropped.
    # Handler locals holding script values live in LV registers meanwhile.

    def fused_loop(self, st, scope):
        """the kind of loop st is, if it runs on script values, else None"""
        def script_value(x):
            return isinstance(x, Expr) and not isinstance(x, (Lin, SpreadIdx, Const))
        t = st["type"]
        if t == "AstStatWhile":
            return "while" if script_value(self.eval(st["condition"], scope)) else None
        if t == "AstStatFor":
            vals = [self.eval(st["from"], scope), self.eval(st["to"], scope)]
            if st.get("step"):
                vals.append(self.eval(st["step"], scope))
            if any(isinstance(x, (Lin, SpreadIdx)) for x in vals):
                return None
            return "for" if any(script_value(x) for x in vals) else None
        vals = self.eval_list(st["values"], scope, 3)
        return "forin" if script_value(vals[0]) else None

    def _loop_locals(self, scope):
        """(scope, key, value) of the handler locals visible here holding script values"""
        out = []
        s = scope
        while s is not None and s is not self.L.iscope and s is not self.L.cscope:
            for k, v in s.vars.items():
                if k != "..." and isinstance(v, Expr) and not isinstance(v, (Lin, SpreadIdx, Const, ClosureExpr)):
                    out.append((s, k, v))
            s = s.parent
        return out

    def _lv(self, key):
        return self.L.lvreg.setdefault(key, len(self.L.lvreg) + 1)

    def loop_enter(self, st, scope, kind):
        L = self.L
        for s, k, v in self._loop_locals(scope):
            L.emit(Assign(Reg(LV_BASE + self._lv(k)), L.value_of(v)))
        loc = st["location"]
        if kind == "forin":
            vals = self.eval_list(st["values"], scope, 3)
            L.emit(Assign(Pseudo("ga", LV_BASE + self._lv(("forin", loc))),
                          GenIter(Multi([None] + [L.value_of(x) for x in vals]))))
        elif kind == "for":
            step = self.eval(st["step"], scope) if st.get("step") else 1
            for part, x in (("i", self.eval(st["from"], scope)), ("lim", self.eval(st["to"], scope)),
                            ("step", step)):
                L.emit(Assign(Reg(LV_BASE + self._lv(("for", loc, part))), L.value_of(x)))
        raise LoopSig(loc)

    def loop_head(self, st, scope):
        L = self.L
        if self.dlog:
            raise Unsupported("a decision on script values before a fused loop")
        del L.out[:]        # (the replayed part ran at the loop's entry)
        for s, k, v in self._loop_locals(scope):
            n = self._lv(k)
            s.vars[k] = Reg(LV_BASE + n)
            L.lv_active[k] = n
        loc = st["location"]
        t = st["type"]
        inner = Scope(scope)
        if t == "AstStatForIn":
            tmp = L.new_temp()
            L.emit(CallStmt(tmp, Pseudo("ga", LV_BASE + self._lv(("forin", loc))), Multi([])))
            if not self.cond_true(TempVal(tmp, 1)):
                return
            for i, v in enumerate(st["vars"]):
                inner.vars[v["location"]] = TempVal(tmp, i + 2)
        elif t == "AstStatFor":
            i, lim, step = (Reg(LV_BASE + self._lv(("for", loc, part))) for part in ("i", "lim", "step"))
            sv = L.fval(step)
            if not isinstance(sv, (int, float)) or isinstance(sv, bool) or sv == 0:
                raise Unsupported("fused numeric loop with an unknown step")
            if not self.cond_true(Bin("CompareLe" if sv > 0 else "CompareGe", i, lim)):
                return
            inner.vars[st["var"]["location"]] = i
        else:
            if not self.cond_true(self.eval(st["condition"], scope)):
                return
        try:
            self.exec_block(st["body"]["body"], inner)
        except BreakSig:
            return
        except ContinueSig:
            pass
        if t == "AstStatFor":
            L.emit(Assign(i, Bin("Add", i, step)))
        raise LoopSig(loc)

    def lin_for(self, st, scope, a, b, c):
        """for i = a, c0 + #tail: the known iterations a .. c0, then one with
        i = SpreadIdx(c0 + 1) (the whole tail in one slot)."""
        if c != 1 or not isinstance(a, int) or not isinstance(b, Lin):
            raise Unsupported("loop over a multiple result with step %r from %r" % (c, a))
        i = a
        while True:
            inner = Scope(scope)
            if i <= b.c:
                inner.vars[st["var"]["location"]] = i
            else:
                inner.vars[st["var"]["location"]] = SpreadIdx(i)
            try:
                self.exec_block(st["body"]["body"], inner)
            except BreakSig:
                return
            except ContinueSig:
                pass
            if i > b.c:
                return
            i += 1


# --------------------------------------------------------------------------

CHECK_MODULUS = 2147483629    # ironbrew1's environment check folds its probes modulo this prime


class CheckResult:
    """Result i of `pcall(<ironbrew1's environment check>)`: the check the
    obfuscator puts at the start of the script. It passes in a real
    environment (pcall -> true, the check -> 0 and its constant), and a
    flag set from it decides whether the rest of the script gets corrupted
    (`handlers[flag and false or "PUSH"] = ...`): the results are taken as
    passing and the call is dropped."""
    __slots__ = ("i",)

    def __init__(self, i):
        self.i = i

    def __repr__(self):
        return "CheckResult(%d)" % self.i

    def __eq__(self, o):
        return isinstance(o, CheckResult) and o.i == self.i

    def __hash__(self):
        return hash(("check", self.i))


class LoopSig(Exception):
    """a run ends at a fused loop's head (entering it or going round again)"""

    def __init__(self, sub):
        self.sub = sub


def _mutable_refs(e, limit=40):
    """what an IR expression reads that a statement can change (None: the
    expression has more than `limit` nodes)"""
    out = set()
    st = [e]
    n = 0
    while st:
        x = st.pop()
        n += 1
        if n > limit:
            return None
        if isinstance(x, Reg):
            out.add(("r", x.n))
        elif isinstance(x, Upval):
            out.add(("u", x.idx))
        elif type(x) is Global:
            out.add(("g", x.name))
        elif isinstance(x, Index):
            out.add("idx")
            st += [x.obj, x.key]
        elif isinstance(x, Bin):
            st += [x.a, x.b]
        elif isinstance(x, Un):
            st.append(x.a)
        elif isinstance(x, S.IfExp):
            st += [x.c, x.a, x.b]
    return out


def _regs_in(x):
    """HLOC register numbers an IR statement / expression / value list reads"""
    out = set()
    st = [x]
    seen = 0
    while st:
        y = st.pop()
        seen += 1
        if seen > 20000:
            break
        if isinstance(y, Reg):
            if HLOC_BASE <= y.n < OVL_BASE:
                out.add(y.n)
        elif isinstance(y, (list, tuple)):
            st += list(y)
        elif isinstance(y, Multi):
            st += list(y.items)
        elif isinstance(y, Assign):
            st.append(y.value)
            if not isinstance(y.target, Reg):
                st.append(y.target)
        elif hasattr(y, "__dict__") and not isinstance(y, (type, LTable)):
            st += [v for v in vars(y).values() if hasattr(v, "__dict__") or isinstance(v, (list, tuple))]
    return out


_TRUTHY_TESTS = {}


def _ast_key(e):
    """an AST expression without its source locations (structural equality)"""
    if isinstance(e, dict):
        return tuple(sorted((k, _ast_key(v)) for k, v in e.items() if k != "location"))
    if isinstance(e, list):
        return tuple(_ast_key(x) for x in e)
    return e


def _truthy_test(node):
    """E of `(E ~= nil) and (E ~= false)` (either order), else None"""
    k = id(node)
    if k in _TRUTHY_TESTS:
        return _TRUTHY_TESTS[k][1]

    def strip(e):
        while e["type"] == "AstExprGroup":
            e = e["expr"]
        return e

    def side(e):
        e = strip(e)
        if e["type"] != "AstExprBinary" or e["op"] != "CompareNe":
            return None
        a, b = strip(e["left"]), strip(e["right"])
        for x, c in ((a, b), (b, a)):
            if c["type"] == "AstExprConstantNil":
                return x, None
            if c["type"] == "AstExprConstantBool" and c["value"] is False:
                return x, False
        return None
    out = None
    l, r = side(node["left"]), side(node["right"])
    if l is not None and r is not None and {l[1], r[1]} == {None, False} and _ast_key(l[0]) == _ast_key(r[0]):
        out = l[0]
    _TRUTHY_TESTS[k] = (node, out)
    return out


def _writes(st):
    if isinstance(st, Assign):
        t = st.target
        if isinstance(t, Reg):
            return {("r", t.n)}
        if isinstance(t, Upval):
            return {("u", t.idx)}
        if type(t) is Global:
            return {("g", t.name)}
        if isinstance(t, Index):
            return {"idx"}
        return set()
    if isinstance(st, CallStmt):
        # a call can change tables, globals and upvalues; registers only
        # through a closure's box, and a boxed register is read as its box
        return {"idx", "g*", "u*"}
    if isinstance(st, SetList):
        return {"idx"}
    return set()


class State:
    """The interpreter at an instruction boundary: pc, carried locals, the
    contents of its own tables (argument stack, open upvalues), boxed
    registers, the pending multiple result, generic-for iterators. Register
    facts (known values) travel separately (`facts`, merged at joins)."""
    __slots__ = ("pc", "vals", "tabs", "boxes", "top", "iters", "facts", "lost", "sub", "live", "_key")
    mode = 0

    def __init__(self, pc, vals, tabs, boxes, top, iters, facts, lost, sub=None, live=None):
        self.pc, self.vals, self.tabs, self.boxes, self.top, self.iters = pc, vals, tabs, boxes, top, iters
        self.facts, self.lost = facts, lost
        self.sub = sub          # a fused loop's head inside this instruction (its AST location), or None
        self.live = live        # pc -> carried locals live there (ProtoLifter.live), or None
        self._key = None

    def key(self, link=None):
        if self._key is None:
            # (a carried local that is dead here does not tell states apart)
            live = self.live.get(self.pc) if self.live is not None else None
            self._key = (0, self.pc,
                         tuple((k, _keyval(v)) for k, v in self.vals if live is None or k in live),
                         tuple((t, tuple(sorted(((repr(k), _keyval(v)) for k, v in h.items()
                                                 if live is None or ("tab", t, k) in live))))
                               for t, h in self.tabs),
                         tuple(sorted((r, _keyval(v)) for r, v in self.boxes.items())),
                         None if self.top is None or (live is not None and ("top",) not in live)
                         else (self.top[0], _multikey(self.top[1])),
                         tuple(sorted((r, _keyval(v)) for r, v in self.iters.items()
                                      if live is None or ("iter", r) in live)),
                         self.sub, _vm_memory(self.facts, live))
        return self._key


def _vm_memory(facts, live=None):
    """scalars the code parked in VM tables (`T[id][k] = 63`): part of the
    state, not merged facts. The obfuscator routes shared blocks by them
    (store a return address, jump to a block that reads it and branches).
    Only slots read later (live) count: junk stores never read would split
    states (a loop's first iteration peeled off)."""
    out = []
    for slot, v in facts.items():
        if isinstance(slot, tuple) and slot[0] == "ovl" and (live is None or slot in live):
            if isinstance(v, Stored):
                v = v.const
            if v is None or isinstance(v, (bool, int, float, bytes)):
                out.append((repr(slot), repr(v)))
    return tuple(sorted(out))


def _is_phantom(v):
    """values that exist only as facts (never as IR): VM objects"""
    return isinstance(v, (FuncRef, Builtin, VMClosure, UpList, InsProxy)) or (isinstance(v, LTable) and v.tid is not None)


def _same_fact(a, b):
    if a is b:
        return True
    if isinstance(a, CheckResult) or isinstance(b, CheckResult):
        return a == b
    if isinstance(a, InsProxy) or isinstance(b, InsProxy):
        return isinstance(a, InsProxy) and isinstance(b, InsProxy) and a.fields is b.fields and a.pc == b.pc
    if isinstance(a, LTable) and isinstance(b, LTable) and a.tid is None and b.tid is None:
        return _keyval(a) == _keyval(b)
    if type(a) is not type(b) or isinstance(a, (LTable, FuncRef, Builtin, UpList)):
        return isinstance(a, FuncRef) and isinstance(b, FuncRef) and a.loc == b.loc
    if isinstance(a, Stored):
        return _same_fact(a.expr, b.expr) and _same_fact(a.const, b.const)
    if isinstance(a, Expr):
        return fmt_expr(a) == fmt_expr(b)
    return S.lua_eq(a, b) and not (isinstance(a, float) and a != a)


def meet_facts(a, b, la, lb, nregs, prog=None):
    """facts true on both incoming paths; registers whose phantom value is
    dropped are `lost` (reading one later is an error); a table built here
    whose fact is dropped is used through its register from then on"""
    out = {}
    lost = set(la) | set(lb)
    for r in set(a) | set(b):
        if r in a and r in b and _same_fact(a[r], b[r]):
            out[r] = a[r]
            continue
        if r in a and r in b:
            # a parked value: the same register on both sides, its value
            # known on one only
            ea = a[r].expr if isinstance(a[r], Stored) else a[r]
            eb = b[r].expr if isinstance(b[r], Stored) else b[r]
            if isinstance(ea, Reg) and isinstance(eb, Reg) and ea.n == eb.n:
                out[r] = ea
                continue
        for x in (a.get(r), b.get(r)):
            if prog is not None and isinstance(x, LTable) and x.tid is None:
                prog.used_table(x)
            if r in a or r in b:
                if _is_phantom(x) or x is VMGLOBAL or not isinstance(r, int) or \
                        (isinstance(x, LTable) and nregs is not None and r > nregs):
                    lost.add(r)
    return out, frozenset(lost - set(out))


class ProtoLifter:
    """Steps the instructions of one captured proto (luasym hooks)."""

    def __init__(self, prog, cap_index, uplist):
        self.prog = prog
        self.dump = prog.dump
        self.cap = prog.dump.caps[cap_index]
        self.cap_index = cap_index
        self.vm = prog.vms[self.cap["mk"]]
        self.special = {}
        self.out = []
        self.tcount = 0
        self.temp_prefix = ""
        self.children = []
        self.captured_regs = set()
        self.uplist = uplist
        # the maker's scope: every captured local
        cs = Scope()
        for k, v in self.cap["vars"].items():
            cs.vars[k] = v
        vm = self.vm
        if len(vm.params) >= 2:
            cs.vars[vm.params[1]] = uplist
        self.cscope = cs
        self.iscope = None
        self.in_prologue = False
        # interpreter locals read before written in some step (shared by all
        # functions of one VM: the handlers are the same)
        self.carry = prog.carry_of.setdefault(self.cap["mk"], set())
        self.new_carry = False
        self.tab_carry = prog.tab_carry_of.setdefault(self.cap["mk"], set())  # prologue tables whose slots a step reads before writing
        self.stack_tabs = {}        # id(prologue table) -> stack number (symbolic values stored there)
        self.results = {}           # id(table) -> SymList filled by the results helper (this step only)
        self.boxes = {}
        self.top = None
        self.iters = {}
        self.facts = {}             # register -> known value (SCCP facts of the current run)
        self.ovl_slots = {}         # (VM table, key) -> register number of a parked symbolic value
        self.home = {}              # id(table built here) -> register holding it (its IR name)
        self.lost = frozenset()     # registers whose VM value did not survive a merge
        self.consumed = set()
        self.last_op = None
        self.base_tabs_ids = set()
        self.tab_written = {}
        self.nregs = None
        self.vmcalls = 0
        self.written_now = set()
        self.hloc = {}              # handler local declaration -> HLOC register number
        self.held = []              # (scope, local, value, refs): handler locals whose value can go stale
        self.hrepl = []             # (statement, copy register, value): statements _materialize pointed at a copy
        self.lvreg = {}             # fused loops: handler local -> LV register number
        self.boxvars = {}           # (pc, register) of a box creation -> BOX_BASE register number
        self.step_reads = set()     # (this run) carried locals read before written
        self.pc_use = {}            # pc -> [locals read before written, locals always written]
        self.live = None            # pc -> carried locals live on entry (from the previous walk)
        self.check_temps = set()    # call temps of the environment check (CheckResult)
        self.lv_active = {}         # (this run) handler locals that live in their LV register

    # ---- access tracking (the carried state)
    def note_read(self, key):
        if self.in_prologue:
            return
        if key not in self.written_now:
            self.step_reads.add(key)
        if key not in self.written_now and key not in self.carry and key != self.vm.pc_decl:
            self.carry.add(key)
            self.new_carry = True

    def note_write(self, key):
        self.written_now.add(key)

    def record_use(self, pc, reads, writes):
        u = self.pc_use.get(pc)
        if u is None:
            self.pc_use[pc] = [set(reads), set(writes)]
        else:
            u[0] |= reads
            u[1] &= writes

    def liveness(self, nodes):
        """pc -> carried locals live on entry (read later before written)"""
        succ = {}
        for k, n in nodes.items():
            out = []
            _next_states(n, out)
            succ.setdefault(k[1], set()).update(ns.pc for ns in out)
        live = {pc: set(u[0]) for pc, u in self.pc_use.items()}
        changed = True
        while changed:
            changed = False
            for pc, ss in succ.items():
                u = self.pc_use.get(pc)
                if u is None:
                    continue
                cur = live.setdefault(pc, set())
                add = set()
                for x in ss:
                    add |= live.get(x, set())
                add -= u[1]
                if not add <= cur:
                    cur |= add
                    changed = True
        pcd = self.vm.pc_decl
        return {pc: frozenset(v | {pcd}) for pc, v in live.items()}

    def local_value(self, key, v):
        """a symbolic value assigned to an interpreter local lives in a register"""
        if isinstance(v, Multi):
            v = v.first()
        if isinstance(v, Expr) and not isinstance(v, (Lin, SpreadIdx)):
            r = Reg(LOC_BASE + self.vm.iloc_index.get(key, 0))
            if not (isinstance(v, Reg) and v.n == r.n):
                self.emit(Assign(r, self.value_of(v)))
            return r
        return v

    def hold(self, key, v, scope):
        """a handler local keeps its value's expression, but when a statement
        is about to change something that expression reads (a register, a
        table, an upvalue, a global), the value is first copied into a
        register of its own (emit): `local x = R[a] + R[c]; R[a] = x; if x <= R[b]`
        must compare the sum, not the new R[a] plus R[c]"""
        if self.in_prologue or not isinstance(v, Expr) or isinstance(v, (Lin, SpreadIdx, Const, TempVal, Vararg,
                                                                            ClosureExpr, KnownGlobal)):
            return v
        refs = _mutable_refs(v)
        if refs is None:
            # a big expression (a local updated in a loop): a register now,
            # so expressions stay small
            n = self.hloc.setdefault(key, len(self.hloc) + 1)
            r = Reg(HLOC_BASE + n)
            c = self.fval(v)
            self.emit(Assign(r, v))
            self.facts.pop(r.n, None)
            if c is not NOFOLD:
                self.facts[r.n] = c
            return r
        if refs:
            self.held.append((scope, key, v, refs))
        return v

    def _materialize(self, st):
        w = _writes(st)
        if not w:
            return
        keep = []
        for ent in self.held:
            sc, key, v, refs = ent
            if sc.vars.get(key) is not v:
                continue            # (the local was reassigned: nothing to keep)
            if not (refs & w or ("g*" in w and any(x[0] == "g" for x in refs if isinstance(x, tuple)))
                    or ("u*" in w and any(x[0] == "u" for x in refs if isinstance(x, tuple)))):
                keep.append(ent)
                continue
            n = self.hloc.setdefault(key, len(self.hloc) + 1)
            r = Reg(HLOC_BASE + n)
            c = self.fval(v)
            cp = Assign(r, v)
            cp.hcopy = True         # (dropped at the end of the run if nothing reads r: prune_copies)
            self.out.append(cp)
            self.facts.pop(r.n, None)
            if c is not NOFOLD:
                self.facts[r.n] = c
            sc.vars[key] = r
            if isinstance(st, Assign) and st.value is v:
                st.value = r
                self.hrepl.append((st, r.n, v))
        self.held = keep

    def prune_copies(self, it, ret_values=None):
        """drop the copies _materialize made that nothing read after all"""
        if not any(getattr(x, "hcopy", False) for x in self.out):
            return
        live = set()
        for d in it.dlog:
            live |= _regs_in(d[2])
        if ret_values is not None:
            live |= _regs_in(ret_values)
        drop = set()
        for i in range(len(self.out) - 1, -1, -1):
            st = self.out[i]
            if getattr(st, "hcopy", False) and st.target.n not in live:
                drop.add(i)
                continue
            live |= _regs_in(st)
        if not drop:
            return
        gone = {self.out[i].target.n for i in drop}
        for st, rn, v in self.hrepl:
            if rn in gone and isinstance(st.value, Reg) and st.value.n == rn:
                st.value = v
        newpos = []
        k = 0
        for i in range(len(self.out) + 1):
            newpos.append(k)
            if i < len(self.out) and i not in drop:
                k += 1
        self.out = [x for i, x in enumerate(self.out) if i not in drop]
        it.dlog = [(a, newpos[b], c, d) for a, b, c, d in it.dlog]

    # ---- prologue / state
    def initial_state(self):
        vm = self.vm
        sc = Scope(self.cscope)
        sc.vars["..."] = Multi([], VarargTail(1))
        self.iscope = sc
        self.written_now = set()
        self.out = []           # (the entry block is what the prologue emits: nothing older)
        self.held = []
        self.in_prologue = True
        it = LiftInterp(self)
        it.exec_block(vm.prologue, sc)
        self.in_prologue = False
        # the prologue's statements: the parameter copy `R[1], R[2] = ...`
        self.entry_out = [x for x in self.out if isinstance(x, Assign) and isinstance(x.target, Reg)]
        self.out = []
        self.base_vals = dict(sc.vars)
        self.base_tabs = {}
        for k, v in sc.vars.items():
            if isinstance(v, LTable) and v.tid is None:
                v.tid = "P%d" % len(self.base_tabs)
                self.base_tabs[v.tid] = (v, dict(v.h))
        return self.snapshot(sc)

    def snapshot(self, sc, sub=None):
        vals = []
        for k in sorted(self.carry | {self.vm.pc_decl}):
            vals.append((k, sc.vars.get(k)))
        pc = sc.vars.get(self.vm.pc_decl)
        tabs = []
        for tid_, (t, _) in sorted(self.base_tabs.items()):
            if tid_ in self.tab_carry:
                tabs.append((tid_, dict(t.h)))
        return State(pc, tuple(vals), tuple(tabs), dict(self.boxes), self.top, dict(self.iters),
                     dict(self.facts), self.lost, sub, self.live)

    def restore(self, state, facts=None, lost=None):
        sc = Scope(self.cscope)
        sc.vars = dict(self.base_vals)
        # tables built here are copied per run; one memo for the carried
        # locals, the VM tables' contents and the facts, so a table held in
        # both a local and a register is still one object
        memo = {}
        for k, v in state.vals:
            sc.vars[k] = _copy_fresh(v, memo)
        for tid_, (t, h) in self.base_tabs.items():
            t.h = dict(h)
        for tid_, h in state.tabs:
            self.base_tabs[tid_][0].h = {k: _copy_fresh(v, memo) for k, v in h.items()}
        self.boxes = dict(state.boxes)
        self.top = state.top
        self.iters = {r: _copy_fresh(v, memo) for r, v in state.iters.items()}
        self.facts = {r: _copy_fresh(v, memo) for r, v in (state.facts if facts is None else facts).items()}
        self.lost = state.lost if lost is None else lost
        self.home = {}
        for r in sorted(x for x in self.facts if isinstance(x, int)):
            f = self.facts[r]
            if isinstance(f, LTable) and f.tid is None and id(f) not in self.home and not self.is_scratch(r):
                self.home[id(f)] = r
        self.results = {}
        self.consumed = set()
        self.held = []
        self.hrepl = []
        self.lv_active = {}
        self.iscope = sc
        self.written_now = set()
        self.step_reads = set()
        return sc

    def scrub(self, sc):
        """after a step: multiple results that were consumed are dead; the
        handler locals' snapshots too"""
        for r in [r for r in self.facts if isinstance(r, int) and HLOC_BASE <= r < OVL_BASE]:
            del self.facts[r]
        if self.top is not None and id(self.top[1]) in self.consumed:
            self.top = None
        live = set()        # call tails still held (the pending top, spread slots of VM tables)
        if self.top is not None:
            live.add(id(self.top[1].tail))
        for tid_, (t, _) in self.base_tabs.items():
            for k, v in list(t.h.items()):
                if isinstance(v, Spread) and id(v.m) in self.consumed:
                    del t.h[k]
                elif isinstance(v, Spread) and v.m.tail is not None:
                    live.add(id(v.m.tail))
        for k, v in list(sc.vars.items()):
            if isinstance(v, Lin) and isinstance(v.tail, TempTail) and id(v.tail) not in live:
                sc.vars[k] = self.base_vals.get(k)

    # ---- luasym hooks
    def is_dispatch(self, node):
        return node is self.vm.loop

    def check_decision(self, cond):
        pass

    def emit(self, st):
        if self.held:
            self._materialize(st)
        self.out.append(st)

    def new_temp(self):
        self.tcount += 1
        return "%s%d" % (self.temp_prefix, self.tcount)

    def special_get(self, sp, it):
        raise Unsupported(sp)

    def special_set(self, sp, v, it):
        raise Unsupported(sp)

    def global_value(self, name):
        return self.prog.globals.get(name.encode("latin-1")) or Global(name)

    def varargs(self, scope):
        s = scope
        while s is not None:
            if "..." in s.vars:
                return s.vars["..."]
            s = s.parent
        raise Unsupported("varargs outside vararg function")

    def as_expr(self, v):
        if isinstance(v, _Lost):
            v.fail()
        if isinstance(v, Stored):
            # (a value stored into a table built here: its value then)
            c = v.const
            if c is None or isinstance(c, (bool, int, float, bytes)):
                return Const(c)
            return self.as_expr(v.expr)
        if isinstance(v, Lin):
            return v.as_expr()
        if isinstance(v, BoxRef):
            return v.target
        if isinstance(v, Expr):
            return v
        if isinstance(v, Vec):
            return v
        if v is None or isinstance(v, (bool, int, float, bytes)):
            return Const(v)
        if isinstance(v, Multi):
            return self.as_expr(v.first())
        if isinstance(v, EnvTable):
            return Global("_ENV")
        if isinstance(v, Builtin):
            return Global(v.name)
        if isinstance(v, Spread):
            return self.as_expr(v.m.first())
        if isinstance(v, LTable) and v.tid is None:
            return self.table_expr(v)
        raise Unsupported("value %r in an expression" % (v,))

    def table_expr(self, v):
        """a table built here, used as a value: its register, or a constructor"""
        r = self.escape(v)
        if r is not None:
            return r
        return S.NewTable(self.ctor_items(v))

    def ctor_items(self, t):
        """constructor items of a table built here: keys 1..n positional"""
        h = {k: x for k, x in t.h.items() if k is not TBLID and k is not TAINT}
        n = 0
        while (n + 1) in h:
            n += 1
        items = [(None, self.value_of(h[i])) for i in range(1, n + 1)]
        for k, x in h.items():
            if isinstance(k, int) and not isinstance(k, bool) and 1 <= k <= n:
                continue
            items.append((Const(k) if not isinstance(k, Expr) else k, self.value_of(x)))
        return items

    def value_of(self, v):
        if isinstance(v, Multi):
            v = v.first()
        if isinstance(v, (ClosureExpr, GenIter, SymList)):
            return v
        if isinstance(v, LTable):
            if v.tid is None:
                return self.table_expr(v)
            raise Unsupported("storing a VM table into a register (table %s: %s)" % (
                v.tid, ", ".join("%r=%s" % (k, fmt_any(x)) for k, x in list(v.h.items())[:6])))
        return self.as_expr(v)

    def sym_binop(self, op, a, b):
        if isinstance(a, (Lin, SpreadIdx)) or isinstance(b, (Lin, SpreadIdx)):
            return self.lin_binop(op, a, b)
        if op in ("CompareEq", "CompareNe"):
            # a register value is never the VM's own tables
            # (nor a table built here that is still tracked: no IR value was
            # ever given it)
            vm = lambda x: isinstance(x, (RegFile, UpList, LTable, FuncRef, VMClosure))  # noqa: E731
            if vm(a) or vm(b):
                return op == "CompareNe"
        if isinstance(a, (SymList, RegFile)) or isinstance(b, (SymList, RegFile)):
            raise Unsupported("arith on VM object")
        return Bin(op, self.as_expr(a), self.as_expr(b))

    def lin_binop(self, op, a, b):
        num = lambda x: isinstance(x, int) and not isinstance(x, bool)  # noqa: E731
        if op == "Add" and isinstance(a, Lin) and num(b):
            return Lin(a.c + b, a.tail)
        if op == "Add" and isinstance(b, Lin) and num(a):
            return Lin(b.c + a, b.tail)
        if op == "Sub" and isinstance(a, Lin) and num(b):
            return Lin(a.c - b, a.tail)
        if op == "Add" and isinstance(a, SpreadIdx) and num(b):
            return SpreadIdx(a.start + b)
        if op == "Add" and isinstance(b, SpreadIdx) and num(a):
            return SpreadIdx(b.start + a)
        if op == "Sub" and isinstance(a, SpreadIdx) and num(b):
            return SpreadIdx(a.start - b)
        if op == "Sub" and isinstance(a, Lin) and isinstance(b, Lin) and a.tail is b.tail:
            return a.c - b.c
        if op in ("CompareLt", "CompareLe", "CompareGt", "CompareGe", "CompareEq", "CompareNe"):
            # counts of multiple results are assumed small (helpers pick a
            # slow path for huge counts) and at least their known part
            if isinstance(a, Lin) and num(b):
                lo = a.c
                if op in ("CompareGt", "CompareGe") and b >= lo + 200:
                    return False
                if op in ("CompareLt", "CompareLe") and b >= lo + 200:
                    return True
                if op == "CompareGe" and b <= lo:
                    return True
                if op == "CompareLt" and b <= lo:
                    return False
                if b <= 0 and op in ("CompareLt", "CompareGe"):
                    # `#extra varargs < 0` (a clamp before copying them): the
                    # copy of the tail is one spread slot, right for any count
                    return op == "CompareGe"
            if isinstance(b, Lin) and num(a):
                flip = {"CompareLt": "CompareGt", "CompareLe": "CompareGe", "CompareGt": "CompareLt",
                        "CompareGe": "CompareLe", "CompareEq": "CompareEq", "CompareNe": "CompareNe"}[op]
                return self.lin_binop(flip, b, a)
            return Bin(op, self.as_expr(a), self.as_expr(b))
        if op == "Sub" and isinstance(a, Lin) and isinstance(b, int):
            return Lin(a.c - b, a.tail)
        return Bin(op, self.as_expr(a), self.as_expr(b))

    def sym_unop(self, op, a):
        if isinstance(a, SymList):
            if op == "Len":
                return a.count_expr()
            raise Unsupported("unop on packed list")
        return Un(op, self.as_expr(a))

    # ---- indexing
    def reg_read(self, k):
        if isinstance(k, SpreadIdx):
            if self.top is None:
                raise Unsupported("register spread without a multiple result")
            base, m = self.top
            if ("top",) not in self.written_now:
                self.step_reads.add(("top",))
            if k.start < base:
                pre = [self.reg_read(r) for r in range(k.start, base)]
                m2 = Multi([self.as_expr(x) for x in pre] + m.items, m.tail)
            elif k.start == base:
                m2 = m
            else:
                raise Unsupported("register spread above the multiple result")
            self.consumed.add(id(m))
            return Spread(m2)
        if is_sym(k):
            c = self.fval(k)
            if c is NOFOLD:
                raise Unsupported("symbolic register index %s" % fmt_expr(k))
            k = c
        k = S.norm_key(k)
        if not isinstance(k, int) or isinstance(k, bool):
            raise Unsupported("register index %r" % (k,))
        if k in self.boxes:
            return BoxRef(self.boxes[k])
        if k in self.iters:
            if ("iter", k) not in self.written_now:
                self.step_reads.add(("iter", k))
            return self.iters[k]
        if k in self.facts:
            f = self.facts[k]
            if isinstance(f, Builtin):
                # a library function the VM cached (`ipairs` from its registry)
                return KnownGlobal(f.name)
            if _is_phantom(f) or isinstance(f, LTable) or f is VMGLOBAL:
                return f
            return Reg(k)       # a known scalar or check result: folded where it decides something (fval)
        if k in self.lost:
            return _Lost(k)
        if self.top is not None and k == self.top[0]:
            # a multiple result's first value read as one value
            return self.as_expr(self.top[1].first())
        return Reg(k)

    def reg_write(self, k, v):
        if isinstance(k, SpreadIdx):
            if not isinstance(v, Spread):
                raise Unsupported("register spread store of %r" % (v,))
            self.top = (k.start, v.m)
            self.written_now.add(("top",))
            return
        if is_sym(k):
            c = self.fval(k)
            if c is NOFOLD:
                raise Unsupported("symbolic register store %s" % fmt_expr(k))
            k = c
        k = S.norm_key(k)
        if not isinstance(k, int) or isinstance(k, bool):
            raise Unsupported("register store at %r" % (k,))
        if isinstance(v, Multi):
            v = v.first()
        if isinstance(v, _Lost):
            if self.top is not None and k <= self.top[0]:
                self.top = None
            for x in (k, ("clo", k), ("glob", k)):
                self.facts.pop(x, None)
            self.iters.pop(k, None)
            self.boxes.pop(k, None)
            self.lost = self.lost | {k}
            return
        # the new value's fact, before k's old fact goes (`r = r ~= nil`)
        newfact = self.fval(v) if isinstance(v, Expr) and not isinstance(v, (Lin, SpreadIdx)) else NOFOLD
        if self.top is not None and k <= self.top[0]:
            self.top = None
        self.iters.pop(k, None)
        self.written_now.add(("iter", k))
        self.facts.pop(k, None)
        self.facts.pop(("clo", k), None)
        self.facts.pop(("glob", k), None)
        if k in self.lost:
            self.lost = self.lost - {k}
        if isinstance(v, Spread):
            self.top = (k, v.m)
            self.written_now.add(("top",))
            return
        if isinstance(v, TempVal) and v.t in self.check_temps:
            self.facts[k] = CheckResult(v.i)
            return
        if isinstance(v, BoxTable) and list(v.h) == [1]:
            # `R[a] = {R[a]}`: a box for a captured local. The box is a
            # variable of its own (BOX_BASE + n per creation site), not the
            # register: the VM moves boxes between registers and reuses the
            # register while the box lives on (`R[b] = R[a]; R[a] = self;
            # ...; R[a] = R[b]` around a method call)
            inner = v.h[1]
            pc = self.iscope.vars.get(self.vm.pc_decl) if self.iscope is not None else None
            bv = Reg(BOX_BASE + self.boxvars.setdefault((pc, k), len(self.boxvars) + 1))
            self.emit(Close(bv.n))      # (a new box here: the next iteration's local is a new variable)
            if isinstance(inner, LTable) and inner.tid is None:
                self.reg_write(k, inner)        # (a table built here: tracked as usual)
                self.escape(inner)
                inner = Reg(k)
            if inner is not None:
                self.emit(Assign(bv, self.value_of(inner)))
            self.boxes[k] = bv
            return
        if isinstance(v, BoxRef):
            # a box copied (an upvalue box into a register)
            self.boxes[k] = v.target
            return
        self.boxes.pop(k, None)
        if isinstance(v, GenIterRef):
            pv = Pseudo("a", k)
            self.emit(Assign(pv, GenIter(Multi([None] + [self.as_expr(x) for x in v.args]))))
            self.iters[k] = pv
            return
        if _is_phantom(v) or v is VMGLOBAL:
            # a VM value in a register (the constant table, a helper): only a fact
            self.facts[k] = v
            return
        if isinstance(v, LTable):
            # a table built here: tracked as a fact while its contents are known
            h = self.home_of(v)
            self.facts[k] = v
            if not self.is_scratch(k) and (h is not None or TAINT in v.h):
                # an existing table moved to another register
                if h is not None:
                    st = Assign(Reg(k), Reg(h))
                    self.emit(st)
                    if TBLID in v.h:
                        self.prog.tbl_stmts.setdefault(v.h[TBLID], []).append(st)
                return
            if not self.is_scratch(k):
                self.home[id(v)] = k
                st = Assign(Reg(k), S.NewTable(self.ctor_items(v)))
                self.emit(st)
                n = self.prog.new_table_id()
                v.h[TBLID] = n
                self.prog.tbl_stmts.setdefault(n, []).append(st)
            return
        if v is None or isinstance(v, (bool, int, float, bytes)):
            # (scratch registers too: a merge with an IR value keeps it; dead
            # stores are dropped by the back end)
            self.facts[k] = v
            self.emit(Assign(Reg(k), Const(v)))
            return
        val = self.value_of(v)
        c = newfact
        self.emit(Assign(Reg(k), val))
        if c is not NOFOLD:
            self.facts[k] = c
        if isinstance(val, ClosureExpr):
            self.facts[("clo", k)] = val
        elif isinstance(val, Global):
            self.facts[("glob", k)] = val.name     # (which global a register caches)

    def is_scratch(self, k):
        return self.nregs is not None and isinstance(k, int) and k > self.nregs

    # ---- facts
    def fval(self, e):
        """the value of IR expression e under the register facts, or NOFOLD"""
        if e is None or isinstance(e, (bool, int, float, bytes)):
            return e
        if isinstance(e, Const):
            return e.v
        if isinstance(e, Reg):
            if e.n in self.facts:
                f = self.facts[e.n]
                if f is None or f is TRUTHY or isinstance(f, (bool, int, float, bytes)):
                    return f
                if isinstance(f, CheckResult):
                    return True if f.i == 1 else f
            return NOFOLD
        if isinstance(e, TempVal) and e.t in self.check_temps:
            return True if e.i == 1 else CheckResult(e.i)
        if isinstance(e, Global):
            return TRUTHY if isinstance(e, KnownGlobal) or (type(e) is Global and e.name in STD_GLOBALS) else NOFOLD
        if isinstance(e, Bin):
            a = self.fval(e.a)
            if a is NOFOLD:
                return NOFOLD
            if e.op == "And":
                return self.fval(e.b) if S.truthy(a) else a
            if e.op == "Or":
                return a if S.truthy(a) else self.fval(e.b)
            b = self.fval(e.b)
            if (isinstance(a, CheckResult) or isinstance(b, CheckResult)) and b is not NOFOLD:
                # the check passed: its results equal what the script compares them with
                if e.op in ("CompareEq", "CompareNe"):
                    return e.op == "CompareEq"
                return NOFOLD
            if isinstance(a, CheckResult):
                return NOFOLD
            if (a is TRUTHY or b is TRUTHY) and e.op in ("CompareEq", "CompareNe") and b is not NOFOLD:
                other = b if a is TRUTHY else a
                if other is None or other is False:
                    return e.op == "CompareNe"
            if b is NOFOLD or a is TRUTHY or b is TRUTHY:
                return NOFOLD
            try:
                if e.op == "CompareEq":
                    return S.lua_eq(a, b)
                if e.op == "CompareNe":
                    return not S.lua_eq(a, b)
                if e.op in ("CompareLt", "CompareLe", "CompareGt", "CompareGe"):
                    if not ((isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool)
                             and not isinstance(b, bool)) or (isinstance(a, bytes) and isinstance(b, bytes))):
                        return NOFOLD
                    return {"CompareLt": a < b, "CompareLe": a <= b, "CompareGt": a > b, "CompareGe": a >= b}[e.op]
                if e.op == "Concat":
                    if isinstance(a, (bytes, int, float)) and isinstance(b, (bytes, int, float)) \
                            and not isinstance(a, bool) and not isinstance(b, bool):
                        f = lambda x: x if isinstance(x, bytes) else S.fmt_num(x).encode()  # noqa: E731
                        return f(a) + f(b)
                    return NOFOLD
                x, y = S.lua_num(a), S.lua_num(b)
                if x is None or y is None or isinstance(a, bool) or isinstance(b, bool):
                    return NOFOLD
                return S.arith(e.op, x, y)
            except (ZeroDivisionError, OverflowError, ValueError, Unsupported):
                return NOFOLD
        if isinstance(e, Un):
            a = self.fval(e.a)
            if a is NOFOLD:
                return NOFOLD
            if e.op == "Not":
                return not S.truthy(a)
            if a is TRUTHY:
                return NOFOLD
            if e.op == "Minus" and isinstance(a, (int, float)) and not isinstance(a, bool):
                return S.fix_int(-a)
            if e.op == "Len" and isinstance(a, bytes):
                return len(a)
            return NOFOLD
        return NOFOLD

    def concrete_key(self, key):
        if is_sym(key):
            return self.fval(key)
        return key

    def home_of(self, t):
        """a register holding table t (IR name of a table built here)"""
        if TAINT in t.h:
            return None
        h = self.home.get(id(t))
        if h is not None and self.facts.get(h) is t:
            return h
        for r, f in self.facts.items():
            if f is t and isinstance(r, int) and not self.is_scratch(r):
                self.home[id(t)] = r
                return r
        return None

    def ir_ref(self, v, into=None):
        """IR form of a value stored into a table built here: a tracked table
        stays tracked (both are our objects, so aliasing is modelled); it is
        used if the table it went into is"""
        if isinstance(v, LTable) and v.tid is None:
            h = self.home_of(v)
            if h is not None:
                if into is not None and TBLID in v.h and TBLID in into.h:
                    self.prog.tbl_deps.setdefault(into.h[TBLID], set()).add(v.h[TBLID])
                return Reg(h)
        if v is None:
            return Const(None)
        return self.value_of(v)

    def escape(self, t):
        """table t is used as a value: from now on only its IR register knows it"""
        h = self.home_of(t)
        if h is None:
            return None
        self.prog.used_table(t)
        for r, f in list(self.facts.items()):
            if f is t:
                del self.facts[r]
        return Reg(h)

    def index(self, obj, key, it):
        if isinstance(obj, Multi):
            obj = obj.first()
        if isinstance(key, Multi):
            key = key.first()
        for x in (obj, key):
            if isinstance(x, _Lost):
                x.fail()
        if isinstance(obj, RegFile):
            return self.reg_read(key)
        if obj is VMGLOBAL:
            # the VM's run-once registry global (tables of bookkeeping tables)
            return VMGLOBAL
        if isinstance(obj, BoxRef):
            if key == 1:
                return obj.target
            return None
        if isinstance(obj, UpList):
            if not isinstance(key, int):
                raise Unsupported("upvalue index %r" % (key,))
            kind = self.uplist.kinds.get(key)
            if kind == "box":
                return BoxRef(Upval(key))
            if isinstance(kind, tuple) and kind[0] == "const":
                return kind[1]      # a literal captured by value
            return Upval(key)
        if isinstance(obj, EnvTable):
            key = self.concrete_key(key) if is_sym(key) and self.fval(key) is not NOFOLD else key
            if isinstance(key, bytes):
                if _hashlike(key):
                    # the VM's run-once registry global: its table from the run
                    v = self.dump.env_vals.get(key)
                    return v if isinstance(v, LTable) else VMGLOBAL
                return Global(key.decode("latin-1"))
            return Index(Global("_ENV"), self.as_expr(key))
        if isinstance(obj, InsProxy):
            k = self.concrete_key(key)
            t = obj.fields.get(S.norm_key(k)) if k is not NOFOLD else None
            if t is None:
                raise Unsupported("instruction proxy field %r" % (key,))
            return self.index(t, obj.pc, it)
        if isinstance(obj, LTable) and id(obj) in self.dump.proxy_fields:
            k = self.concrete_key(key)
            if isinstance(k, int) and not isinstance(k, bool):
                return InsProxy(self.dump.proxy_fields[id(obj)], k)
        if isinstance(obj, LTable):
            lst = self.results.get(id(obj))
            if lst is not None:
                return self.symlist_get(lst, key)
            if isinstance(key, SpreadIdx):
                # the values from key.start on, up to the table's spread slot
                if id(obj) in self.base_tabs_ids:
                    for j in range(key.start, key.start + 64):
                        if j not in self.tab_written.get(id(obj), ()):
                            self.step_reads.add(("tab", obj.tid, j))
                    if obj.tid not in self.tab_carry:
                        self.tab_carry.add(obj.tid)
                        self.new_carry = True
                vals = []
                n = key.start
                while n <= key.start + 256:
                    x = _unstore(obj.get(n))
                    if isinstance(x, Spread):
                        return Spread(Multi([self.as_expr(v) for v in vals] + x.m.items, x.m.tail))
                    vals.append(x)
                    n += 1
                raise Unsupported("spread read of a VM table")
            if is_sym(key):
                c = self.fval(key)
                if c is NOFOLD:
                    if obj.tid is None:
                        r = self.escape(obj)
                        if r is not None:
                            return Index(r, self.as_expr(key))
                    raise Unsupported("symbolic index into a concrete VM table (key %s)" % fmt_expr(key))
                key = c
            if id(obj) in self.base_tabs_ids and S.norm_key(key) not in self.tab_written.get(id(obj), ()):
                self.step_reads.add(("tab", obj.tid, S.norm_key(key)))
                if obj.tid not in self.tab_carry:
                    self.tab_carry.add(obj.tid)
                    self.new_carry = True
            if isinstance(obj.tid, int):
                slot = ("ovl", obj.tid, S.norm_key(key))
                if slot in self.facts and slot not in self.written_now:
                    # (a slot something wrote: operand and junk reads of slots
                    # never written do not matter for keys)
                    self.step_reads.add(slot)
                if slot in self.facts:
                    v = self.facts[slot]
                    if isinstance(v, Stored):
                        c = v.const
                        # (a known scalar reads as itself: operands, jump targets)
                        return c if c is None or isinstance(c, (bool, int, float, bytes)) else v.expr
                    return v
                # (a slot some paths wrote and others did not: the value from the run)
            v = obj.get(key)
            if isinstance(v, Stored):
                return v.const
            if obj.tid is None and isinstance(v, Expr):
                # a value stored into a table built here: read it through the table
                h = self.home_of(obj)
                if h is not None:
                    self.prog.used_table(obj)
                    return Index(Reg(h), self.as_expr(key))
            return v
        if isinstance(obj, SymList):
            return self.symlist_get(obj, key)
        if obj is VMGLOBAL:
            return None
        if isinstance(obj, Expr):
            return Index(obj, self.as_expr(key))
        if obj is None:
            raise Unsupported("index nil")
        raise Unsupported("index %r" % (obj,))

    def symlist_get(self, lst, key):
        if isinstance(key, SpreadIdx):
            s = key.start
            if s <= len(lst.items):
                m = Multi([self.as_expr(x) for x in lst.items[s - 1:]], lst.tail)
            elif lst.tail is not None:
                m = Multi([], lst.tail.drop(s - len(lst.items) - 1))
            else:
                m = Multi([])
            return Spread(m)
        if key == lst.nkey or (lst.nkey is None and key == b"n"):
            return self.count_of(lst)
        if isinstance(key, int) and key >= 1:
            if key <= len(lst.items):
                return lst.items[key - 1]
            if lst.tail is not None:
                return lst.tail.at(key - len(lst.items))
            return None
        if key in lst.extra:
            return lst.extra[key]
        raise Unsupported("packed list index %r" % (key,))

    def count_of(self, lst):
        if lst.tail is None:
            return len(lst.items)
        return Lin(len(lst.items), lst.tail)

    def newindex(self, obj, key, v, it):
        if isinstance(key, Multi):
            key = key.first()
        if isinstance(v, Multi):
            v = v.first()
        for x in (obj, key):
            if isinstance(x, _Lost):
                x.fail()
        if isinstance(obj, RegFile):
            self.reg_write(key, v)
            return
        if isinstance(obj, InsProxy):
            k = self.concrete_key(key)
            t = obj.fields.get(S.norm_key(k)) if k is not NOFOLD else None
            if t is None:
                raise Unsupported("instruction proxy field %r" % (key,))
            return self.newindex(t, obj.pc, v, it)
        if isinstance(obj, BoxRef):
            if key != 1:
                raise Unsupported("box store at %r" % (key,))
            self.emit(Assign(obj.target, self.value_of(v)))
            return
        if isinstance(obj, EnvTable):
            if is_sym(key) and self.fval(key) is not NOFOLD:
                key = self.fval(key)
            if isinstance(key, bytes) and _hashlike(key):
                return      # the VM's run-once key
            tgt = Global(key.decode("latin-1")) if isinstance(key, bytes) else Index(Global("_ENV"), self.as_expr(key))
            self.emit(Assign(tgt, self.value_of(v)))
            return
        if obj is VMGLOBAL:
            return
        if isinstance(obj, LTable):
            if isinstance(obj.tid, int):
                # VM data (constant caches, registries): a store is kept as a
                # path-sensitive fact (a value parked there is read back:
                # `T[id] = x ... x = T[id]`); symbolic values go through a
                # dedicated register so later reads see the stored value
                if is_sym(key):
                    key = self.fval(key)
                    if key is NOFOLD:
                        return
                k = S.norm_key(key)
                slot = ("ovl", obj.tid, k)
                self.written_now.add(slot)
                if isinstance(v, _Lost):
                    self.facts.pop(slot, None)
                    return
                if isinstance(v, Reg) and isinstance(self.facts.get(("clo", v.n)), ClosureExpr):
                    # a closure parked in the VM's registry: one of its runtime
                    # functions (integrity checks), not script code
                    self.facts[("clo", v.n)].runtime = True
                if isinstance(v, Expr) and not isinstance(v, (Lin, SpreadIdx)):
                    n = self.ovl_slots.setdefault((obj.tid, k), len(self.ovl_slots) + 1)
                    r = Reg(OVL_BASE + n)
                    self.emit(Assign(r, self.value_of(v)))
                    c = self.fval(v)
                    self.facts.pop(r.n, None)
                    if c is not NOFOLD:
                        # (a read of the slot gives r: it keeps the known value)
                        self.facts[r.n] = c
                    v = Stored(r, c) if c is not NOFOLD else r
                self.facts[slot] = v
                return
            if is_sym(key):
                c = self.fval(key)
                if c is NOFOLD:
                    if obj.tid is None:
                        r = self.escape(obj)
                        if r is not None:
                            self.emit(Assign(Index(r, self.as_expr(key)), self.value_of(v)))
                            return
                    raise Unsupported("symbolic key store into a concrete VM table (key %s, table %s: %s)" % (
                        fmt_expr(key), obj.tid, _keyval(obj)[:200]))
                key = c
            k = S.norm_key(key)
            if id(obj) in self.base_tabs_ids:
                self.tab_written.setdefault(id(obj), set()).add(k)
                self.written_now.add(("tab", obj.tid, k))
                if isinstance(v, LTable) and v.tid is None:
                    v = self.table_expr(v)
                if isinstance(v, Spread):
                    # a multiple result moved onto the argument stack: a copy
                    # of its own (the register's one is consumed by the move)
                    v = Spread(Multi(list(v.m.items), v.m.tail))
                if isinstance(v, Expr) and not isinstance(v, (Lin, SpreadIdx)):
                    # argument stack: the value is copied into a stack register
                    n = self.stack_tabs.setdefault(obj.tid, len(self.stack_tabs) + 1)
                    r = Reg(STACK_BASE * n + k)
                    if not (isinstance(v, Reg) and v.n == r.n):
                        self.emit(Assign(r, self.value_of(v)))
                    v = r
                obj.set(k, v)
                return
            if obj.tid is None:
                h = self.home_of(obj)
                if h is not None and (_is_phantom(k) or _is_phantom(v) or v is VMGLOBAL
                                      or (isinstance(v, LTable) and self.home_of(v) is None)):
                    # VM objects as keys/values (an opaque predicate built on the
                    # instruction table): the table can no longer be IR
                    obj.h[TAINT] = True
                    h = None
                if h is not None:
                    st = Assign(Index(Reg(h), self.ir_ref(k, obj)), self.ir_ref(v, obj))
                    self.emit(st)
                    if TBLID in obj.h:
                        self.prog.tbl_stmts.setdefault(obj.h[TBLID], []).append(st)
                if isinstance(v, Expr):
                    c = self.fval(v)
                    if c is not NOFOLD:
                        v = Stored(v, c)
                obj.set(k, v)
                return
            obj.set(k, v)
            return
        if isinstance(obj, Expr):
            if isinstance(key, SpreadIdx):
                if not isinstance(v, Spread):
                    raise Unsupported("spread store of %r" % (v,))
                self.emit(SetList(obj, key.start, Multi([self.as_expr(x) for x in v.m.items], v.m.tail)))
                return
            self.emit(Assign(Index(obj, self.as_expr(key)), self.value_of(v)))
            return
        if isinstance(obj, SymList):
            obj.extra[key] = v
            return
        raise Unsupported("newindex %r" % (obj,))

    # ---- calls
    def call_symbolic(self, fn, args, it, stat):
        if isinstance(fn, Multi):
            fn = fn.first()
        if isinstance(fn, FuncRef):
            if fn.loc in self.prog.vms:
                return self.make_closure(args)
            if fn.node is None:
                raise Unsupported("call of an unknown VM function %s" % fn.loc)
            return it.call_lua(LuaFunc(fn.node, self.cscope), args)
        if isinstance(fn, LuaFunc):
            return it.call_lua(fn, args)
        if isinstance(fn, BoxRef):
            fn = fn.target
        if isinstance(fn, VMClosure) or any(_is_phantom(x) or x is VMGLOBAL for x in args.items):
            # one of the VM's runtime functions (constant decoding, integrity
            # checks: called with the VM's own tables, which script code
            # can never reach)
            self.vmcalls += 1
            return Multi([])
        if isinstance(fn, (UpList, LTable, RegFile)):
            raise Unsupported("call of a VM object %r" % (fn,))
        fe = self.as_expr(fn)
        gname = fe.name if isinstance(fe, Global) else             self.facts.get(("glob", fe.n)) if isinstance(fe, Reg) else None
        if gname == "pcall" and len(args.items) == 1 and args.tail is None:
            c = args.items[0]
            if isinstance(c, Reg):
                c = self.facts.get(("clo", c.n))
            if isinstance(c, ClosureExpr) and c.proto in self.prog.check_protos:
                c.runtime = True
                t = self.new_temp()
                self.check_temps.add(t)
                return Multi([], TempTail(t))
        t = self.new_temp()
        items = []
        tail = args.tail
        for i, x in enumerate(args.items):
            if isinstance(x, Spread):
                if i != len(args.items) - 1 or tail is not None:
                    raise Unsupported("spread in the middle of an argument list")
                items += [self.as_expr(y) for y in x.m.items]
                tail = x.m.tail
                self.consumed.add(id(x.m))
            else:
                items.append(self.value_of(x) if not isinstance(x, SymList) else x)
        self.emit(CallStmt(t, fe, Multi(items, tail)))
        return Multi([], TempTail(t))

    def make_closure(self, args):
        vals = args.items
        proto = vals[0] if vals else None
        ups = vals[1] if len(vals) > 1 else None
        if not isinstance(proto, LTable):
            raise Unsupported("closure of a non-proto %r" % (proto,))
        ci = self.dump.cap_of.get(id(proto))
        if ci is None:
            raise Unsupported("closure of a proto that was never captured (table %s)" % proto.tid)
        entries = []
        kinds = {}
        if isinstance(ups, LTable):
            n = max([k for k in ups.h if isinstance(k, int)] + [0])
            for i in range(1, n + 1):
                e = ups.h.get(i)
                if isinstance(e, Stored):
                    e = e.expr
                if isinstance(e, BoxRef):
                    kinds[i] = "box"
                    t = e.target
                    if isinstance(t, Reg):
                        entries.append(MaybeBox(t.n))
                        self.captured_regs.add(t.n)
                    else:
                        entries.append(t)
                else:
                    x = self.as_expr(e) if e is not None else Const(None)
                    c = self.fval(x)
                    if c is None or (isinstance(c, (bool, int, float, bytes)) and c is not TRUTHY):
                        # a by-value capture of a known literal: the closure's
                        # upvalue is that literal (the obfuscator hoists
                        # constants into the parent and passes them down)
                        kinds[i] = ("const", c)
                    entries.append(x)
        c = ClosureExpr(ci, entries)
        c.kinds = kinds
        self.children.append(c)
        return c

    def call_builtin(self, fn, args, it, stat):
        name = fn.name
        a = args
        if name == "table.create":
            if self.in_prologue:
                n = a.items[0] if a.items else None
                self.nregs = n if isinstance(n, int) and not isinstance(n, bool) else None
                return RegFile()
            return LTable()
        if name == "coroutine.wrap":
            f = a.items[0] if a.items else None
            if isinstance(f, LuaFunc) and _is_geniter_fn(f.node):
                vals = it.eval_list(f.node["body"]["body"][0]["values"], Scope(f.env), 3)
                return GenIterRef(vals)
            raise Unsupported("coroutine.wrap of a VM function")
        if name == "select":
            n = a.items[0] if a.items else None
            rest = Multi(a.items[1:], a.tail)
            if n == b"#":
                if rest.tail is None:
                    return len(rest.items)
                return Lin(len(rest.items), rest.tail)
            if isinstance(n, SpreadIdx):
                # select(i, ...) for the tail part of a loop up to #varargs:
                # all values from i on, as one spread slot
                n = n.start
                k = n - 1
                if k <= len(rest.items):
                    return Spread(Multi(rest.items[k:], rest.tail))
                return Spread(Multi([], rest.tail.drop(k - len(rest.items)) if rest.tail else None))
            if isinstance(n, int):
                k = n - 1
                if k <= len(rest.items):
                    return Multi(rest.items[k:], rest.tail)
                return Multi([], rest.tail.drop(k - len(rest.items)) if rest.tail else None)
            raise Unsupported("select with %r" % (n,))
        if name in ("unpack", "table.unpack"):
            return self.unpack(a)
        if name == "math.min" and len(a.items) == 2 and any(isinstance(x, Lin) for x in a.items):
            # min(#varargs, nparams): the parameter copy (missing ones read nil)
            other = [x for x in a.items if not isinstance(x, Lin)]
            if other and isinstance(other[0], int):
                return other[0]
        if name == "setmetatable":
            return Multi(a.items[:1])
        if name in S.CONCRETE:
            vals = a.items
            if a.tail is not None or any(is_sym(x) or isinstance(x, (SymList, Multi)) for x in vals):
                raise Unsupported("builtin %s on symbolic values" % name)
            try:
                return S.CONCRETE[name](*vals)
            except Exception as ex:  # noqa: BLE001
                raise Unsupported("%s failed: %s" % (name, ex))
        raise Unsupported("builtin " + name)

    def unpack(self, a):
        t = a.items[0] if a.items else None
        i = a.items[1] if len(a.items) > 1 else 1
        j = a.items[2] if len(a.items) > 2 else None
        if isinstance(t, RegFile):
            if isinstance(j, Lin):
                if self.top is None:
                    raise Unsupported("unpack registers to a missing top")
                base, m = self.top
                if ("top",) not in self.written_now:
                    self.step_reads.add(("top",))
                vals = [self.reg_read(n) for n in range(i, base)]
                self.consumed.add(id(m))
                return Multi([self.as_expr(v) for v in vals] + m.items, m.tail)
            if not isinstance(i, int) or not isinstance(j, int):
                raise Unsupported("unpack registers with symbolic range")
            vals = [self.reg_read(n) for n in range(i, j + 1)]
            return self._spread_multi(vals)
        if isinstance(t, SymList):
            if i != 1:
                raise Unsupported("unpack packed list from %r" % (i,))
            return Multi(t.items, t.tail)
        if isinstance(t, LTable):
            lst = self.results.get(id(t))
            if lst is not None:
                return Multi(lst.items, lst.tail)
            if j is None:
                j = t.length()
            if isinstance(j, Lin) and isinstance(i, int):
                # up to a count with a tail: the values up to the spread slot
                if id(t) in self.base_tabs_ids:
                    for n in range(i, i + 64):
                        if n not in self.tab_written.get(id(t), ()):
                            self.step_reads.add(("tab", t.tid, n))
                vals = []
                n = i
                while True:
                    x = _unstore(t.get(n))
                    vals.append(x)
                    if isinstance(x, Spread) or n > j.c + 1:
                        break
                    n += 1
                if not isinstance(vals[-1], Spread):
                    raise Unsupported("unpack up to a count with a tail, without the tail")
                return self._spread_multi(vals)
            if not isinstance(i, int) or not isinstance(j, int):
                raise Unsupported("unpack of a VM table with symbolic range")
            if id(t) in self.base_tabs_ids:
                for n in range(i, j + 1):
                    if n not in self.tab_written.get(id(t), ()):
                        self.step_reads.add(("tab", t.tid, n))
                    if n not in self.tab_written.get(id(t), ()) and t.tid not in self.tab_carry:
                        self.tab_carry.add(t.tid)
                        self.new_carry = True
            return self._spread_multi([_unstore(t.get(n)) for n in range(i, j + 1)])
        raise Unsupported("unpack %r" % (t,))

    def _spread_multi(self, vals):
        if vals and isinstance(vals[-1], Spread):
            sp = vals[-1]
            self.consumed.add(id(sp.m))
            return Multi(vals[:-1] + sp.m.items, sp.m.tail)
        return Multi(vals)

    def call_lua_hook(self, fn, args, it):
        """the results helper `f(t, ...)`: t holds the values, returns their count"""
        t = args.items[0] if args.items else None
        m = Multi(args.items[1:], args.tail)
        if not isinstance(t, LTable):
            raise Unsupported("results helper on %r" % (t,))
        lst = SymList(m.items, m.tail)
        self.results[id(t)] = lst
        # the values stay in the table for later instructions (`return
        # unpack(t, 1, top)`): known ones, then the tail as one spread slot
        t.h = {}
        for i, x in enumerate(m.items, 1):
            t.set(i, x)
        if m.tail is not None:
            t.h[len(m.items) + 1] = Spread(Multi([], m.tail))
        if id(t) in self.base_tabs_ids:
            self.tab_written.setdefault(id(t), set()).update(range(1, len(m.items) + 2))
            self.written_now.update(("tab", t.tid, j) for j in range(1, len(m.items) + 2))
        n = self.count_of(lst)
        top = self.vm.results_top.get(id(fn.node))
        if top is not None and self.iscope is not None:
            sc = self.iscope.lookup(top)
            if sc is not None:
                if sc is self.iscope:
                    self.note_write(top)
                sc.vars[top] = n
        return n


class LiftInterp(IBInterp):
    def cond_true(self, v):
        if isinstance(v, _Lost):
            v.fail()
        if isinstance(v, KnownGlobal) or (type(v) is Global and v.name in STD_GLOBALS):
            return True
        if isinstance(v, (Lin, SpreadIdx)):
            return True         # (a count or an index: a number)
        while isinstance(v, Un) and v.op == "Not" and isinstance(v.a, Un) and v.a.op == "Not":
            v = v.a.a           # (`not not x` decides like x)
        if is_sym(v) and not isinstance(v, (Lin, SpreadIdx)):
            c = self.L.fval(v)
            if c is not NOFOLD:
                return S.truthy(c)
        return S.Interp.cond_true(self, v)

    def call(self, fn, args, stat=False):
        if not isinstance(args, Multi):
            args = Multi(list(args))
        if isinstance(fn, LuaFunc) and id(fn.node) in self.L.vm.results_fns:
            return self.L.call_lua_hook(fn, args, self)
        if isinstance(fn, FuncRef) and fn.node is not None and fn.loc not in self.L.prog.vms:
            return self.call_lua(LuaFunc(fn.node, self.L.cscope), args)
        return S.Interp.call(self, fn, args, stat)


# --------------------------------------------------------------------------
# stepping and walking

def build_tree(paths, d, start):
    """paths share decisions[:d]; statements before `start` were emitted already."""
    if len(paths) == 1 and len(paths[0][0]) <= d:
        taken, dlog, out, oc = paths[0]
        return Node(out[start:], outcome=oc)
    p0 = paths[0]
    if len(p0[0]) <= d:
        taken, dlog, out, oc = p0
        return Node(out[start:], outcome=oc)
    cond = p0[1][d][2]
    at = p0[1][d][1]
    stmts = p0[2][start:at]
    tp = [p for p in paths if p[0][d]]
    fp = [p for p in paths if not p[0][d]]
    then = build_tree(tp, d + 1, at) if tp else None
    els = build_tree(fp, d + 1, at) if fp else None
    if then is not None and els is not None and _node_text(then) == _node_text(els):
        # both ways do the same (e.g. a close loop comparing a box's value)
        then.stmts = stmts + then.stmts
        return then
    return Node(stmts, cond=cond, then=then, els=els)


def _node_text(n):
    out = [ir.fmt_stmt(s) for s in n.stmts]
    if n.cond is not None:
        out.append("if " + fmt_expr(n.cond))
        out.append(_node_text(n.then) if n.then else "-")
        out.append(_node_text(n.els) if n.els else "-")
    elif isinstance(n.outcome, Next):
        out.append("-> %r" % (n.outcome.state.key(),))
    elif isinstance(n.outcome, Ret):
        out.append("ret " + fmt_multi(n.outcome.values))
    return "\n".join(out)


class Stepper:
    def __init__(self, lf):
        self.lf = lf

    def run_once(self, state, facts, lost, decisions, tprefix):
        lf = self.lf
        lf.out = []
        lf.tcount = 0
        lf.temp_prefix = tprefix
        lf.tab_written = {}
        sc = lf.restore(state, facts, lost)
        it = LiftInterp(lf)
        it.decisions = list(decisions)
        it.loop_sub = state.sub
        inner = Scope(sc)
        sub = None
        try:
            try:
                it.exec_block(lf.vm.loop_body, inner)
                oc = "next"
            except ContinueSig:
                oc = "next"
            except BreakSig:
                it.exec_block(lf.vm.after, sc)
                oc = ("ret", Multi([]))
        except ReturnSig as r:
            oc = ("ret", r.values)
        except LoopSig as ls:
            oc, sub = "next", ls.sub
        if oc == "next":
            lf.prune_copies(it)
            lf.scrub(sc)
            return it, Next(lf.snapshot(sc, sub))
        m = oc[1] if isinstance(oc[1], Multi) else Multi([oc[1]])
        items = []
        tail = m.tail
        for i, x in enumerate(m.items):
            if isinstance(x, Spread) and i == len(m.items) - 1 and tail is None:
                items += [lf.as_expr(y) for y in x.m.items]
                tail = x.m.tail
            else:
                items.append(lf.value_of(x) if not isinstance(x, SymList) else x)
        lf.prune_copies(it, items)
        return it, Ret(Multi(items, tail))

    def step(self, state, facts, lost, tprefix):
        paths = []
        todo = [[]]
        reads, writes = set(), None
        while todo:
            dec = todo.pop()
            it, oc = self.run_once(state, facts, lost, dec, tprefix)
            reads |= self.lf.step_reads
            writes = set(self.lf.written_now) if writes is None else writes & self.lf.written_now
            if len(paths) > 128:
                raise Unsupported("too many paths in one instruction")
            taken = [d[3] for d in it.dlog]
            for j in range(len(dec), len(taken)):
                todo.append(taken[:j] + [not taken[j]])
            paths.append((taken, it.dlog, list(self.lf.out), oc))
        self.lf.record_use(state.pc, reads, writes or set())
        return build_tree(paths, 0, 0)


def _next_states(node, out):
    if node is None:
        return
    if node.cond is not None:
        _next_states(node.then, out)
        _next_states(node.els, out)
    elif isinstance(node.outcome, Next):
        out.append(node.outcome.state)


class Program:
    def __init__(self, source, dump_json):
        import luauast
        self.source = source
        self.root = luauast.parse(source)
        self.funcs = ast_functions(self.root)
        self.vms = {}
        for mk, interp in instrument.find_vms(self.root):
            self.vms[mk["location"]] = VMModel(mk, interp)
        self.dump = Dump(dump_json, self.funcs)
        g = LTable()
        for lib in ("bit32", "string", "table", "math", "buffer"):
            t = LTable()
            for nm in list(S.CONCRETE) + ["table.pack", "table.unpack", "table.move", "table.create"]:
                if nm.startswith(lib + "."):
                    t.set(nm.split(".", 1)[1].encode(), Builtin(nm))
            g.set(lib.encode(), t)
        for nm in ("select", "unpack", "getfenv", "setfenv", "tonumber", "setmetatable"):
            g.set(nm.encode(), Builtin(nm))
        self.globals = g
        self.stats = {"functions": 0, "errors": 0, "fallbacks": 0}
        self.tbl_counter = 0
        self.tbl_stmts = {}     # table id -> IR statements that build it
        self.tbl_deps = {}      # table id -> tables stored into it
        self.tbl_used = set()
        self.carry_of = {}      # VM -> interpreter locals carried between instructions
        # protos of ironbrew1's environment check (CheckResult): the only
        # ones with the check's modulus among their constants
        self.check_protos = {i for i, c in enumerate(self.dump.caps)
                             if any(isinstance(v, LTable) and CHECK_MODULUS in v.h.values()
                                    for v in c["vars"].values())}
        self.tab_carry_of = {}

    def new_table_id(self):
        self.tbl_counter += 1
        return self.tbl_counter

    def used_table(self, t):
        if TBLID in t.h:
            self.tbl_used.add(t.h[TBLID])

    def dead_statements(self):
        """IR statements of tables built here that nothing ever read (the
        obfuscator's opaque-predicate tables): ids of the statements"""
        used = set(self.tbl_used)
        todo = list(used)
        while todo:
            n = todo.pop()
            for d in self.tbl_deps.get(n, ()):
                if d not in used:
                    used.add(d)
                    todo.append(d)
        dead = set()
        for n, sts in self.tbl_stmts.items():
            if n not in used:
                dead |= {id(x) for x in sts}
        return dead

    def walk(self, ci, uplist, limit=MAX_STATES):
        """(entry key, [(key, node)], lifter) of capture ci.

        Sparse conditional constant propagation over the instruction graph:
        every state is stepped with the register facts that hold on all its
        incoming edges (meet at joins); when they shrink it is stepped again.
        Facts decide the obfuscator's opaque predicates and keep the VM's own
        bookkeeping values (constant table, caches) concrete."""
        lf = ProtoLifter(self, ci, uplist)
        passes = 0
        for _ in range(MAX_RESTARTS):
            lf.new_carry = False
            lf.pc_use = {}
            lf.boxes, lf.top, lf.iters, lf.facts, lf.lost = {}, None, {}, {}, frozenset()
            s0 = lf.initial_state()
            lf.base_tabs_ids = {id(t) for t, _ in lf.base_tabs.values()}
            st = Stepper(lf)
            k0 = s0.key()
            states = {k0: s0}
            facts_in = {k0: ({}, frozenset())}
            nodes = {}
            sid = {}
            first = []
            work = [k0]
            inwork = {k0}
            steps = 0
            restart = False
            while work:
                k = work.pop()
                inwork.discard(k)
                s = states[k]
                fa, lo = facts_in[k]
                if os.environ.get("DEVIRT_FACTS") == str(s.pc):
                    print("-- facts at %s: %s lost %s %s" % (s.pc, {r: _keyval(v) for r, v in sorted(fa.items(), key=repr)},
                                                          sorted(lo, key=repr), ("boxes", s.boxes, "vals", s.vals, "tabs", s.tabs)), file=sys.stderr)
                steps += 1
                if steps > limit * 4 or len(first) > limit:
                    raise Unsupported("state limit (%d instruction states)" % limit)
                try:
                    # (temp names per state, not per step: a state stepped again
                    # must name its calls as before, successors refer to them)
                    node = st.step(s, fa, lo, "%s_%d_" % (s.pc, sid.setdefault(k, len(sid) + 1)))
                except Unsupported as e:
                    if os.environ.get("DEVIRT_TB"):
                        import traceback
                        traceback.print_exc()
                    node = Node([], outcome=None)
                    node.error = "%s, function %d" % (e, ci)
                if lf.new_carry:
                    restart = True
                    break
                if k not in nodes:
                    first.append(k)
                nodes[k] = node
                nxt = []
                _next_states(node, nxt)
                for ns in reversed(nxt):
                    nk = ns.key()
                    if nk not in facts_in:
                        states[nk] = ns
                        facts_in[nk] = (ns.facts, ns.lost)
                    else:
                        of, ol = facts_in[nk]
                        mf, ml = meet_facts(of, ns.facts, ol, ns.lost, lf.nregs, self)
                        if len(mf) == len(of) and ml == ol:
                            continue
                        facts_in[nk] = (mf, ml)
                    if nk not in inwork:
                        work.append(nk)
                        inwork.add(nk)
            if os.environ.get("DEVIRT_STATS"):
                print("-- walk cap %d: %d steps, %d states, restart=%s" % (ci, steps, len(first), restart),
                      file=sys.stderr)
            if not restart and passes < 1:
                # walk again, telling states apart only by the carried
                # locals live at their pc (micro-op temporaries, the
                # multiple-result top, ... stay behind with stale values)
                passes += 1
                lf.live = lf.liveness(nodes)
                continue
            if not restart:
                order = [(k, nodes[k]) for k in first]
                if lf.entry_out:
                    # an entry block of its own: the prologue runs once, even
                    # when the first instruction is a loop head
                    ek = ("E", 0)
                    order.insert(0, (ek, Node(list(lf.entry_out), outcome=Next(s0))))
                    return ek, order, lf
                return k0, order, lf
        raise Unsupported("the interpreter state kept growing (restarts)")


def prune(order, dead):
    """drop statements of unused tables and runtime closures from the walk"""
    def drop(st):
        if id(st) in dead:
            return True
        return isinstance(st, Assign) and isinstance(st.value, ClosureExpr) and getattr(st.value, "runtime", False)

    def walk(n):
        if n is None:
            return
        n.stmts = [x for x in n.stmts if not drop(x)]
        walk(n.then)
        walk(n.els)
    for _, node in order:
        walk(node)


class FunctionLifter:
    def __init__(self, prog):
        self.prog = prog
        self.lifting = set()
        self.memo = {}

    def lift(self, ci, uplist, upnames, depth=0):
        prog = self.prog
        prog.stats["functions"] += 1
        self.lifting.add(ci)
        try:
            k0, order, lf = prog.walk(ci, uplist)
            prune(order, prog.dead_statements())
            forloops.rewrite(order)
            me = sys.modules[__name__]
            prefix = "r" if depth == 0 else "r%d_" % depth
            lines, params, nerr, fallbacks = backend.lower(
                k0, order, me, None, prefix, upnames,
                lambda x, names: self.closure(x, names, depth))
            prog.stats["errors"] += nerr
            prog.stats["fallbacks"] += fallbacks
            return lines, params
        finally:
            self.lifting.discard(ci)

    def closure(self, c, parent_names, depth):
        import codegen as CG
        ci = c.proto
        if ci in self.lifting:
            return CG.FuncE(["function(...) --[[ recursive function ]] end"])
        capnames = getattr(c, "capnames", {})
        upnames = {}
        kinds = getattr(c, "kinds", {})
        for i, e in enumerate(c.upvals, 1):
            if isinstance(kinds.get(i), tuple):
                continue        # (a literal: the child uses the value, it captures nothing)
            if isinstance(e, MaybeBox):
                upnames[i] = capnames.get(e.reg, "nil")
            elif isinstance(e, Reg):
                upnames[i] = capnames.get(e.n, "nil")
            elif isinstance(e, Upval):
                upnames[i] = parent_names.get(("up", e.idx), "upv%d" % e.idx)
            else:
                upnames[i] = "nil"
        key = (ci, depth, tuple(sorted(upnames.items())), tuple(sorted(getattr(c, "kinds", {}).items())))
        if key in self.memo:
            lines, params = self.memo[key]
        else:
            try:
                lines, params = self.lift(ci, UpList(getattr(c, "kinds", {})), upnames, depth + 1)
            except Unsupported as ex:
                lines, params = ["error(\"devirt: could not lift closure: %s\")" % str(ex).replace("\"", "'")], ["..."]
            self.memo[key] = (lines, params)
        f = CG.FuncE(["function(%s)" % ", ".join(params)] + ["\t" + ln for ln in lines] + ["end"])
        f.captures = set(upnames.values())
        return f


# back end options: registers holding a literal are Luau compiler/obfuscator
# temps (idioms.inline_const_locals)
INLINE_CONST_LOCALS = True

# the IR names the back end looks up on its module parameter
from ir import (IRStmt, Outcome, Crash, ForPrep, fmt_stmt, fmt_node, fmt_tail, fmt_const)  # noqa: E402,F401


def main_proto(prog):
    """The script's main function: the first closure made."""
    return 0


def lift_program(source, dump_json):
    prog = Program(source, dump_json)
    fl = FunctionLifter(prog)
    lines, params = fl.lift(main_proto(prog), UpList(), {})
    text = "\n".join(lines)
    return text, prog


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("source")
    ap.add_argument("dump")
    ap.add_argument("--raw", type=int, help="print the instruction graph of capture N")
    ap.add_argument("--out")
    a = ap.parse_args()
    src = open(a.source, encoding="latin-1").read()
    d = json.load(open(a.dump))

    def go():
        if a.raw is not None:
            prog = Program(src, d)
            k0, order, lf = prog.walk(a.raw, UpList())
            code = LiftInterp(lf).eval(lf.vm.loop_body[0]["values"][0]["expr"], lf.cscope)
            for k, node in order:
                ins = code.get(k[1]) if isinstance(code, LTable) else None
                print("-- pc %s   %s" % (k[1], fmt_any(ins)[:200]))
                if getattr(node, "error", None):
                    print("   ERROR " + node.error)
                for ln in ir.fmt_node(node, "   "):
                    print(ln)
            return
        text, prog = lift_program(src, d)
        text = backend.finish_text(backend.polish(text))
        if a.out:
            with open(a.out, "w", encoding="utf-8", newline="\n") as f:
                f.write(text + "\n")
        else:
            sys.stdout.buffer.write((text + "\n").encode("utf-8"))
        print("[*] %r" % prog.stats, file=sys.stderr)
    backend.run_big_stack(go)


if __name__ == "__main__":
    main()
