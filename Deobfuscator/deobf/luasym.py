"""
Symbolic Luau interpreter over luau-ast JSON, used by devirt.py to lift
Luraph VM instructions.

The devirtualizer runs one iteration of the *real* dispatch loop per VM
instruction: operand arrays and helpers are concrete (captured at runtime),
registers are symbolic. Concrete code (instruction decoders, the if-tree that
selects the handler) just runs; symbolic values build IR expressions, and a
branch on a symbolic condition forks the run (see Interp.run_paths).

Values:
  None, bool, int/float, bytes (Lua strings), LTable, Builtin, LuaFunc, Buf
  and symbolic IR expressions (Expr subclasses, see below).
"""
import math
import struct


class Unsupported(Exception):
    pass


# --------------------------------------------------------------------------
# concrete values

class LTable:
    __slots__ = ("h", "tid", "meta")

    def __init__(self, h=None, tid=None):
        self.h = h if h is not None else {}
        self.tid = tid
        self.meta = None

    def get(self, k):
        return self.h.get(norm_key(k))

    def set(self, k, v):
        k = norm_key(k)
        if v is None:
            self.h.pop(k, None)
        else:
            self.h[k] = v

    def length(self):
        n = 0
        while (n + 1) in self.h:
            n += 1
        return n

    def __repr__(self):
        return "LTable#%s" % (self.tid if self.tid is not None else id(self))


class Buf:
    __slots__ = ("data",)

    def __init__(self, data):
        self.data = bytearray(data)


class Builtin:
    __slots__ = ("name", "fn")

    def __init__(self, name, fn=None):
        self.name = name
        self.fn = fn

    def __repr__(self):
        return "Builtin(%s)" % self.name


class LuaFunc:
    """A Lua function from the source AST (VM helpers such as e:G3)."""
    __slots__ = ("node", "env")

    def __init__(self, node, env):
        self.node = node
        self.env = env


def norm_key(k):
    if isinstance(k, float) and k == int(k) and not math.isinf(k):
        return int(k)
    if isinstance(k, Expr):
        raise Unsupported("symbolic table key on a concrete table: %r" % (k,))
    return k


# --------------------------------------------------------------------------
# symbolic IR expressions

class Expr:
    """Symbolic value. Subclasses are plain data; `pure` means evaluation has
    no side effects (calls are always materialized into temps)."""
    pure = True

    def __repr__(self):
        return "<%s %s>" % (type(self).__name__, self.__dict__)


class Const(Expr):
    def __init__(self, v):
        self.v = v


class Reg(Expr):
    def __init__(self, n):
        self.n = n

    def __eq__(self, o):
        return isinstance(o, Reg) and o.n == self.n

    def __hash__(self):
        return hash(("reg", self.n))


class Pseudo(Expr):
    """Hidden VM state (numeric/generic for-loop variables), per loop depth."""

    def __init__(self, name, depth):
        self.name, self.depth = name, depth

    def __eq__(self, o):
        return isinstance(o, Pseudo) and (o.name, o.depth) == (self.name, self.depth)

    def __hash__(self):
        return hash(("pseudo", self.name, self.depth))


class Global(Expr):
    def __init__(self, name):
        self.name = name


class Upval(Expr):
    def __init__(self, idx):
        self.idx = idx

    def __eq__(self, o):
        return isinstance(o, Upval) and o.idx == self.idx

    def __hash__(self):
        return hash(("upv", self.idx))


class Index(Expr):
    def __init__(self, obj, key):
        self.obj, self.key = obj, key


class Bin(Expr):
    def __init__(self, op, a, b):
        self.op, self.a, self.b = op, a, b


class Un(Expr):
    def __init__(self, op, a):
        self.op, self.a = op, a


class IfExp(Expr):
    def __init__(self, c, a, b):
        self.c, self.a, self.b = c, a, b


class TempVal(Expr):
    """i-th value (1-based) of a materialized call."""

    def __init__(self, t, i):
        self.t, self.i = t, i

    def __eq__(self, o):
        return isinstance(o, TempVal) and (o.t, o.i) == (self.t, self.i)

    def __hash__(self):
        return hash(("tv", self.t, self.i))


class Vararg(Expr):
    """i-th value of the function's varargs (1-based)."""

    def __init__(self, i):
        self.i = i


class NewTable(Expr):
    def __init__(self, items=None):
        self.items = items or []   # [(key or None, value)]


class ClosureExpr(Expr):
    def __init__(self, proto, upvals):
        self.proto, self.upvals = proto, upvals


# multi-value tails (a variable number of values)
class Multi:
    """Values of a call / vararg expression: fixed prefix + optional tail."""

    def __init__(self, items, tail=None):
        self.items, self.tail = list(items), tail

    def first(self):
        if self.items:
            return self.items[0]
        if self.tail is not None:
            return self.tail.at(1)
        return None


class TempTail:
    def __init__(self, t, start=1):
        self.t, self.start = t, start

    def at(self, i):
        return TempVal(self.t, self.start + i - 1)

    def drop(self, k):
        return TempTail(self.t, self.start + k)


class VarargTail:
    def __init__(self, start=1):
        self.start = start

    def at(self, i):
        return Vararg(self.start + i - 1)

    def drop(self, k):
        return VarargTail(self.start + k)


class SymList:
    """A table built by table.pack / {...} whose length may be symbolic:
    positions 1..len(items) are known, then `tail` (a Multi tail) follows
    starting at position len(items)+1 + shift. `n` field reads give Len."""

    def __init__(self, items, tail=None, nkey=None):
        self.items = list(items)
        self.tail = tail
        self.nkey = nkey
        self.extra = {}

    def count_expr(self):
        if self.tail is None:
            return len(self.items)
        return Bin("Add", TailCount(self.tail), len(self.items)) if self.items else TailCount(self.tail)


class TailCount(Expr):
    def __init__(self, tail):
        self.tail = tail


# --------------------------------------------------------------------------
# special runtime objects of the VM closure

class RegFile:
    """The VM register array: z[n] reads Reg(n), writes emit assignments."""


class EnvTable:
    """getfenv() of the script: indexing gives globals."""


class UpContainer:
    """Stand-in for the table an upvalue box points into (box[4] in Luraph's
    {[4]=registers,[7]=index} boxes): any index of it is the upvalue."""

    def __init__(self, idx):
        self.idx = idx


# --------------------------------------------------------------------------
# control-flow signals

class BreakSig(Exception):
    pass


class ContinueSig(Exception):
    pass


class ReturnSig(Exception):
    def __init__(self, values):
        self.values = values


class YieldSig(Exception):
    """Reached a dispatch loop (instruction boundary)."""

    def __init__(self, node):
        self.node = node


class NeedDecision(Exception):
    pass


# --------------------------------------------------------------------------

def truthy(v):
    return not (v is None or v is False)


def is_sym(v):
    return isinstance(v, Expr)


def lua_num(v):
    if isinstance(v, bool) or v is None:
        return None
    if isinstance(v, (int, float)):
        return v
    if isinstance(v, bytes):
        try:
            s = v.decode("latin-1").strip()
            return int(s, 0) if s.lower().startswith(("0x", "-0x")) else float(s)
        except ValueError:
            return None
    return None


def fix_int(x):
    if isinstance(x, float) and x.is_integer() and abs(x) < 2 ** 63:
        return int(x)
    return x


def arith(op, a, b):
    if op == "Add":
        return fix_int(a + b)
    if op == "Sub":
        return fix_int(a - b)
    if op == "Mul":
        return fix_int(a * b)
    if op == "Div":
        if b == 0:
            if a == 0:
                return float("nan")
            return math.copysign(float("inf"), a) * (1 if not (isinstance(b, float) and math.copysign(1, b) < 0) else -1)
        return fix_int(a / b)
    if op == "FloorDiv":
        if b == 0:
            return arith("Div", a, b)
        return fix_int(math.floor(a / b)) if isinstance(a, float) or isinstance(b, float) else a // b
    if op == "Mod":
        if b == 0:
            return float("nan")
        if isinstance(a, int) and isinstance(b, int):
            return a % b
        r = math.fmod(a, b)
        if r != 0 and (r < 0) != (b < 0):
            r += b
        return fix_int(r)
    if op == "Pow":
        return fix_int(float(a) ** float(b))
    raise Unsupported(op)


def u32(x):
    return int(x) & 0xFFFFFFFF


def _bit(name):
    def band(*a):
        r = 0xFFFFFFFF
        for x in a:
            r &= u32(x)
        return r

    def bor(*a):
        r = 0
        for x in a:
            r |= u32(x)
        return r

    def bxor(*a):
        r = 0
        for x in a:
            r ^= u32(x)
        return r

    def lshift(x, n):
        n = int(n)
        return 0 if abs(n) >= 32 else (u32(x) << n) & 0xFFFFFFFF if n >= 0 else u32(x) >> -n

    def rshift(x, n):
        n = int(n)
        return 0 if abs(n) >= 32 else u32(x) >> n if n >= 0 else (u32(x) << -n) & 0xFFFFFFFF

    def arshift(x, n):
        x, n = u32(x), int(n)
        if x & 0x80000000:
            x -= 1 << 32
        return u32(x >> min(n, 31)) if n >= 0 else lshift(x, -n)

    def lrotate(x, n):
        x, n = u32(x), int(n) % 32
        return ((x << n) | (x >> (32 - n))) & 0xFFFFFFFF

    def rrotate(x, n):
        return lrotate(x, -int(n))

    def bnot(x):
        return (~u32(x)) & 0xFFFFFFFF

    def extract(x, f, w=1):
        return (u32(x) >> int(f)) & ((1 << int(w)) - 1)

    def replace(x, v, f, w=1):
        m = ((1 << int(w)) - 1) << int(f)
        return (u32(x) & ~m | ((u32(v) << int(f)) & m)) & 0xFFFFFFFF

    def btest(*a):
        return band(*a) != 0

    def countlz(x):
        x = u32(x)
        return 32 - x.bit_length()

    def countrz(x):
        x = u32(x)
        return 32 if x == 0 else (x & -x).bit_length() - 1

    return locals()[name]


BIT32 = ["band", "bor", "bxor", "bnot", "lshift", "rshift", "arshift", "lrotate", "rrotate",
         "extract", "replace", "btest", "countlz", "countrz"]


def _buf_fns():
    fmt = {"i8": "<b", "u8": "<B", "i16": "<h", "u16": "<H", "i32": "<i", "u32": "<I", "f32": "<f", "f64": "<d"}
    out = {}
    for k, f in fmt.items():
        size = struct.calcsize(f)

        def rd(b, off, f=f, size=size):
            return fix_int(struct.unpack_from(f, b.data, int(off))[0])

        def wr(b, off, v, f=f, k=k):
            if k.startswith(("u", "i")):
                bits = struct.calcsize(f) * 8
                v = int(v) & ((1 << bits) - 1)
                if k.startswith("i") and v >= 1 << (bits - 1):
                    v -= 1 << bits
            struct.pack_into(f, b.data, int(off), v)
        out["buffer.read" + k] = rd
        out["buffer.write" + k] = wr
    out["buffer.len"] = lambda b: len(b.data)
    out["buffer.tostring"] = lambda b: bytes(b.data)
    out["buffer.fromstring"] = lambda s: Buf(s)
    out["buffer.create"] = lambda n: Buf(bytes(int(n)))
    out["buffer.readstring"] = lambda b, o, n: bytes(b.data[int(o):int(o) + int(n)])
    return out


def _str_byte(s, i=1, j=None):
    n = len(s)
    i = int(i)
    j = i if j is None else int(j)
    if i < 0:
        i += n + 1
    if j < 0:
        j += n + 1
    i = max(i, 1)
    j = min(j, n)
    return Multi(list(s[i - 1:j]))


def _str_sub(s, i=1, j=-1):
    n = len(s)
    i, j = int(i), int(j)
    if i < 0:
        i = max(n + i + 1, 1)
    elif i == 0:
        i = 1
    if j < 0:
        j = n + j + 1
    elif j > n:
        j = n
    return s[i - 1:j] if i <= j else b""


CONCRETE = {"string.byte": _str_byte, "string.sub": _str_sub, "string.len": lambda s: len(s),
            "string.char": lambda *a: bytes(int(x) for x in a),
            "string.rep": lambda s, n, sep=b"": sep.join([s] * int(n)),
            "math.floor": lambda x: fix_int(math.floor(x)), "math.ceil": lambda x: fix_int(math.ceil(x)),
            "math.abs": lambda x: abs(x), "math.max": lambda *a: max(a), "math.min": lambda *a: min(a),
            "tonumber": lambda x, b=None: lua_num(x) if b is None else int(x.decode(), int(b))}
for _n in BIT32:
    CONCRETE["bit32." + _n] = _bit(_n)
CONCRETE.update(_buf_fns())


# --------------------------------------------------------------------------

class Scope:
    """Local variables keyed by declaration location (luau-ast)."""
    __slots__ = ("vars", "parent")

    def __init__(self, parent=None):
        self.vars = {}
        self.parent = parent

    def lookup(self, key):
        s = self
        while s is not None:
            if key in s.vars:
                return s
            s = s.parent
        return None


class Interp:
    """Evaluates AST nodes. Hooks for the VM-specific parts:
      special[decl_key] -> "sink" (reads nil, writes ignored) or
                           ("pseudo", name) (for-loop state, see devirt)
      emit(stmt)        -> IR statement sink
      new_temp()        -> temp id for a materialized call
    """

    def __init__(self, lifter):
        self.L = lifter
        self.decisions = []
        self.dpos = 0
        self.dlog = []          # (decision index, emitted count at that time, cond)
        self.seen = {}          # id(cond) -> (cond, decision) in this run
        self.steps = 0

    # ---- decisions (forking on symbolic conditions)
    def decide(self, cond):
        if self.dpos < len(self.decisions):
            d = self.decisions[self.dpos]
        else:
            d = True
            self.decisions.append(d)
        self.dlog.append((self.dpos, len(self.L.out), cond, d))
        self.dpos += 1
        return d

    def cond_true(self, v):
        if is_sym(v):
            # the same value tested again (`c and x or y` tests c twice):
            # the same decision, not a fork into an infeasible combination
            base, neg = v, False
            while isinstance(base, Un) and base.op == "Not":
                base, neg = base.a, not neg
            hit = self.seen.get(id(base))
            if hit is not None and hit[0] is base:
                return hit[1] != neg
            self.L.check_decision(v)
            d = self.decide(v)
            self.seen[id(base)] = (base, d != neg)
            return d
        if isinstance(v, (SymList, Multi, RegFile, EnvTable, UpContainer)):
            return True
        return truthy(v)

    # ---- variables
    def getvar(self, scope, local):
        key = local["location"]
        sp = self.L.special.get(key)
        if sp is not None:
            return self.L.special_get(sp, self)
        s = scope.lookup(key)
        if s is None:
            raise Unsupported("unbound local %s@%s" % (local["name"], key))
        return s.vars[key]

    def setvar(self, scope, local, v):
        key = local["location"]
        sp = self.L.special.get(key)
        if sp is not None:
            self.L.special_set(sp, v, self)
            return
        s = scope.lookup(key)
        if s is None:
            raise Unsupported("assign to unbound local %s" % local["name"])
        s.vars[key] = v

    # ---- statements
    def exec_block(self, stmts, scope):
        for st in stmts:
            self.exec_stmt(st, scope)

    def exec_stmt(self, st, scope):
        self.steps += 1
        if self.steps > 2_000_000:
            raise Unsupported("interpreter step limit")
        t = st["type"]
        if t == "AstStatBlock":
            self.exec_block(st["body"], Scope(scope))
        elif t == "AstStatLocal":
            vals = self.eval_list(st["values"], scope, len(st["vars"]))
            for v, x in zip(st["vars"], vals):
                scope.vars[v["location"]] = x
                sp = self.L.special.get(v["location"])
                if sp is not None and sp[0] == "reg":
                    # a register local (LPH_JIT) is assigned where it is declared
                    self.L.special_set(sp, x, self)
        elif t == "AstStatAssign":
            # evaluate targets' object/key first, then values (Lua order is unspecified; fine)
            targets = [self.lvalue(v, scope) for v in st["vars"]]
            vals = self.eval_list(st["values"], scope, len(targets))
            if len(targets) > 1 and hasattr(self.L, "parallel_values"):
                vals = self.L.parallel_values(targets, vals, self)
            for tg, x in zip(targets, vals):
                self.assign(tg, x, scope)
        elif t == "AstStatCompoundAssign":
            tg = self.lvalue(st["var"], scope)
            cur = self.read_lvalue(tg, scope)
            self.assign(tg, self.binop(st["op"], cur, self.eval(st["value"], scope)), scope)
        elif t == "AstStatIf":
            if self.cond_true(self.eval(st["condition"], scope)):
                self.exec_block(st["thenbody"]["body"], Scope(scope))
            elif st.get("elsebody") is not None:
                e = st["elsebody"]
                if e["type"] == "AstStatIf":
                    self.exec_stmt(e, scope)
                else:
                    self.exec_block(e["body"], Scope(scope))
        elif t == "AstStatWhile":
            if self.L.is_dispatch(st):
                raise YieldSig(st)
            n = 0
            while self.cond_true(self.eval(st["condition"], scope)):
                n += 1
                if n > 100000:
                    raise Unsupported("while loop limit")
                try:
                    self.exec_block(st["body"]["body"], Scope(scope))
                except BreakSig:
                    break
                except ContinueSig:
                    continue
        elif t == "AstStatRepeat":
            n = 0
            while True:
                n += 1
                if n > 100000:
                    raise Unsupported("repeat loop limit")
                inner = Scope(scope)
                try:
                    self.exec_block(st["body"]["body"], inner)
                except BreakSig:
                    break
                except ContinueSig:
                    pass
                if self.cond_true(self.eval(st["condition"], inner)):
                    break
        elif t == "AstStatFor":
            a = self.eval(st["from"], scope)
            b = self.eval(st["to"], scope)
            c = self.eval(st["step"], scope) if st.get("step") else 1
            if a is None or b is None or c is None:
                raise Unsupported("numeric for with unknown bounds")
            if is_sym(a) or is_sym(b) or is_sym(c):
                raise Unsupported("numeric for with symbolic bounds")
            if not all(isinstance(x, (int, float)) and not isinstance(x, bool) for x in (a, b, c)):
                raise Unsupported("numeric for with non-numeric bounds")
            if c == 0:
                raise Unsupported("numeric for with zero step")
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
                i = fix_int(i + c)
        elif t == "AstStatForIn":
            vals = self.eval_list(st["values"], scope, 3)
            f, s, ctl = vals
            n = 0
            while True:
                n += 1
                if n > 1000000:
                    raise Unsupported("for-in limit")
                r = self.call(f, [s, ctl])
                r = self.adjust(r, len(st["vars"]))
                if r[0] is None:
                    break
                if is_sym(r[0]):
                    raise Unsupported("symbolic generic for")
                ctl = r[0]
                inner = Scope(scope)
                for v, x in zip(st["vars"], r):
                    inner.vars[v["location"]] = x
                try:
                    self.exec_block(st["body"]["body"], inner)
                except BreakSig:
                    break
                except ContinueSig:
                    pass
        elif t == "AstStatReturn":
            raise ReturnSig(self.eval_multi_list(st["list"], scope))
        elif t == "AstStatBreak":
            raise BreakSig()
        elif t == "AstStatContinue":
            raise ContinueSig()
        elif t == "AstStatExpr":
            e = st["expr"]
            if e["type"] != "AstExprCall":
                raise Unsupported("expression statement " + e["type"])
            self.eval_call(e, scope, stat=True)
        elif t == "AstStatLocalFunction":
            scope.vars[st["name"]["location"]] = LuaFunc(st["func"], scope)
        elif t == "AstStatFunction":
            raise Unsupported("function statement")
        else:
            raise Unsupported("statement " + t)

    # ---- lvalues: ("local", node) | ("index", obj, key)
    def lvalue(self, node, scope):
        t = node["type"]
        if t == "AstExprLocal":
            return ("local", node["local"])
        if t == "AstExprIndexExpr":
            return ("index", self.eval(node["expr"], scope), self.eval(node["index"], scope))
        if t == "AstExprIndexName":
            return ("index", self.eval(node["expr"], scope), node["index"].encode("latin-1"))
        if t == "AstExprGlobal":
            return ("global", node["global"])
        raise Unsupported("lvalue " + t)

    def read_lvalue(self, tg, scope):
        if tg[0] == "local":
            return self.getvar(scope, tg[1])
        if tg[0] == "index":
            return self.index(tg[1], tg[2])
        raise Unsupported("read global lvalue")

    def assign(self, tg, v, scope):
        if tg[0] == "local":
            self.setvar(scope, tg[1], v)
        elif tg[0] == "index":
            self.newindex(tg[1], tg[2], v)
        elif hasattr(self.L, "set_global"):
            # "Hardcode Globals": a handler stores a script global directly
            self.L.set_global(tg[1], v)
        else:
            raise Unsupported("assignment to global %s in VM code" % tg[1])

    # ---- expressions
    def eval_list(self, nodes, scope, want):
        """Evaluate an expression list adjusted to `want` values."""
        vals = self.eval_multi_list(nodes, scope)
        return self.adjust(vals, want)

    def adjust(self, m, want):
        if not isinstance(m, Multi):
            m = Multi([m])
        out = list(m.items[:want])
        i = 1
        while len(out) < want:
            if m.tail is not None:
                out.append(m.tail.at(i))
                i += 1
            else:
                out.append(None)
        return out

    def eval_multi_list(self, nodes, scope):
        items = []
        tail = None
        for i, n in enumerate(nodes):
            if i == len(nodes) - 1 and n["type"] in ("AstExprCall", "AstExprVarargs"):
                m = self.eval_multi(n, scope)
                items += m.items
                tail = m.tail
            else:
                items.append(self.eval(n, scope))
        return Multi(items, tail)

    def eval_multi(self, node, scope):
        t = node["type"]
        if t == "AstExprCall":
            r = self.eval_call(node, scope)
            return r if isinstance(r, Multi) else Multi([r])
        if t == "AstExprVarargs":
            return self.L.varargs(scope)
        return Multi([self.eval(node, scope)])

    def eval(self, node, scope):
        t = node["type"]
        if t == "AstExprConstantNumber":
            return fix_int(node["value"])
        if t == "AstExprConstantString":
            return node["value"].encode("latin-1")
        if t == "AstExprConstantBool":
            return node["value"]
        if t == "AstExprConstantNil":
            return None
        if t == "AstExprLocal":
            return self.getvar(scope, node["local"])
        if t == "AstExprGlobal":
            return self.L.global_value(node["global"])
        if t == "AstExprGroup":
            return self.eval(node["expr"], scope)
        if t == "AstExprIndexExpr":
            obj = self.eval(node["expr"], scope)
            if obj is None:
                raise Unsupported("index nil @%s" % node["location"])
            return self.index(obj, self.eval(node["index"], scope))
        if t == "AstExprIndexName":
            obj = self.eval(node["expr"], scope)
            if obj is None:
                raise Unsupported("index nil @%s" % node["location"])
            return self.index(obj, node["index"].encode("latin-1"))
        if t == "AstExprCall":
            r = self.eval_call(node, scope)
            return r.first() if isinstance(r, Multi) else r
        if t == "AstExprVarargs":
            return self.L.varargs(scope).first()
        if t == "AstExprBinary":
            op = node["op"]
            # symbolic operands fork (short-circuit evaluation is control flow)
            if op == "And":
                a = self.eval(node["left"], scope)
                return self.eval(node["right"], scope) if self.cond_true(a) else a
            if op == "Or":
                a = self.eval(node["left"], scope)
                return a if self.cond_true(a) else self.eval(node["right"], scope)
            return self.binop(op, self.eval(node["left"], scope), self.eval(node["right"], scope))
        if t == "AstExprUnary":
            return self.unop(node["op"], self.eval(node["expr"], scope))
        if t == "AstExprIfElse":
            c = self.eval(node["condition"], scope)
            return self.eval(node["trueExpr"] if self.cond_true(c) else node["falseExpr"], scope)
        if t == "AstExprTable":
            return self.table_ctor(node, scope)
        if t == "AstExprFunction":
            return LuaFunc(node, scope)
        if t == "AstExprTypeAssertion":
            return self.eval(node["expr"], scope)
        raise Unsupported("expression " + t)

    def table_ctor(self, node, scope):
        items = node["items"]
        # {...} and {f()} build SymLists when a tail is involved
        tb = LTable()
        pos = 1
        symbolic = False
        for i, it in enumerate(items):
            if it["kind"] == "item":
                last = i == len(items) - 1
                if last and it["value"]["type"] in ("AstExprCall", "AstExprVarargs"):
                    m = self.eval_multi(it["value"], scope)
                    if m.tail is not None:
                        lst = SymList([tb.h.get(k) for k in range(1, pos)] + m.items, m.tail,
                                      nkey=None)
                        return lst
                    for v in m.items:
                        tb.set(pos, v)
                        pos += 1
                else:
                    tb.set(pos, self.eval(it["value"], scope))
                    pos += 1
            else:
                k = it["key"]["value"].encode("latin-1") if it["kind"] == "record" else self.eval(it["key"], scope)
                v = self.eval(it["value"], scope)
                if is_sym(k):
                    symbolic = True
                tb.set(k, v)
        if symbolic:
            raise Unsupported("symbolic key in table constructor")
        return tb

    # ---- operators
    def binop(self, op, a, b):
        if is_sym(a) or is_sym(b) or isinstance(a, (SymList, RegFile)) or isinstance(b, (SymList, RegFile)):
            return self.L.sym_binop(op, a, b)
        if op in ("Add", "Sub", "Mul", "Div", "FloorDiv", "Mod", "Pow"):
            x, y = lua_num(a), lua_num(b)
            if x is None or y is None:
                raise Unsupported("arith on %r %r" % (a, b))
            return arith(op, x, y)
        if op == "Concat":
            def s(v):
                if isinstance(v, bytes):
                    return v
                if isinstance(v, (int, float)):
                    return fmt_num(v).encode()
                raise Unsupported("concat")
            return s(a) + s(b)
        if op == "CompareEq":
            return lua_eq(a, b)
        if op == "CompareNe":
            return not lua_eq(a, b)
        if op in ("CompareLt", "CompareLe", "CompareGt", "CompareGe"):
            if not ((isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool)
                     and not isinstance(b, bool)) or (isinstance(a, bytes) and isinstance(b, bytes))):
                raise Unsupported("compare %r %r" % (a, b))
            return {"CompareLt": a < b, "CompareLe": a <= b, "CompareGt": a > b, "CompareGe": a >= b}[op]
        raise Unsupported("binop " + op)

    def unop(self, op, a):
        if is_sym(a) or isinstance(a, SymList):
            return self.L.sym_unop(op, a)
        if op == "Not":
            return not truthy(a)
        if op == "Minus":
            x = lua_num(a)
            if x is None:
                raise Unsupported("unm")
            return fix_int(-x)
        if op == "Len":
            if isinstance(a, bytes):
                return len(a)
            if isinstance(a, LTable):
                return a.length()
            raise Unsupported("len of %r" % (a,))
        raise Unsupported("unop " + op)

    # ---- indexing
    def index(self, obj, key):
        return self.L.index(obj, key, self)

    def newindex(self, obj, key, v):
        self.L.newindex(obj, key, v, self)

    # ---- calls
    def eval_call(self, node, scope, stat=False):
        fnode = node["func"]
        if node.get("self"):
            obj = self.eval(fnode["expr"], scope)
            fn = self.index(obj, fnode["index"].encode("latin-1"))
            args = self.eval_multi_list(node["args"], scope)
            args = Multi([obj] + args.items, args.tail)
        else:
            fn = self.eval(fnode, scope)
            args = self.eval_multi_list(node["args"], scope)
        return self.call(fn, args, stat=stat)

    def call(self, fn, args, stat=False):
        if not isinstance(args, Multi):
            args = Multi(list(args))
        if isinstance(fn, LuaFunc):
            return self.call_lua(fn, args)
        if isinstance(fn, Builtin):
            return self.L.call_builtin(fn, args, self, stat)
        return self.L.call_symbolic(fn, args, self, stat)

    def call_lua(self, fn, args):
        node = fn.node
        scope = Scope(fn.env)
        vals = self.adjust(args, len(node["args"]))
        for a, v in zip(node["args"], vals):
            scope.vars[a["location"]] = v
        if node.get("vararg"):
            rest = Multi(args.items[len(node["args"]):], args.tail.drop(max(0, len(node["args"]) - len(args.items)))
                         if args.tail is not None else None)
            scope.vars["..."] = rest
        try:
            self.exec_block(node["body"]["body"], scope)
        except ReturnSig as r:
            return r.values
        return Multi([])


def lua_eq(a, b):
    if isinstance(a, bool) or isinstance(b, bool):
        return a is b
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        return a == b
    if isinstance(a, bytes) and isinstance(b, bytes):
        return a == b
    return a is b


def fmt_num(v):
    if isinstance(v, int):
        return str(v)
    if v != v:
        return "nan"
    if math.isinf(v):
        return "inf" if v > 0 else "-inf"
    if v.is_integer() and abs(v) < 1e15:
        return str(int(v))
    r = "%.14g" % v
    if float(r) != v:
        r = "%.17g" % v
    return r
