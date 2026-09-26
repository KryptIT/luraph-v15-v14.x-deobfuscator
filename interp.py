"""Tree-walking Lua 5.1 interpreter with hooks for symbolic execution of VM handlers."""
import math
from luaparse import Node
from ir import E, EConst, EReg, EGlobal, EUpval, EIndex, ECall, EBin, EUn, EVarargAt, EResult, ECount, EIter


class LuaError(Exception):
    pass


class Unsupported(Exception):
    pass


class StepLimit(Exception):
    pass


class LuaTable:
    __slots__ = ('d', 'meta', 'n', 'multi')

    def __init__(self):
        self.d = {}
        self.meta = None
        self.n = 0
        self.multi = None     # (position, MultiMarker) for symbolic multi-value tail

    def rawget(self, k):
        if isinstance(k, float) and k.is_integer():
            k = int(k)
        v = self.d.get(k)
        if v is None and self.multi is not None and isinstance(k, int) and k >= self.multi[0]:
            return self.multi[1].nth(k - self.multi[0] + 1)
        return v

    def rawset(self, k, v):
        if isinstance(k, float) and k.is_integer():
            k = int(k)
        if k is None:
            raise LuaError('table index is nil')
        if v is None:
            self.d.pop(k, None)
            if isinstance(k, int) and 1 <= k <= self.n:
                self.n = k - 1
        else:
            self.d[k] = v
            if isinstance(k, int) and k == self.n + 1:
                n = k
                while (n + 1) in self.d:
                    n += 1
                self.n = n

    def length(self):
        return self.n


class LuaFunction:
    __slots__ = ('node', 'scope', 'name')

    def __init__(self, node, scope, name=None):
        self.node, self.scope, self.name = node, scope, name


class Builtin:
    __slots__ = ('fn', 'name')

    def __init__(self, fn, name):
        self.fn, self.name = fn, name

    def __repr__(self):
        return 'builtin:' + self.name


class MultiMarker:
    """Stands for 'all remaining values' produced by a symbolic source (call id / varargs)."""
    __slots__ = ('src',)

    def __init__(self, src):
        self.src = src

    def nth(self, k):
        if self.src == 'vararg':
            return EVarargAt(k - 1)
        return EResult(self.src, k)

    def single(self):
        return self.nth(1)


class Scope:
    __slots__ = ('vars', 'parent')

    def __init__(self, parent=None):
        self.vars = {}
        self.parent = parent

    def find(self, name):
        s = self
        while s is not None:
            if name in s.vars:
                return s
            s = s.parent
        return None


# ---- role objects used when symbolically executing VM handlers
class SymStack:
    pass


class SymEnv:
    pass


class SymUpv:
    pass


class SymVarargs:
    pass


def is_sym(v):
    return isinstance(v, (E, MultiMarker))


def lift(v):
    if isinstance(v, MultiMarker):
        return v.single()
    if isinstance(v, E):
        return v
    if v is None or isinstance(v, (bool, float, int, bytes)):
        if isinstance(v, int) and not isinstance(v, bool):
            v = float(v)
        return EConst(v)
    if isinstance(v, LuaTable) and v.meta is None and v.multi is None:
        from ir import ETable
        items = []
        for k in sorted([k for k in v.d if isinstance(k, int)]):
            items.append((EConst(float(k)), lift(v.d[k])))
        for k, x in v.d.items():
            if not isinstance(k, int):
                items.append((lift(k), lift(x)))
        return ETable(tuple(items))
    raise Unsupported('cannot lift %r' % (type(v),))


def num2str(v):
    if v != v:
        return b'nan' if not math.copysign(1, v) < 0 else b'-nan'
    if v in (math.inf, -math.inf):
        return b'inf' if v > 0 else b'-inf'
    if float(v).is_integer() and abs(v) < 1e15:
        return str(int(v)).encode()
    s = '%.14g' % v
    return s.encode()


def tonum(v):
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        return float(v)
    if isinstance(v, bytes):
        s = v.strip().decode('latin-1')
        try:
            if s.lower().startswith(('0x', '-0x')):
                neg = s.startswith('-')
                r = float(int(s[3:] if neg else s[2:], 16))
                return -r if neg else r
            return float(s)
        except ValueError:
            return None
    return None


class Ret(Exception):
    """Used only across python frames when needed."""


BREAK = ('break',)


class Interp:
    def __init__(self):
        self.G = LuaTable()
        self.string_meta = None
        self.call_hook = None      # fn(func, args) -> list | None
        self.index_hook = None     # fn(table, key) -> None
        self.ctx = None            # symbolic context (decide / record)
        self.steps = 0
        self.max_steps = 50_000_000

    # ------------------------------------------------------------ helpers
    def tick(self):
        self.steps += 1
        if self.steps > self.max_steps:
            raise StepLimit()

    def truth(self, v):
        if v is None or v is False:
            return False
        if is_sym(v):
            if self.ctx is None:
                raise Unsupported('symbolic condition without context')
            return self.ctx.decide(lift(v))
        return True

    def tostr(self, v):
        if isinstance(v, bytes):
            return v
        if isinstance(v, (int, float)) and not isinstance(v, bool):
            return num2str(float(v))
        if v is None:
            return b'nil'
        if v is True:
            return b'true'
        if v is False:
            return b'false'
        if isinstance(v, LuaTable):
            mm = self.getmeta(v, b'__tostring')
            if mm is not None:
                return self.call(mm, [v])[0]
            return b'table: 0x%08x' % (id(v) & 0xffffffff)
        return b'function: 0x%08x' % (id(v) & 0xffffffff)

    def getmeta(self, v, ev):
        m = v.meta if isinstance(v, LuaTable) else (self.string_meta if isinstance(v, bytes) else None)
        if m is None:
            return None
        return m.rawget(ev)

    # ------------------------------------------------------------ table access
    def index(self, o, k):
        if isinstance(o, LuaTable):
            if self.index_hook is not None:
                self.index_hook(o, k)
            if is_sym(k):
                raise Unsupported('symbolic key into concrete table')
            v = o.rawget(k)
            if v is None and o.meta is not None:
                h = o.meta.rawget(b'__index')
                if h is not None:
                    if isinstance(h, LuaTable):
                        return self.index(h, k)
                    r = self.call(h, [o, k])
                    return r[0] if r else None
            return v
        if isinstance(o, bytes):
            return self.index(self.string_meta.rawget(b'__index'), k)
        if isinstance(o, SymStack):
            return EReg(self._regkey(k))
        if isinstance(o, SymEnv):
            if not isinstance(k, bytes):
                raise Unsupported('env key')
            return EGlobal(k)
        if isinstance(o, SymUpv):
            return EUpval(int(k))
        if isinstance(o, SymVarargs):
            if isinstance(k, EIter):
                return EVarargAt(k)
            return EVarargAt(int(k))
        if is_sym(o):
            return EIndex(lift(o), lift(k))
        raise LuaError('attempt to index a %s value' % self.type(o).decode())

    def _regkey(self, k):
        if isinstance(k, (int, float)) and not isinstance(k, bool):
            return int(k)
        if isinstance(k, EIter):
            return k
        if isinstance(k, EBin) and isinstance(k.a, EIter):
            return k
        raise Unsupported('register key %r' % (k,))

    def setindex(self, o, k, v):
        if isinstance(o, LuaTable):
            if o.meta is not None and o.rawget(k) is None:
                h = o.meta.rawget(b'__newindex')
                if h is not None:
                    if isinstance(h, LuaTable):
                        return self.setindex(h, k, v)
                    self.call(h, [o, k, v])
                    return
            if is_sym(k):
                raise Unsupported('symbolic key store')
            o.rawset(k, v)
            return
        if isinstance(o, SymStack):
            self.ctx.record(('set', EReg(self._regkey(k)), self._val(v)))
            return
        if isinstance(o, SymEnv):
            self.ctx.record(('set', EGlobal(k), self._val(v)))
            return
        if isinstance(o, SymUpv):
            self.ctx.record(('set', EUpval(int(k)), self._val(v)))
            return
        if is_sym(o):
            self.ctx.record(('set', EIndex(lift(o), lift(k)), self._val(v)))
            return
        raise LuaError('attempt to index a %s value' % self.type(o).decode())

    def _val(self, v):
        if self.ctx is not None and hasattr(self.ctx, 'value_hook'):
            r = self.ctx.value_hook(v)
            if r is not None:
                return r
        return lift(v)

    def type(self, v):
        if v is None:
            return b'nil'
        if isinstance(v, bool):
            return b'boolean'
        if isinstance(v, (int, float)):
            return b'number'
        if isinstance(v, bytes):
            return b'string'
        if isinstance(v, LuaTable):
            return b'table'
        if isinstance(v, (LuaFunction, Builtin)):
            return b'function'
        return b'userdata'

    # ------------------------------------------------------------ arithmetic
    def arith(self, op, a, b):
        if is_sym(a) or is_sym(b):
            a2, b2 = a, b
            if isinstance(a2, ECount) and isinstance(b2, (int, float)) and not isinstance(b2, bool):
                if op == '+':
                    return ECount(a2.src, a2.off + b2)
                if op == '-':
                    return ECount(a2.src, a2.off - b2)
            if isinstance(b2, ECount) and isinstance(a2, (int, float)) and not isinstance(a2, bool) and op == '+':
                return ECount(b2.src, b2.off + a2)
            if isinstance(a2, EIter) or isinstance(b2, EIter):
                return EBin(op, lift(a2), lift(b2))
            return EBin(op, lift(a2), lift(b2))
        x, y = tonum(a), tonum(b)
        if x is None or y is None:
            mm = self.getmeta(a, b'__' + {'+': b'add', '-': b'sub', '*': b'mul', '/': b'div', '%': b'mod', '^': b'pow'}[op]) \
                if isinstance(a, LuaTable) else None
            if mm is None and isinstance(b, LuaTable):
                mm = self.getmeta(b, b'__' + {'+': b'add', '-': b'sub', '*': b'mul', '/': b'div', '%': b'mod', '^': b'pow'}[op])
            if mm is not None:
                return self.call(mm, [a, b])[0]
            raise LuaError('attempt to perform arithmetic on a %s value' % self.type(a if x is None else b).decode())
        if op == '+':
            return x + y
        if op == '-':
            return x - y
        if op == '*':
            return x * y
        if op == '/':
            if y == 0:
                if x == 0 or x != x:
                    return math.nan
                return math.copysign(math.inf, x) * math.copysign(1, y)
            return x / y
        if op == '%':
            if y == 0:
                return math.nan
            if math.isinf(y):
                return x if (x >= 0) == (y > 0) else y
            return x - math.floor(x / y) * y
        if op == '^':
            try:
                return math.pow(x, y)
            except OverflowError:
                return math.inf
            except ValueError:
                return math.nan
        raise LuaError(op)

    def concat(self, a, b):
        if is_sym(a) or is_sym(b):
            return EBin('..', lift(a), lift(b))
        if isinstance(a, (bytes, int, float)) and not isinstance(a, bool) and \
                isinstance(b, (bytes, int, float)) and not isinstance(b, bool):
            return self.tostr(a) + self.tostr(b)
        mm = self.getmeta(a, b'__concat') or self.getmeta(b, b'__concat')
        if mm is not None:
            return self.call(mm, [a, b])[0]
        raise LuaError('attempt to concatenate a %s value' % self.type(a if not isinstance(a, (bytes, float, int)) else b).decode())

    def eq(self, a, b):
        if is_sym(a) or is_sym(b):
            return EBin('==', lift(a), lift(b))
        if isinstance(a, bool) or isinstance(b, bool):
            return a is b
        if isinstance(a, (int, float)) and isinstance(b, (int, float)):
            return a == b
        if type(a) is not type(b):
            return False
        if isinstance(a, bytes):
            return a == b
        if a is b:
            return True
        if isinstance(a, LuaTable) and isinstance(b, LuaTable):
            mm = self.getmeta(a, b'__eq')
            if mm is not None and mm is self.getmeta(b, b'__eq'):
                return self.truth(self.call(mm, [a, b])[0])
        return a is b

    def lt(self, a, b):
        if is_sym(a) or is_sym(b):
            return EBin('<', lift(a), lift(b))
        if isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool) and not isinstance(b, bool):
            return a < b
        if isinstance(a, bytes) and isinstance(b, bytes):
            return a < b
        mm = self.getmeta(a, b'__lt')
        if mm is not None:
            return self.truth(self.call(mm, [a, b])[0])
        raise LuaError('attempt to compare %s with %s' % (self.type(a).decode(), self.type(b).decode()))

    def le(self, a, b):
        if is_sym(a) or is_sym(b):
            return EBin('<=', lift(a), lift(b))
        if isinstance(a, (int, float)) and isinstance(b, (int, float)) and not isinstance(a, bool) and not isinstance(b, bool):
            return a <= b
        if isinstance(a, bytes) and isinstance(b, bytes):
            return a <= b
        mm = self.getmeta(a, b'__le')
        if mm is not None:
            return self.truth(self.call(mm, [a, b])[0])
        raise LuaError('attempt to compare %s with %s' % (self.type(a).decode(), self.type(b).decode()))

    def length(self, v):
        if isinstance(v, bytes):
            return float(len(v))
        if isinstance(v, LuaTable):
            mm = self.getmeta(v, b'__len')
            if mm is not None:
                return self.call(mm, [v])[0]
            if v.multi is not None:
                raise Unsupported('length of symbolic multi table')
            return float(v.length())
        if is_sym(v):
            return EUn('#', lift(v))
        raise LuaError('attempt to get length of a %s value' % self.type(v).decode())

    # ------------------------------------------------------------ calls
    def call(self, f, args):
        self.tick()
        if self.call_hook is not None:
            r = self.call_hook(f, args)
            if r is not None:
                return r
        if isinstance(f, LuaFunction):
            return self.run_function(f, args)
        if isinstance(f, Builtin):
            r = f.fn(self, args)
            return [] if r is None else r
        if is_sym(f):
            if self.ctx is None:
                raise Unsupported('symbolic call')
            return self.ctx.symcall(f, args)
        if isinstance(f, LuaTable):
            mm = self.getmeta(f, b'__call')
            if mm is not None:
                return self.call(mm, [f] + list(args))
        raise LuaError('attempt to call a %s value' % self.type(f).decode())

    def run_function(self, f, args):
        node = f.node
        sc = Scope(f.scope)
        params = node.a
        for i, p in enumerate(params):
            v = args[i] if i < len(args) else None
            if isinstance(v, MultiMarker):
                v = v.single()
            sc.vars[p] = v
        if node.b:
            sc.vars['...'] = list(args[len(params):])
        r = self.exec_block(node.c, sc)
        if r is not None and r[0] == 'ret':
            return r[1]
        return []

    # ------------------------------------------------------------ expressions
    def lookup(self, name, scope):
        s = scope.find(name)
        if s is not None:
            return s.vars[name]
        return self.index(self.G, name.encode())

    def assign_name(self, name, scope, v):
        s = scope.find(name)
        if s is not None:
            s.vars[name] = v
        else:
            self.setindex(self.G, name.encode(), v)

    def eval(self, n, sc):
        k = n.k
        if k == 'Num':
            return n.a
        if k == 'Str':
            return n.a
        if k == 'Name':
            v = self.lookup(n.a, sc)
            return v.single() if isinstance(v, MultiMarker) else v
        if k == 'Index':
            return self.index(self.eval(n.a, sc), self.eval(n.b, sc))
        if k == 'Call' or k == 'Method':
            r = self.evalm(n, sc)
            v = r[0] if r else None
            return v.single() if isinstance(v, MultiMarker) else v
        if k == 'Bin':
            op = n.a
            if op == 'and':
                a = self.eval(n.b, sc)
                if is_sym(a):
                    b = self.eval(n.c, sc)
                    return self._symlogic('and', a, b)
                return self.eval(n.c, sc) if self.truth(a) else a
            if op == 'or':
                a = self.eval(n.b, sc)
                if is_sym(a):
                    b = self.eval(n.c, sc)
                    return self._symlogic('or', a, b)
                return a if self.truth(a) else self.eval(n.c, sc)
            a = self.eval(n.b, sc)
            b = self.eval(n.c, sc)
            if op in ('+', '-', '*', '/', '%', '^'):
                return self.arith(op, a, b)
            if op == '..':
                return self.concat(a, b)
            if op == '==':
                return self.eq(a, b)
            if op == '~=':
                r = self.eq(a, b)
                return EUn('not', r) if is_sym(r) else not r
            if op == '<':
                return self.lt(a, b)
            if op == '>':
                return self.lt(b, a)
            if op == '<=':
                return self.le(a, b)
            if op == '>=':
                return self.le(b, a)
            raise LuaError('bad op ' + op)
        if k == 'Un':
            v = self.eval(n.b, sc)
            if n.a == 'not':
                if is_sym(v):
                    return EUn('not', lift(v))
                return not self.truth(v)
            if n.a == '-':
                if is_sym(v):
                    return EUn('-', lift(v))
                x = tonum(v)
                if x is None:
                    mm = self.getmeta(v, b'__unm')
                    if mm is not None:
                        return self.call(mm, [v])[0]
                    raise LuaError('attempt to perform arithmetic on a %s value' % self.type(v).decode())
                return -x
            if n.a == '#':
                return self.length(v)
        if k == 'Nil':
            return None
        if k == 'True':
            return True
        if k == 'False':
            return False
        if k == 'Paren':
            return self.eval(n.a, sc)
        if k == 'Vararg':
            va = self.lookup('...', sc)
            v = va[0] if va else None
            return v.single() if isinstance(v, MultiMarker) else v
        if k == 'Func':
            return LuaFunction(n, sc)
        if k == 'Table':
            t = LuaTable()
            i = 1
            items = n.a
            for idx, (kind, key, val) in enumerate(items):
                if kind == 'key':
                    kk = self.eval(key, sc)
                    self.setindex(t, kk, self.eval(val, sc))
                elif idx == len(items) - 1 and val.k in ('Call', 'Method', 'Vararg'):
                    vals = self.evalm(val, sc)
                    for v in vals:
                        if isinstance(v, MultiMarker):
                            t.multi = (i, v)
                            break
                        t.rawset(i, v)
                        i += 1
                else:
                    t.rawset(i, self.eval(val, sc))
                    i += 1
            return t
        raise LuaError('cannot eval ' + k)

    def _symlogic(self, op, a, b):
        # simplify junk opaque predicates mixed with symbolic values (condition semantics)
        if not is_sym(b):
            if op == 'or':
                return a if not (b is not None and b is not False) else True
            return a if (b is not None and b is not False) else False
        return EBin(op, lift(a), lift(b))

    def evalm(self, n, sc):
        k = n.k
        if k == 'Call':
            f = self.eval(n.a, sc)
            args = self.explist(n.b, sc)
            return self.call(f, args)
        if k == 'Method':
            o = self.eval(n.a, sc)
            f = self.index(o, n.b)
            args = self.explist(n.c, sc)
            return self.call(f, [o] + args)
        if k == 'Vararg':
            return list(self.lookup('...', sc))
        return [self.eval(n, sc)]

    def explist(self, nodes, sc):
        out = []
        for i, e in enumerate(nodes):
            if i == len(nodes) - 1 and e.k in ('Call', 'Method', 'Vararg'):
                out.extend(self.evalm(e, sc))
            else:
                out.append(self.eval(e, sc))
        return out

    # ------------------------------------------------------------ statements
    def exec_block(self, stmts, parent):
        sc = Scope(parent)
        for s in stmts:
            r = self.exec(s, sc)
            if r is not None:
                return r
        return None

    def exec(self, s, sc):
        self.tick()
        k = s.k
        if k == 'Local':
            vals = self.explist(s.b, sc) if s.b else []
            for i, nm in enumerate(s.a):
                v = vals[i] if i < len(vals) else None
                if isinstance(v, MultiMarker) and i < len(s.a) - 1:
                    # expand marker across remaining names
                    for j in range(i, len(s.a)):
                        sc.vars[s.a[j]] = v.nth(j - i + 1)
                    break
                sc.vars[nm] = v.single() if isinstance(v, MultiMarker) else v
            return None
        if k == 'Assign':
            targets = s.a
            if len(targets) == 1 and len(s.b) == 1:
                t = targets[0]
                if t.k == 'Name':
                    v = self.eval(s.b[0], sc)
                    self.assign_name(t.a, sc, v)
                else:
                    o = self.eval(t.a, sc)
                    key = self.eval(t.b, sc)
                    v = self.eval(s.b[0], sc)
                    self.setindex(o, key, v)
                return None
            refs = []
            for t in targets:
                if t.k == 'Name':
                    refs.append(('n', t.a))
                else:
                    refs.append(('i', self.eval(t.a, sc), self.eval(t.b, sc)))
            vals = self.explist(s.b, sc)
            if vals and isinstance(vals[-1], MultiMarker):
                m = vals.pop()
                j = 1
                while len(vals) < len(targets):
                    vals.append(m.nth(j))
                    j += 1
            for i, r in enumerate(refs):
                v = vals[i] if i < len(vals) else None
                if r[0] == 'n':
                    self.assign_name(r[1], sc, v)
                else:
                    self.setindex(r[1], r[2], v)
            return None
        if k == 'CallStat':
            r = self.evalm(s.a, sc)
            if self.ctx is not None and hasattr(self.ctx, 'callstat'):
                self.ctx.callstat(r)
            return None
        if k == 'If':
            for c, b in zip(s.a, s.b):
                if self.truth(self.eval(c, sc)):
                    return self.exec_block(b, sc)
            if s.c is not None:
                return self.exec_block(s.c, sc)
            return None
        if k == 'While':
            while self.truth(self.eval(s.a, sc)):
                r = self.exec_block(s.b, sc)
                if r is not None:
                    if r is BREAK:
                        break
                    return r
            return None
        if k == 'NumFor':
            a = self.eval(s.b, sc)
            b = self.eval(s.c, sc)
            c = self.eval(s.d, sc) if s.d is not None else 1.0
            if is_sym(a) or is_sym(b) or is_sym(c):
                if self.ctx is not None and hasattr(self.ctx, 'symfor'):
                    return self.ctx.symfor(self, s, sc, a, b, c)
                raise Unsupported('symbolic for')
            a, b, c = tonum(a), tonum(b), tonum(c)
            if a is None or b is None or c is None:
                raise LuaError("'for' value must be a number")
            if c == 0:
                raise LuaError("'for' step is zero")
            i = a
            while (i <= b) if c > 0 else (i >= b):
                inner = Scope(sc)
                inner.vars[s.a] = i
                r = self.exec_block(s.e, inner)
                if r is not None:
                    if r is BREAK:
                        break
                    return r
                i += c
            return None
        if k == 'GenFor':
            vals = self.explist(s.b, sc)
            f = vals[0] if vals else None
            st = vals[1] if len(vals) > 1 else None
            ctl = vals[2] if len(vals) > 2 else None
            while True:
                rs = self.call(f, [st, ctl])
                if not rs or rs[0] is None:
                    break
                ctl = rs[0]
                inner = Scope(sc)
                for i, nm in enumerate(s.a):
                    inner.vars[nm] = rs[i] if i < len(rs) else None
                r = self.exec_block(s.c, inner)
                if r is not None:
                    if r is BREAK:
                        break
                    return r
            return None
        if k == 'Repeat':
            while True:
                inner = Scope(sc)
                for st in s.a:
                    r = self.exec(st, inner)
                    if r is not None:
                        if r is BREAK:
                            return None
                        return r
                if self.truth(self.eval(s.b, inner)):
                    break
            return None
        if k == 'Do':
            return self.exec_block(s.a, sc)
        if k == 'Return':
            return ('ret', self.explist(s.a, sc))
        if k == 'Break':
            return BREAK
        if k == 'LocalFunction':
            f = LuaFunction(s.b, sc, s.a)
            sc.vars[s.a] = None
            f.scope = sc
            sc.vars[s.a] = f
            return None
        if k in ('Goto', 'Label'):
            raise Unsupported('goto')
        raise LuaError('cannot exec ' + k)
