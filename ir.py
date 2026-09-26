"""Intermediate representation for lifted code (expressions + statements)."""


class E:
    """Base expression. Fields stored in tuple self.f; structural equality."""
    __slots__ = ('f',)
    names = ()

    def __init__(self, *f):
        self.f = tuple(f)

    def __eq__(self, o):
        return type(self) is type(o) and self.f == o.f

    def __hash__(self):
        return hash((type(self).__name__, self.f))

    def __getattr__(self, n):
        try:
            return self.f[type(self).names.index(n)]
        except ValueError:
            raise AttributeError(n)

    def __repr__(self):
        return '%s%r' % (type(self).__name__, self.f)

    def children(self):
        for x in self.f:
            if isinstance(x, E):
                yield x
            elif isinstance(x, tuple):
                for y in x:
                    if isinstance(y, E):
                        yield y
                    elif isinstance(y, tuple):
                        for z in y:
                            if isinstance(z, E):
                                yield z

    def map(self, fn):
        """Rebuild with fn applied to direct child expressions."""
        def m(x):
            if isinstance(x, E):
                return fn(x)
            if isinstance(x, tuple):
                return tuple(m(y) for y in x)
            return x
        return type(self)(*[m(x) for x in self.f])


def mk(name, *fields):
    cls = type(name, (E,), {'__slots__': (), 'names': fields})
    return cls


EConst = mk('EConst', 'v')
EReg = mk('EReg', 'n')
EGlobal = mk('EGlobal', 'name')
EUpval = mk('EUpval', 'k')
EIndex = mk('EIndex', 'obj', 'key')
ECall = mk('ECall', 'fn', 'args')
EBin = mk('EBin', 'op', 'a', 'b')
EUn = mk('EUn', 'op', 'a')
EClosure = mk('EClosure', 'pid', 'caps')
EVararg = mk('EVararg')
EVarargAt = mk('EVarargAt', 'k')
ETable = mk('ETable', 'items')            # items: tuple of (key_or_None, value)
EResult = mk('EResult', 'id', 'k')        # k-th result of materialized call id
ETemp = mk('ETemp', 'id')
EMultiReg = mk('EMultiReg', 'base')       # all values from register base onward (multret)
ECount = mk('ECount', 'src', 'off')       # symbolic "number of values of src" + off
EIter = mk('EIter', 'start')              # symbolic loop index over a multi range
EVar = mk('EVar', 'name')                 # final named variable (after naming pass)
EFunc = mk('EFunc', 'fn')                 # lifted function object (Function) for printing


def walk(e):
    """Pre-order walk of expression tree."""
    yield e
    for c in e.children():
        yield from walk(c)


def subst(e, fn):
    """Bottom-up substitution: fn(expr) -> expr or None (keep)."""
    e2 = e.map(lambda c: subst(c, fn))
    r = fn(e2)
    return e2 if r is None else r


# ------------------------------------------------------------------ statements
class S:
    pass


class SAssign(S):
    def __init__(self, targets, values, local=False):
        self.targets, self.values, self.local = list(targets), list(values), local

    def __repr__(self):
        return 'SAssign(%r=%r)' % (self.targets, self.values)


class SCall(S):
    def __init__(self, call):
        self.call = call

    def __repr__(self):
        return 'SCall(%r)' % (self.call,)


class SIf(S):
    def __init__(self, cond, then, els=None):
        self.cond, self.then, self.els = cond, then, els or []

    def __repr__(self):
        return 'SIf(%r)' % (self.cond,)


class SWhile(S):
    def __init__(self, cond, body):
        self.cond, self.body = cond, body


class SNumFor(S):
    def __init__(self, var, init, limit, step, body):
        self.var, self.init, self.limit, self.step, self.body = var, init, limit, step, body


class SGenFor(S):
    def __init__(self, vars, exprs, body):
        self.vars, self.exprs, self.body = list(vars), list(exprs), body


class SReturn(S):
    def __init__(self, values):
        self.values = list(values)


class SBreak(S):
    pass


class SContinue(S):
    pass


class SGoto(S):
    def __init__(self, target):
        self.target = target


class SLocal(S):
    """Plain declaration without value: local a, b"""
    def __init__(self, vars):
        self.vars = list(vars)


class SComment(S):
    def __init__(self, text):
        self.text = text


class Function:
    def __init__(self, pid, nparams, body, is_vararg=False):
        self.pid, self.nparams, self.body, self.is_vararg = pid, nparams, body, is_vararg
        self.upnames = {}   # upvalue index -> EVar in parent (filled by naming)
        self.parent = None
        self.captures = None


def stmt_exprs(s):
    """Expressions directly evaluated by a statement (not nested blocks)."""
    if isinstance(s, SAssign):
        r = list(s.values)
        for t in s.targets:
            if isinstance(t, EIndex):
                r.extend([t.obj, t.key])
        return r
    if isinstance(s, SCall):
        return [s.call]
    if isinstance(s, SIf):
        return [s.cond]
    if isinstance(s, SWhile):
        return [s.cond]
    if isinstance(s, SNumFor):
        return [x for x in (s.init, s.limit, s.step) if x is not None]
    if isinstance(s, SGenFor):
        return list(s.exprs)
    if isinstance(s, SReturn):
        return list(s.values)
    return []


def stmt_blocks(s):
    if isinstance(s, SIf):
        return [s.then, s.els]
    if isinstance(s, (SWhile, SNumFor, SGenFor)):
        return [s.body]
    return []


def map_stmt_exprs(s, fn):
    """Apply fn to each top-level expression slot of statement (in place)."""
    if isinstance(s, SAssign):
        s.values = [fn(v) for v in s.values]
        nt = []
        for t in s.targets:
            if isinstance(t, EIndex):
                t = EIndex(fn(t.obj), fn(t.key))
            nt.append(t)
        s.targets = nt
    elif isinstance(s, SCall):
        s.call = fn(s.call)
    elif isinstance(s, (SIf, SWhile)):
        s.cond = fn(s.cond)
    elif isinstance(s, SNumFor):
        s.init, s.limit = fn(s.init), fn(s.limit)
        s.step = fn(s.step) if s.step is not None else None
    elif isinstance(s, SGenFor):
        s.exprs = [fn(x) for x in s.exprs]
    elif isinstance(s, SReturn):
        s.values = [fn(v) for v in s.values]


def all_stmts(block):
    for s in block:
        yield s
        for b in stmt_blocks(s):
            yield from all_stmts(b)
