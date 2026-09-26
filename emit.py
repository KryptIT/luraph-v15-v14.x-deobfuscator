"""Pretty-print IR back to Lua source."""
import math
import re
from ir import *

KW = {'and', 'break', 'do', 'else', 'elseif', 'end', 'false', 'for', 'function', 'if', 'in', 'local', 'nil',
      'not', 'or', 'repeat', 'return', 'then', 'true', 'until', 'while', 'goto'}
BIN = {'or': (1, 1), 'and': (2, 2), '<': (3, 3), '>': (3, 3), '<=': (3, 3), '>=': (3, 3), '~=': (3, 3),
       '==': (3, 3), '..': (5, 4), '+': (6, 6), '-': (6, 6), '*': (7, 7), '/': (7, 7), '%': (7, 7), '^': (10, 9)}
UN = 8
LEVEL = {'or': 1, 'and': 2, '<': 3, '>': 3, '<=': 3, '>=': 3, '~=': 3, '==': 3, '..': 4, '+': 5, '-': 5,
         '*': 6, '/': 6, '%': 6, '^': 8}


def prec_of(e):
    if isinstance(e, EBin):
        return LEVEL[e.op]
    if isinstance(e, EUn):
        return 7
    if isinstance(e, EConst) and isinstance(e.v, float) and (e.v < 0 or (e.v == 0 and math.copysign(1, e.v) < 0)):
        return 7
    return 100


def is_ident(b):
    if not isinstance(b, bytes):
        return False
    try:
        s = b.decode('ascii')
    except UnicodeDecodeError:
        return False
    return re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', s) is not None and s not in KW


def lua_str(b):
    out = ['"']
    for i, c in enumerate(b):
        ch = chr(c)
        if ch == '"':
            out.append('\\"')
        elif ch == '\\':
            out.append('\\\\')
        elif ch == '\n':
            out.append('\\n')
        elif ch == '\r':
            out.append('\\r')
        elif ch == '\t':
            out.append('\\t')
        elif 32 <= c < 127:
            out.append(ch)
        else:
            nxt = b[i + 1:i + 2]
            if nxt.isdigit():
                out.append('\\%03d' % c)
            else:
                out.append('\\%d' % c)
    out.append('"')
    return ''.join(out)


def lua_num(v):
    if v != v:
        return '(0/0)'
    if v == math.inf:
        return 'math.huge'
    if v == -math.inf:
        return '-math.huge'
    if float(v).is_integer() and abs(v) < 1e16:
        return str(int(v))
    r = repr(float(v))
    return r


class Printer:
    def __init__(self, funcs, namer=None):
        self.funcs = funcs            # pid -> Function
        self.namer = namer or (lambda e: None)
        self.lines = []
        self.upstack = []             # stack of capture tuples for EUpval resolution

    # ---------------- expressions
    def name_of(self, e):
        n = self.namer(e)
        if n is not None:
            return n
        if isinstance(e, EVar):
            return e.name
        if isinstance(e, EReg):
            return 'r%s' % (e.n,)
        if isinstance(e, EUpval):
            if self.upstack and self.upstack[-1] is not None and e.k < len(self.upstack[-1]):
                cap = self.upstack[-1][e.k]
                saved = self.upstack.pop()
                try:
                    return self.expr(cap)
                finally:
                    self.upstack.append(saved)
            return 'upval%d' % e.k
        if isinstance(e, ETemp):
            return 't%d' % e.id
        if isinstance(e, EGlobal):
            return e.name.decode('latin-1') if is_ident(e.name) else '_G[%s]' % lua_str(e.name)
        return None

    def expr(self, e, prec=0, indent=0):
        n = self.name_of(e) if isinstance(e, (EVar, EReg, EUpval, ETemp, EGlobal)) else None
        if n is not None:
            return n
        if isinstance(e, EConst):
            v = e.v
            if v is None:
                return 'nil'
            if v is True:
                return 'true'
            if v is False:
                return 'false'
            if isinstance(v, bytes):
                return lua_str(v)
            return lua_num(v)
        if isinstance(e, EIndex):
            obj = self.prefix(e.obj, indent)
            if isinstance(e.key, EConst) and is_ident(e.key.v):
                return obj + '.' + e.key.v.decode()
            return obj + '[' + self.expr(e.key, 0, indent) + ']'
        if isinstance(e, ECall):
            args = list(e.args)
            f = e.fn
            if isinstance(f, EIndex) and isinstance(f.key, EConst) and is_ident(f.key.v) and args and \
                    args[0] == f.obj and isinstance(f.obj, (EVar, EReg, EUpval, EGlobal)):
                return self.prefix(f.obj, indent) + ':' + f.key.v.decode() + '(' + \
                    ', '.join(self.expr(a, 0, indent) for a in args[1:]) + ')'
            return self.prefix(f, indent) + '(' + ', '.join(self.expr(a, 0, indent) for a in args) + ')'
        if isinstance(e, EBin):
            p = LEVEL[e.op]
            right_assoc = e.op in ('..', '^')
            ls = self.expr(e.a, 0, indent)
            rs = self.expr(e.b, 0, indent)
            lpv, rpv = prec_of(e.a), prec_of(e.b)
            if lpv < p or (lpv == p and right_assoc):
                ls = '(' + ls + ')'
            if rpv < p or (rpv == p and not right_assoc):
                rs = '(' + rs + ')'
            return ls + ' ' + e.op + ' ' + rs
        if isinstance(e, EUn):
            op = e.op
            inner = self.expr(e.a, 0, indent)
            if prec_of(e.a) < 7:
                inner = '(' + inner + ')'
            if op == 'not':
                return 'not ' + inner
            if op == '-' and inner.startswith('-'):
                return '- ' + inner
            return op + inner
        if isinstance(e, EVararg):
            return '...'
        if isinstance(e, EVarargAt):
            return '(select(%s, ...))' % (lua_num(e.k + 1) if isinstance(e.k, (int, float)) else self.expr(e.k))
        if isinstance(e, ETable):
            if not e.items:
                return '{}'
            parts = []
            pos = 1
            for k, v in e.items:
                if k is None or (isinstance(k, EConst) and k.v == pos):
                    parts.append(self.expr(v, 0, indent))
                    pos += 1
                elif isinstance(k, EConst) and is_ident(k.v):
                    parts.append('%s = %s' % (k.v.decode(), self.expr(v, 0, indent)))
                else:
                    parts.append('[%s] = %s' % (self.expr(k, 0, indent), self.expr(v, 0, indent)))
            return '{' + ', '.join(parts) + '}'
        if isinstance(e, EClosure):
            return self.function_expr(e, indent, None)
        if isinstance(e, EMultiReg):
            return 'r%d --[[...]]' % e.base
        if isinstance(e, EResult):
            return 'result%d_%s' % (e.id, e.k)
        return '--[[?%r]]' % (e,)

    def prefix(self, e, indent):
        s = self.expr(e, 0, indent)
        if isinstance(e, (EVar, EReg, EUpval, ETemp, EIndex, ECall)) or \
                (isinstance(e, EGlobal) and is_ident(e.name)):
            return s
        return '(' + s + ')'

    def params(self, fn):
        if getattr(fn, 'param_names', None) is not None:
            ps = [self.expr(v) for v in fn.param_names]
        else:
            ps = [self.expr(EReg(i)) for i in range(fn.nparams)]
        if fn.is_vararg:
            ps.append('...')
        return ', '.join(ps)

    def function_expr(self, e, indent, name, local=False):
        fn = self.funcs[e.pid]
        self.upstack.append(e.caps)
        saved = self.lines
        self.lines = []
        self.block(fn.body, indent + 1)
        body = self.lines
        self.lines = saved
        self.upstack.pop()
        head = 'function%s(%s)' % ((' ' + name) if name else '', self.params_for(fn, e))
        if local:
            head = 'local ' + head
        pad = '    ' * indent
        if not body:
            return head + ' end'
        return head + '\n' + '\n'.join(body) + '\n' + pad + 'end'

    def params_for(self, fn, e):
        self.upstack.append(e.caps)
        try:
            return self.params(fn)
        finally:
            self.upstack.pop()

    # ---------------- statements
    def emit(self, indent, text):
        self.lines.append('    ' * indent + text)

    def block(self, stmts, indent):
        prev_compound = None
        for s in stmts:
            compound = isinstance(s, (SIf, SWhile, SNumFor, SGenFor)) or (
                isinstance(s, SAssign) and len(s.values) == 1 and isinstance(s.values[0], EClosure))
            if prev_compound is not None and (compound or prev_compound) and indent == 0:
                self.lines.append('')
            self.stmt(s, indent)
            prev_compound = compound

    def stmt(self, s, indent):
        if isinstance(s, SAssign):
            if len(s.targets) == 1 and len(s.values) == 1 and isinstance(s.values[0], EClosure):
                t = s.targets[0]
                nm = None
                if isinstance(t, (EVar, EReg)) or (isinstance(t, EGlobal) and is_ident(t.name)):
                    nm = self.expr(t, 0, indent)
                elif isinstance(t, EIndex) and isinstance(t.key, EConst) and is_ident(t.key.v) and \
                        isinstance(t.obj, (EVar, EGlobal, EIndex)):
                    nm = self.expr(t, 0, indent)
                if nm is not None:
                    self.emit(indent, self.function_expr(s.values[0], indent, nm, local=s.local))
                    return
            lhs = ', '.join(self.expr(t, 0, indent) for t in s.targets)
            vals = s.values
            if s.local and len(vals) == 1 and isinstance(vals[0], EConst) and vals[0].v is None:
                self.emit(indent, 'local ' + lhs)
                return
            rhs = ', '.join(self.value(v, indent) for v in vals)
            self.emit(indent, ('local ' if s.local else '') + lhs + (' = ' + rhs if vals else ''))
        elif isinstance(s, SLocal):
            self.emit(indent, 'local ' + ', '.join(self.expr(v) for v in s.vars))
        elif isinstance(s, SCall):
            self.emit(indent, self.expr(s.call, 0, indent))
        elif isinstance(s, SIf):
            self.emit(indent, 'if ' + self.expr(s.cond, 0, indent) + ' then')
            self.block(s.then, indent + 1)
            els = s.els
            while len(els) == 1 and isinstance(els[0], SIf):
                e = els[0]
                self.emit(indent, 'elseif ' + self.expr(e.cond, 0, indent) + ' then')
                self.block(e.then, indent + 1)
                els = e.els
            if els:
                self.emit(indent, 'else')
                self.block(els, indent + 1)
            self.emit(indent, 'end')
        elif isinstance(s, SWhile):
            self.emit(indent, 'while ' + self.expr(s.cond, 0, indent) + ' do')
            self.block(s.body, indent + 1)
            self.emit(indent, 'end')
        elif isinstance(s, SNumFor):
            h = 'for %s = %s, %s' % (self.expr(s.var), self.expr(s.init, 0, indent), self.expr(s.limit, 0, indent))
            if s.step is not None and not (isinstance(s.step, EConst) and s.step.v == 1):
                h += ', ' + self.expr(s.step, 0, indent)
            self.emit(indent, h + ' do')
            self.block(s.body, indent + 1)
            self.emit(indent, 'end')
        elif isinstance(s, SGenFor):
            self.emit(indent, 'for %s in %s do' % (', '.join(self.expr(v) for v in s.vars),
                                                   ', '.join(self.expr(x, 0, indent) for x in s.exprs)))
            self.block(s.body, indent + 1)
            self.emit(indent, 'end')
        elif isinstance(s, SReturn):
            self.emit(indent, ('return ' + ', '.join(self.expr(v, 0, indent) for v in s.values)).rstrip())
        elif isinstance(s, SBreak):
            self.emit(indent, 'break')
        elif isinstance(s, SContinue):
            self.emit(indent, 'goto continue -- (continue)')
        elif isinstance(s, SGoto):
            self.emit(indent, 'goto label_%d' % s.target)
        elif isinstance(s, SComment):
            self.emit(indent, '-- ' + s.text)
        else:
            self.emit(indent, '-- ?? %r' % (s,))

    def value(self, v, indent):
        s = self.expr(v, 0, indent)
        if isinstance(v, EBin) and v.op in ('==', '~=', '<', '<=', '>', '>=', 'and', 'or') or \
                (isinstance(v, EUn) and v.op == 'not'):
            return '(' + s + ')'
        return s
