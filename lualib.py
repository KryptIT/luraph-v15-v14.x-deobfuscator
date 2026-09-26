"""Standard library for the interpreter (pure functions only unless allow_io)."""
import math
from interp import (LuaTable, LuaFunction, Builtin, MultiMarker, LuaError, Unsupported, SymStack, SymVarargs,
                    is_sym, tonum, num2str, lift)
from ir import EReg, ECount, EMultiReg, EVararg, EIter

# ------------------------------------------------------------------ lua patterns
L_ESC = ord('%')
SPECIALS = b'^$*+?.([%-'


class MatchState:
    def __init__(self, src, pat):
        self.src, self.pat = src, pat
        self.level = 0
        self.capture = []   # list of [start, len]  len: -1 = position, -2 = unclosed
        self.depth = 0


def class_end(ms, p):
    pat = ms.pat
    if p >= len(pat):
        raise LuaError('malformed pattern')
    c = pat[p]
    p += 1
    if c == L_ESC:
        if p >= len(pat):
            raise LuaError('malformed pattern (ends with %)')
        return p + 1
    if c == ord('['):
        if p < len(pat) and pat[p] == ord('^'):
            p += 1
        while True:
            if p >= len(pat):
                raise LuaError('malformed pattern (missing ])')
            cc = pat[p]
            p += 1
            if cc == L_ESC:
                p += 1
            if p < len(pat) and pat[p] == ord(']'):
                return p + 1
            if p >= len(pat):
                raise LuaError('malformed pattern (missing ])')
    return p


def single_class(c, cl):
    ch = chr(c)
    lo = chr(cl).lower()
    if lo == 'a':
        r = ch.isalpha() and c < 128
    elif lo == 'c':
        r = c < 32 or c == 127
    elif lo == 'd':
        r = 48 <= c <= 57
    elif lo == 'g':
        r = 33 <= c <= 126
    elif lo == 'l':
        r = 97 <= c <= 122
    elif lo == 'p':
        r = (33 <= c <= 47) or (58 <= c <= 64) or (91 <= c <= 96) or (123 <= c <= 126)
    elif lo == 's':
        r = c in (32, 9, 10, 11, 12, 13)
    elif lo == 'u':
        r = 65 <= c <= 90
    elif lo == 'w':
        r = (48 <= c <= 57) or (65 <= c <= 90) or (97 <= c <= 122)
    elif lo == 'x':
        r = (48 <= c <= 57) or (65 <= c <= 70) or (97 <= c <= 102)
    else:
        return cl == c
    if chr(cl).isupper():
        r = not r
    return r


def match_class_set(ms, c, p, ec):
    pat = ms.pat
    sig = True
    p += 1
    if pat[p] == ord('^'):
        sig = False
        p += 1
    while p < ec:
        if pat[p] == L_ESC:
            p += 1
            if single_class(c, pat[p]):
                return sig
            p += 1
        elif p + 2 < ec and pat[p + 1] == ord('-'):
            if pat[p] <= c <= pat[p + 2]:
                return sig
            p += 3
        else:
            if pat[p] == c:
                return sig
            p += 1
    return not sig


def single_match(ms, s, p, ep):
    if s >= len(ms.src):
        return False
    c = ms.src[s]
    pc = ms.pat[p]
    if pc == ord('.'):
        return True
    if pc == L_ESC:
        return single_class(c, ms.pat[p + 1])
    if pc == ord('['):
        return match_class_set(ms, c, p, ep - 1)
    return pc == c


def do_match(ms, s, p):
    ms.depth += 1
    if ms.depth > 200:
        raise LuaError('pattern too complex')
    try:
        pat = ms.pat
        while True:
            if p >= len(pat):
                return s
            pc = pat[p]
            if pc == ord('('):
                if p + 1 < len(pat) and pat[p + 1] == ord(')'):
                    return start_capture(ms, s, p + 2, -1)
                return start_capture(ms, s, p + 1, -2)
            if pc == ord(')'):
                return end_capture(ms, s, p + 1)
            if pc == ord('$') and p + 1 == len(pat):
                return s if s == len(ms.src) else None
            if pc == L_ESC and p + 1 < len(pat):
                nc = pat[p + 1]
                if nc == ord('b'):
                    return match_balance(ms, s, p + 2)
                if nc == ord('f'):
                    p += 2
                    ep = class_end(ms, p)
                    prev = ms.src[s - 1] if s > 0 else 0
                    cur = ms.src[s] if s < len(ms.src) else 0
                    if (not match_class_set(ms, prev, p, ep - 1)) and match_class_set(ms, cur, p, ep - 1):
                        p = ep
                        continue
                    return None
                if 48 <= nc <= 57:
                    l = nc - ord('1')
                    st, ln = ms.capture[l]
                    cap = ms.src[st:st + ln]
                    if ms.src[s:s + len(cap)] == cap:
                        s += len(cap)
                        p += 2
                        continue
                    return None
            ep = class_end(ms, p)
            epc = pat[ep] if ep < len(pat) else None
            if epc == ord('?'):
                if single_match(ms, s, p, ep):
                    r = do_match(ms, s + 1, ep + 1)
                    if r is not None:
                        return r
                p = ep + 1
                continue
            if epc == ord('*'):
                return max_expand(ms, s, p, ep)
            if epc == ord('+'):
                return max_expand(ms, s + 1, p, ep) if single_match(ms, s, p, ep) else None
            if epc == ord('-'):
                return min_expand(ms, s, p, ep)
            if not single_match(ms, s, p, ep):
                return None
            s += 1
            p = ep
    finally:
        ms.depth -= 1


def max_expand(ms, s, p, ep):
    i = 0
    while single_match(ms, s + i, p, ep):
        i += 1
    while i >= 0:
        r = do_match(ms, s + i, ep + 1)
        if r is not None:
            return r
        i -= 1
    return None


def min_expand(ms, s, p, ep):
    while True:
        r = do_match(ms, s, ep + 1)
        if r is not None:
            return r
        if single_match(ms, s, p, ep):
            s += 1
        else:
            return None


def start_capture(ms, s, p, what):
    ms.capture.append([s, what])
    r = do_match(ms, s, p)
    if r is None:
        ms.capture.pop()
    return r


def end_capture(ms, s, p):
    l = None
    for i in range(len(ms.capture) - 1, -1, -1):
        if ms.capture[i][1] == -2:
            l = i
            break
    if l is None:
        raise LuaError('invalid pattern capture')
    ms.capture[l][1] = s - ms.capture[l][0]
    r = do_match(ms, s, p)
    if r is None:
        ms.capture[l][1] = -2
    return r


def match_balance(ms, s, p):
    if s >= len(ms.src) or ms.src[s] != ms.pat[p]:
        return None
    b, e = ms.pat[p], ms.pat[p + 1]
    cont = 1
    i = s + 1
    while i < len(ms.src):
        c = ms.src[i]
        if c == e:
            cont -= 1
            if cont == 0:
                return do_match(ms, i + 1, p + 2)
        elif c == b:
            cont += 1
        i += 1
    return None


def get_capture(ms, i, s, e):
    if i >= len(ms.capture):
        if i == 0:
            return ms.src[s:e]
        raise LuaError('invalid capture index')
    st, ln = ms.capture[i]
    if ln == -1:
        return float(st + 1)
    return ms.src[st:st + ln]


def captures(ms, s, e, wholeifnone=True):
    n = len(ms.capture) if (ms.capture or not wholeifnone) else 1
    return [get_capture(ms, i, s, e) for i in range(n)]


def str_find(src, pat, init, plain, find):
    ls = len(src)
    if init < 0:
        init = max(ls + init, 0)
    elif init > 0:
        init -= 1
    if init > ls:
        return [None]
    if find and (plain or not any(c in SPECIALS for c in pat)):
        i = src.find(pat, init)
        if i < 0:
            return [None]
        return [float(i + 1), float(i + len(pat))]
    anchor = pat[:1] == b'^'
    p = 1 if anchor else 0
    s = init
    while True:
        ms = MatchState(src, pat)
        e = do_match(ms, s, p)
        if e is not None:
            if find:
                return [float(s + 1), float(e)] + (captures(ms, s, e, False) if ms.capture else [])
            return captures(ms, s, e)
        s += 1
        if anchor or s > ls:
            return [None]


def gsub(interp, src, pat, repl, max_n):
    anchor = pat[:1] == b'^'
    p = 1 if anchor else 0
    s = 0
    out = []
    n = 0
    while max_n is None or n < max_n:
        ms = MatchState(src, pat)
        e = do_match(ms, s, p)
        if e is not None:
            n += 1
            whole = src[s:e]
            caps = captures(ms, s, e)
            if isinstance(repl, bytes):
                r = bytearray()
                i = 0
                while i < len(repl):
                    c = repl[i]
                    if c == L_ESC and i + 1 < len(repl):
                        i += 1
                        d = repl[i]
                        if d == ord('0'):
                            r += whole
                        elif 49 <= d <= 57:
                            v = get_capture(ms, d - 49, s, e)
                            r += interp.tostr(v)
                        else:
                            r.append(d)
                    else:
                        r.append(c)
                    i += 1
                val = bytes(r)
            elif isinstance(repl, LuaTable):
                val = interp.index(repl, caps[0])
            else:
                rr = interp.call(repl, caps)
                val = rr[0] if rr else None
            if val is None or val is False:
                out.append(whole)
            else:
                out.append(interp.tostr(val))
        if e is not None and e > s:
            s = e
        elif s < len(src):
            out.append(src[s:s + 1])
            s += 1
        else:
            break
        if anchor:
            break
    out.append(src[s:])
    return [b''.join(out), float(n)]


# ------------------------------------------------------------------ helpers
def arg(args, i, default=None):
    v = args[i] if i < len(args) else default
    if isinstance(v, MultiMarker):
        v = v.single()
    return v


def argnum(args, i, default=None):
    v = arg(args, i, default)
    if is_sym(v):
        raise Unsupported('symbolic number argument')
    x = tonum(v)
    if x is None:
        raise LuaError('bad argument #%d (number expected)' % (i + 1))
    return x


def argstr(args, i, default=None):
    v = arg(args, i, default)
    if is_sym(v):
        raise Unsupported('symbolic string argument')
    if isinstance(v, (int, float)) and not isinstance(v, bool):
        return num2str(float(v))
    if not isinstance(v, bytes):
        raise LuaError('bad argument #%d (string expected)' % (i + 1))
    return v


def strsub(s, i, j):
    l = len(s)
    i = int(i)
    j = int(j)
    if i < 0:
        i = max(l + i + 1, 1)
    elif i == 0:
        i = 1
    if j < 0:
        j = l + j + 1
    elif j > l:
        j = l
    if i > j:
        return b''
    return s[i - 1:j]


def tou32(x):
    return int(math.fmod(math.floor(x), 2 ** 32)) % (2 ** 32)


def make_env(interp, sandbox=False, output=None):
    G = interp.G

    def reg(tbl, name, fn):
        tbl.rawset(name.encode(), Builtin(fn, name))

    def lib(name):
        t = LuaTable()
        G.rawset(name.encode(), t)
        return t

    G.rawset(b'_G', G)
    G.rawset(b'_VERSION', b'Lua 5.1')

    def _print(I, a):
        if sandbox:
            raise Unsupported('print in sandbox')
        if output is not None:
            output.append(b'\t'.join(I.tostr(x) for x in a))
        return []
    reg(G, 'print', _print)
    reg(G, 'type', lambda I, a: [I.type(arg(a, 0))])
    reg(G, 'tostring', lambda I, a: [I.tostr(arg(a, 0))])

    def _tonumber(I, a):
        v = arg(a, 0)
        base = arg(a, 1)
        if base is None:
            return [tonum(v)]
        base = int(base)
        s = I.tostr(v).strip().lower().decode('latin-1')
        try:
            return [float(int(s, base))]
        except ValueError:
            return [None]
    reg(G, 'tonumber', _tonumber)

    def _select(I, a):
        n = a[0] if a else None
        rest = list(a[1:])
        if n == b'#':
            if rest and isinstance(rest[-1], MultiMarker):
                m = rest[-1]
                return [ECount(m.src, len(rest) - 1)]
            return [float(len(rest))]
        n = int(tonum(n))
        if n < 0:
            n = len(rest) + n
        else:
            n -= 1
        return rest[n:]
    reg(G, 'select', _select)

    def _unpack(I, a):
        t = arg(a, 0)
        i = int(argnum(a, 1, 1.0)) if arg(a, 1) is not None else 1
        j = arg(a, 2)
        if isinstance(t, SymStack):
            if isinstance(j, ECount):
                base = int(j.off) + 1
                out = [EReg(k) for k in range(i, base)]
                return out + [MultiMarker(('reg', base, j.src))]
            if is_sym(j):
                raise Unsupported('symbolic unpack end')
            return [EReg(k) for k in range(i, int(j) + 1)]
        if isinstance(t, SymVarargs):
            raise Unsupported('unpack varargs')
        if j is None:
            if t.multi is not None:
                raise Unsupported('unpack symbolic multi table')
            j = t.length()
        if is_sym(j):
            raise Unsupported('symbolic unpack end')
        return [t.rawget(k) for k in range(i, int(j) + 1)]
    reg(G, 'unpack', _unpack)

    def _next(I, a):
        t = arg(a, 0)
        k = arg(a, 1)
        keys = list(t.d.keys())
        if k is None:
            idx = 0
        else:
            if isinstance(k, float) and k.is_integer():
                k = int(k)
            idx = keys.index(k) + 1
        if idx >= len(keys):
            return [None]
        kk = keys[idx]
        return [float(kk) if isinstance(kk, int) else kk, t.d[kk]]
    nextb = Builtin(_next, 'next')
    G.rawset(b'next', nextb)
    reg(G, 'pairs', lambda I, a: [nextb, arg(a, 0), None])

    def _inext(I, a):
        t = arg(a, 0)
        i = int(arg(a, 1)) + 1
        v = I.index(t, float(i))
        return [None] if v is None else [float(i), v]
    inext = Builtin(_inext, 'inext')
    reg(G, 'ipairs', lambda I, a: [inext, arg(a, 0), 0.0])
    reg(G, 'rawget', lambda I, a: [arg(a, 0).rawget(arg(a, 1))])

    def _rawset(I, a):
        arg(a, 0).rawset(arg(a, 1), arg(a, 2))
        return [arg(a, 0)]
    reg(G, 'rawset', _rawset)
    reg(G, 'rawequal', lambda I, a: [arg(a, 0) is arg(a, 1) or arg(a, 0) == arg(a, 1)])

    def _setmt(I, a):
        t = arg(a, 0)
        t.meta = arg(a, 1)
        return [t]
    reg(G, 'setmetatable', _setmt)
    reg(G, 'getmetatable', lambda I, a: [arg(a, 0).meta if isinstance(arg(a, 0), LuaTable) else
                                          (I.string_meta if isinstance(arg(a, 0), bytes) else None)])

    def _pcall(I, a):
        try:
            return [True] + I.call(a[0], list(a[1:]))
        except LuaError as e:
            return [False, str(e).encode()]
    reg(G, 'pcall', _pcall)

    def _error(I, a):
        raise LuaError(I.tostr(arg(a, 0)).decode('latin-1'))
    reg(G, 'error', _error)

    def _assert(I, a):
        if not I.truth(arg(a, 0)):
            raise LuaError('assertion failed!')
        return list(a)
    reg(G, 'assert', _assert)
    reg(G, 'getfenv', lambda I, a: [G])
    reg(G, 'setfenv', lambda I, a: [arg(a, 0)])

    # string
    S = lib('string')

    def _byte(I, a):
        s = argstr(a, 0)
        i = int(argnum(a, 1, 1.0))
        j = int(argnum(a, 2, float(i)))
        sub = strsub(s, i, j)
        return [float(c) for c in sub]
    reg(S, 'byte', _byte)

    def _char(I, a):
        return [bytes(int(argnum(a, i)) & 255 for i in range(len(a)))]
    reg(S, 'char', _char)
    reg(S, 'sub', lambda I, a: [strsub(argstr(a, 0), argnum(a, 1, 1.0), argnum(a, 2, -1.0))])
    reg(S, 'len', lambda I, a: [float(len(argstr(a, 0)))])
    reg(S, 'lower', lambda I, a: [argstr(a, 0).lower()])
    reg(S, 'upper', lambda I, a: [argstr(a, 0).upper()])
    reg(S, 'reverse', lambda I, a: [argstr(a, 0)[::-1]])

    def _rep(I, a):
        s = argstr(a, 0)
        n = int(argnum(a, 1))
        sep = argstr(a, 2, b'')
        if n <= 0:
            return [b'']
        if n * len(s) > 50_000_000:
            raise Unsupported('rep too large')
        return [sep.join([s] * n)]
    reg(S, 'rep', _rep)
    reg(S, 'gsub', lambda I, a: gsub(I, argstr(a, 0), argstr(a, 1), arg(a, 2),
                                    None if arg(a, 3) is None else int(argnum(a, 3))))
    reg(S, 'find', lambda I, a: str_find(argstr(a, 0), argstr(a, 1), int(argnum(a, 2, 1.0)),
                                        I.truth(arg(a, 3)), True))
    reg(S, 'match', lambda I, a: str_find(argstr(a, 0), argstr(a, 1), int(argnum(a, 2, 1.0)), False, False))

    def _gmatch(I, a):
        src, pat = argstr(a, 0), argstr(a, 1)
        state = {'s': 0}

        def it(I2, _):
            s = state['s']
            while s <= len(src):
                ms = MatchState(src, pat)
                e = do_match(ms, s, 0)
                if e is not None:
                    state['s'] = e + 1 if e == s else e
                    return captures(ms, s, e)
                s += 1
            state['s'] = s
            return [None]
        return [Builtin(it, 'gmatch_it')]
    reg(S, 'gmatch', _gmatch)

    def _format(I, a):
        fmt = argstr(a, 0)
        out = bytearray()
        i = 0
        ai = 1
        while i < len(fmt):
            c = fmt[i]
            if c != L_ESC:
                out.append(c)
                i += 1
                continue
            j = i + 1
            while j < len(fmt) and fmt[j:j + 1] in (b'-', b'+', b' ', b'#', b'0') or (j < len(fmt) and 48 <= fmt[j] <= 57) or (j < len(fmt) and fmt[j] == 46):
                j += 1
            spec = fmt[i:j + 1].decode()
            conv = fmt[j:j + 1]
            i = j + 1
            if conv == b'%':
                out += b'%'
                continue
            v = arg(a, ai)
            ai += 1
            if conv in (b'd', b'i'):
                out += (spec[:-1] + 'd' if conv == b'i' else spec).replace('i', 'd').encode() % int(tonum(v))
            elif conv in (b'x', b'X', b'o', b'c'):
                out += spec.encode() % int(tonum(v))
            elif conv in (b'f', b'g', b'e', b'G', b'E'):
                out += spec.encode() % tonum(v)
            elif conv == b's':
                out += spec.encode() % I.tostr(v)
            elif conv == b'q':
                out += b'"' + I.tostr(v).replace(b'\\', b'\\\\').replace(b'"', b'\\"').replace(b'\n', b'\\n') + b'"'
            else:
                raise Unsupported('format ' + spec)
        return [bytes(out)]
    reg(S, 'format', _format)
    sm = LuaTable()
    sm.rawset(b'__index', S)
    interp.string_meta = sm

    # table
    T = lib('table')

    def _concat(I, a):
        t = arg(a, 0)
        sep = argstr(a, 1, b'')
        i = int(argnum(a, 2, 1.0))
        j = int(argnum(a, 3, float(t.length())))
        return [sep.join(I.tostr(t.rawget(k)) for k in range(i, j + 1))]
    reg(T, 'concat', _concat)

    def _insert(I, a):
        t = arg(a, 0)
        if len(a) == 2:
            t.rawset(t.length() + 1, arg(a, 1))
        else:
            pos = int(argnum(a, 1))
            n = t.length()
            for k in range(n, pos - 1, -1):
                t.rawset(k + 1, t.rawget(k))
            t.rawset(pos, arg(a, 2))
        return []
    reg(T, 'insert', _insert)

    def _remove(I, a):
        t = arg(a, 0)
        n = t.length()
        pos = int(argnum(a, 1, float(n)))
        if n == 0:
            return [None]
        v = t.rawget(pos)
        for k in range(pos, n):
            t.rawset(k, t.rawget(k + 1))
        t.rawset(n, None)
        return [v]
    reg(T, 'remove', _remove)
    reg(T, 'unpack', _unpack)
    reg(T, 'getn', lambda I, a: [float(arg(a, 0).length())])

    # math
    M = lib('math')
    reg(M, 'floor', lambda I, a: [float(math.floor(argnum(a, 0)))])
    reg(M, 'ceil', lambda I, a: [float(math.ceil(argnum(a, 0)))])
    reg(M, 'abs', lambda I, a: [abs(argnum(a, 0))])
    reg(M, 'sqrt', lambda I, a: [math.sqrt(argnum(a, 0)) if argnum(a, 0) >= 0 else math.nan])
    reg(M, 'max', lambda I, a: [max(argnum(a, i) for i in range(len(a)))])
    reg(M, 'min', lambda I, a: [min(argnum(a, i) for i in range(len(a)))])
    reg(M, 'ldexp', lambda I, a: [math.ldexp(argnum(a, 0), int(argnum(a, 1)))])

    def _frexp(I, a):
        m, e = math.frexp(argnum(a, 0))
        return [m, float(e)]
    reg(M, 'frexp', _frexp)
    reg(M, 'fmod', lambda I, a: [math.fmod(argnum(a, 0), argnum(a, 1))])

    def _modf(I, a):
        f, i = math.modf(argnum(a, 0))
        return [i, f]
    reg(M, 'modf', _modf)
    reg(M, 'pow', lambda I, a: [I.arith('^', argnum(a, 0), argnum(a, 1))])
    reg(M, 'exp', lambda I, a: [math.exp(argnum(a, 0))])
    reg(M, 'log', lambda I, a: [math.log(argnum(a, 0)) if arg(a, 1) is None else math.log(argnum(a, 0), argnum(a, 1))])
    reg(M, 'sin', lambda I, a: [math.sin(argnum(a, 0))])
    reg(M, 'cos', lambda I, a: [math.cos(argnum(a, 0))])
    reg(M, 'tan', lambda I, a: [math.tan(argnum(a, 0))])
    M.rawset(b'huge', math.inf)
    M.rawset(b'pi', math.pi)

    # bit32 / bit
    for nm in ('bit32', 'bit'):
        B = lib(nm)

        def mk(f, name):
            reg(B, name, lambda I, a, f=f: [float(f([tou32(argnum(a, i)) for i in range(len(a))]))])
        import functools
        mk(lambda xs: functools.reduce(lambda x, y: x ^ y, xs, 0), 'bxor')
        mk(lambda xs: functools.reduce(lambda x, y: x & y, xs, 0xffffffff), 'band')
        mk(lambda xs: functools.reduce(lambda x, y: x | y, xs, 0), 'bor')
        mk(lambda xs: (~xs[0]) & 0xffffffff, 'bnot')
        mk(lambda xs: (xs[0] << (xs[1] & 31)) & 0xffffffff if xs[1] < 32 else 0, 'lshift')
        mk(lambda xs: (xs[0] >> xs[1]) if xs[1] < 32 else 0, 'rshift')
        mk(lambda xs: ((xs[0] - (1 << 32) if xs[0] & 0x80000000 else xs[0]) >> min(xs[1], 31)) & 0xffffffff, 'arshift')
        mk(lambda xs: 1 if functools.reduce(lambda x, y: x & y, xs, 0xffffffff) else 0, 'btest_')
        reg(B, 'btest', lambda I, a: [bool(functools.reduce(lambda x, y: x & y, [tou32(argnum(a, i)) for i in range(len(a))], 0xffffffff))])
        mk(lambda xs: (xs[0] >> xs[1]) & ((1 << (xs[2] if len(xs) > 2 else 1)) - 1), 'extract')
    return G
