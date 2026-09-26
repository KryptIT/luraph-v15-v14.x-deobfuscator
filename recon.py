"""High-level reconstruction passes run after structuring and the generic cleanups.

  * fold_calls   - evaluates calls of pure helper closures (e.g. string decryptors) on constant
                   arguments by *executing the recovered function* in the sandbox interpreter
  * prune_caps   - drops closure captures that are no longer referenced
  * const_fold   - folds arithmetic between numeric literals
  * name_all     - gives every register web a name (v1, v2, ...) and inserts `local` declarations
"""
import math
import re

import emit
import interp
import lualib
import luaparse
import passes
from ir import *


# ============================================================ helpers
def closures_in(fn):
    for s in all_stmts(fn.body):
        for e in stmt_exprs(s):
            for x in walk(e):
                if isinstance(x, EClosure):
                    yield x


def child_order(funcs, root=0):
    """Functions in pre-order of nesting, with parent pointer + the closure creating them."""
    out = [(funcs[root], None, None)]
    i = 0
    seen = {root}
    while i < len(out):
        fn = out[i][0]
        for c in closures_in(fn):
            if c.pid in funcs and c.pid not in seen:
                seen.add(c.pid)
                out.append((funcs[c.pid], fn, c))
        i += 1
    return out


def defs_count(fn):
    cnt = {}
    for s in all_stmts(fn.body):
        for r in passes.stmt_defs(s):
            cnt[r] = cnt.get(r, 0) + 1
    for i in range(fn.nparams):
        cnt[i] = cnt.get(i, 0) + 1
    return cnt


def single_def_value(fn, r):
    """If register r is assigned exactly once (single target, single value) return that value."""
    if defs_count(fn).get(r) != 1:
        return None
    for s in all_stmts(fn.body):
        if isinstance(s, SAssign) and s.targets == [EReg(r)] and len(s.values) == 1:
            return s.values[0]
    return None


ENV_OK = (EGlobal, EConst)


def env_expr(fn, e, depth=0):
    """Resolve e to an expression built only from globals, constants, constant-key indexing and
    and/or.  Returns the resolved expression, or None."""
    if depth > 20:
        return None
    if isinstance(e, ENV_OK):
        return e
    if isinstance(e, EReg) and isinstance(e.n, int):
        v = single_def_value(fn, e.n)
        return None if v is None else env_expr(fn, v, depth + 1)
    if isinstance(e, EIndex) and isinstance(e.key, EConst):
        o = env_expr(fn, e.obj, depth + 1)
        return None if o is None else EIndex(o, e.key)
    if isinstance(e, EBin) and e.op in ('or', 'and'):
        a, b = env_expr(fn, e.a, depth + 1), env_expr(fn, e.b, depth + 1)
        return None if a is None or b is None else EBin(e.op, a, b)
    return None


def unsafe_body(funcs, pid, seen=None):
    """Does the function (or anything nested) contain IR we cannot faithfully print/execute?"""
    seen = seen or set()
    if pid in seen:
        return False
    seen.add(pid)
    fn = funcs.get(pid)
    if fn is None:
        return True
    for s in all_stmts(fn.body):
        if isinstance(s, (SGoto, SComment, SContinue)):
            return True
        for e in stmt_exprs(s) + list(getattr(s, 'targets', [])):
            for x in walk(e):
                if isinstance(x, (EMultiReg, ETemp, EResult, ECount, EIter)):
                    return True
                if isinstance(x, EClosure) and unsafe_body(funcs, x.pid, seen):
                    return True
    return False


# ============================================================ executing helper closures
class Evaluator:
    def __init__(self, funcs, step_limit=2_000_000):
        self.funcs = funcs
        self.step_limit = step_limit
        self.cache = {}
        self._decl = None

    def _declared_funcs(self):
        """Copies of all functions with every register pre-declared local (for sandbox printing)."""
        if self._decl is None:
            out = {}
            for pid, fn in self.funcs.items():
                regs = set()
                for s in all_stmts(fn.body):
                    regs.update(passes.stmt_defs(s))
                    for e in stmt_exprs(s):
                        regs.update(passes.regs_in(e))
                regs -= set(range(fn.nparams))
                body = ([SLocal([EReg(n) for n in sorted(regs)])] if regs else []) + list(fn.body)
                out[pid] = Function(pid, fn.nparams, body, fn.is_vararg)
            self._decl = out
        return self._decl

    def source(self, pid, caps, args):
        pr = emit.Printer(self._declared_funcs())
        lines = []
        for i, c in enumerate(caps):
            lines.append('local u%d = %s' % (i, pr.expr(c)))
        fake = EClosure(pid, tuple(EVar('u%d' % i) for i in range(len(caps))))
        lines.append('local f = ' + pr.function_expr(fake, 0, None))
        lines.append('return f(%s)' % ', '.join(pr.expr(a) for a in args))
        return '\n'.join(lines)

    def call(self, pid, caps, args):
        key = (pid, tuple(caps), tuple(args))
        if key in self.cache:
            return self.cache[key]
        res = None
        try:
            if not unsafe_body(self.funcs, pid):
                src = self.source(pid, caps, args)
                ast = luaparse.parse(src.encode('latin-1'))
                I = interp.Interp()
                I.max_steps = self.step_limit
                lualib.make_env(I, sandbox=True)
                before = dict(I.G.d) if hasattr(I.G, 'd') else None
                sc = interp.Scope()
                sc.vars['...'] = []
                r = I.exec_block(ast, sc)
                after = dict(I.G.d) if hasattr(I.G, 'd') else None
                vals = r[1] if r is not None and r[0] == 'ret' else []
                if before == after and len(vals) == 1 and \
                        (isinstance(vals[0], (bytes, bool)) or
                         (isinstance(vals[0], float) and math.isfinite(vals[0]))):
                    res = EConst(vals[0])
        except Exception:
            res = None
        self.cache[key] = res
        return res


def fold_calls(funcs, root=0):
    """Replace calls of pure helper closures on constant arguments with their result."""
    ev = Evaluator(funcs)
    changed = False
    known = {}          # pid -> {callee expr: (pid, resolved caps)}
    for fn, parent, clo in child_order(funcs, root):
        table = {}
        # closures held in this function's registers
        for s in all_stmts(fn.body):
            if isinstance(s, SAssign) and len(s.targets) == 1 and isinstance(s.targets[0], EReg) and \
                    len(s.values) == 1 and isinstance(s.values[0], EClosure):
                r = s.targets[0].n
                if single_def_value(fn, r) is not s.values[0]:
                    continue
                caps = [env_expr(fn, c) for c in s.values[0].caps]
                if all(c is not None for c in caps):
                    table[EReg(r)] = (s.values[0].pid, caps)
        # closures reaching us through upvalues
        if clo is not None:
            ptab = known.get(parent.pid, {})
            for k, c in enumerate(clo.caps):
                if c in ptab:
                    table[EUpval(k)] = ptab[c]
        known[fn.pid] = table

        def f(x):
            if isinstance(x, ECall) and x.args and all(isinstance(a, EConst) for a in x.args):
                tgt = None
                if x.fn in table:
                    tgt = table[x.fn]
                elif isinstance(x.fn, EClosure):
                    caps = [env_expr(fn, c) for c in x.fn.caps]
                    if all(c is not None for c in caps):
                        tgt = (x.fn.pid, caps)
                if tgt is not None:
                    return ev.call(tgt[0], tgt[1], list(x.args))
            return None
        for s in all_stmts(fn.body):
            if isinstance(s, SCall):
                continue          # result discarded: keep the call (it may have effects)
            if isinstance(s, SAssign) and len(s.values) == 1 and len(s.targets) > 1:
                continue          # multiple results wanted
            before = repr(stmt_exprs(s))
            map_stmt_exprs(s, lambda e: subst(e, f))
            if repr(stmt_exprs(s)) != before:
                changed = True
    return changed


# ============================================================ capture pruning
def prune_caps(funcs, root=0):
    changed = False
    sites = {}
    for fn in funcs.values():
        for c in closures_in(fn):
            sites[c.pid] = sites.get(c.pid, 0) + 1
    for fn, parent, clo in child_order(funcs, root):
        if clo is None or sites.get(fn.pid) != 1:
            continue
        used = set()
        for s in all_stmts(fn.body):
            for e in stmt_exprs(s) + list(getattr(s, 'targets', [])):
                for x in walk(e):
                    if isinstance(x, EUpval):
                        used.add(x.k)
        if len(used) == len(clo.caps):
            continue
        keep = [k for k in range(len(clo.caps)) if k in used]
        remap = {k: i for i, k in enumerate(keep)}
        newcaps = tuple(clo.caps[k] for k in keep)

        def g(x):
            if isinstance(x, EUpval) and x.k in remap:
                return EUpval(remap[x.k])
            return None
        for s in all_stmts(fn.body):
            map_stmt_exprs(s, lambda e: subst(e, g))
            if isinstance(s, SAssign):
                s.targets = [subst(t, g) if isinstance(t, EUpval) else t for t in s.targets]

        def h(x):
            if isinstance(x, EClosure) and x is clo:
                return EClosure(x.pid, newcaps)
            return None
        for s in all_stmts(parent.body):
            map_stmt_exprs(s, lambda e: _replace_identity(e, clo, EClosure(clo.pid, newcaps)))
        changed = True
        return changed | prune_caps(funcs, root)
    return changed


def _replace_identity(e, old, new):
    if e is old:
        return new
    if isinstance(e, EClosure) and e == old:
        return new
    return e.map(lambda c: _replace_identity(c, old, new))


# ============================================================ constant folding
ARITH = {'+': lambda a, b: a + b, '-': lambda a, b: a - b, '*': lambda a, b: a * b}


def const_fold(fn):
    def f(x):
        if isinstance(x, EBin) and x.op in ARITH and isinstance(x.a, EConst) and isinstance(x.b, EConst) and \
                type(x.a.v) is float and type(x.b.v) is float:
            v = ARITH[x.op](x.a.v, x.b.v)
            if math.isfinite(v) and float(v).is_integer() and abs(v) < 2 ** 53:
                return EConst(float(v))
        if isinstance(x, EBin) and x.op == '..' and isinstance(x.a, EConst) and isinstance(x.b, EConst) and \
                isinstance(x.a.v, bytes) and isinstance(x.b.v, bytes):
            return EConst(x.a.v + x.b.v)
        return None
    changed = False
    for s in all_stmts(fn.body):
        before = repr(stmt_exprs(s))
        map_stmt_exprs(s, lambda e: subst(e, f))
        if repr(stmt_exprs(s)) != before:
            changed = True
    return changed


# ============================================================ naming
PH = '\x01%d\x01'


class Namer:
    def __init__(self):
        self.uid = 0

    def fresh(self):
        self.uid += 1
        return EVar(PH % self.uid)

    def name_function(self, fn, upmap):
        """upmap: upvalue index -> expression (already named) from the enclosing function."""
        # 1. resolve upvalues to the parent's variables
        def up(x):
            if isinstance(x, EUpval) and x.k in upmap:
                return upmap[x.k]
            return None
        for s in all_stmts(fn.body):
            map_stmt_exprs(s, lambda e: subst(e, up))
            if isinstance(s, SAssign):
                s.targets = [subst(t, up) if isinstance(t, EUpval) else t for t in s.targets]

        fl = passes.Flow(fn)
        names = {}

        def name_of_web(w):
            if w not in names:
                names[w] = self.fresh()
            return names[w]
        params = []
        for i in range(fn.nparams):
            params.append(name_of_web(fl.find(('param', i))))
        fn.param_names = params

        for s in all_stmts(fn.body):
            usemap = {r: name_of_web(fl.web_of_use(s, r)) for r in set(passes.stmt_uses(s))}

            def g(x):
                if isinstance(x, EReg) and x.n in usemap:
                    return usemap[x.n]
                return None
            if isinstance(s, SAssign):
                newt = []
                for t in s.targets:
                    if isinstance(t, EReg):
                        newt.append(name_of_web(fl.web_of_def((id(s), t.n))))
                    elif isinstance(t, EIndex):
                        newt.append(EIndex(subst(t.obj, g), subst(t.key, g)))
                    else:
                        newt.append(t)
                s.values = [subst(v, g) for v in s.values]
                s.targets = newt
            else:
                map_stmt_exprs(s, lambda e: subst(e, g))
            if isinstance(s, SNumFor):
                s.var = name_of_web(fl.web_of_def((id(s), s.var.n)))
            if isinstance(s, SGenFor):
                s.vars = [name_of_web(fl.web_of_def((id(s), v.n))) for v in s.vars]
        declare_locals(fn, set(params))

    def run(self, funcs, root=0):
        upmaps = {root: {}}
        for fn, parent, clo in child_order(funcs, root):
            if clo is not None:
                # the parent was named already; find its (renamed) closure node for this pid
                cur = None
                for c in closures_in(parent):
                    if c.pid == fn.pid:
                        cur = c
                        break
                upmaps[fn.pid] = {k: c for k, c in enumerate(cur.caps)} if cur is not None else {}
            self.name_function(fn, upmaps.get(fn.pid, {}))


def declare_locals(fn, params):
    occ = {}        # var -> list of paths
    forbind = {}    # var -> list of for-statement paths

    def note(e, p):
        for x in walk(e):
            if isinstance(x, EVar) and x.name.startswith('\x01'):
                occ.setdefault(x, []).append(p)

    def visit(block, path):
        for i, s in enumerate(block):
            p = path + ((id(block), i),)
            for e in stmt_exprs(s):
                note(e, p)
            if isinstance(s, SAssign):
                for t in s.targets:
                    note(t, p)
            if isinstance(s, SNumFor):
                forbind.setdefault(s.var, []).append(p)
            if isinstance(s, SGenFor):
                for v in s.vars:
                    forbind.setdefault(v, []).append(p)
            for b in stmt_blocks(s):
                visit(b, p)
    visit(fn.body, ())
    blocks = {}
    for b in [fn.body] + [b for s in all_stmts(fn.body) for b in stmt_blocks(s)]:
        blocks[id(b)] = b

    decls = {}      # (block id, index) -> list of vars
    for v, paths in occ.items():
        if v in params:
            continue
        if v in forbind:
            fp = forbind[v]
            if len(fp) == 1 and all(p[:len(fp[0])] == fp[0] for p in paths):
                continue        # for-loop control variable only
        allp = paths + forbind.get(v, [])
        n = 0
        while all(len(p) > n for p in allp) and len({p[n] for p in allp}) == 1:
            n += 1
        if any(len(p) == n for p in allp) or len({p[n][0] for p in allp}) != 1:
            at = allp[0][n - 1] if n > 0 else None
        else:
            at = (allp[0][n][0], min(p[n][1] for p in allp))
        if at is None:
            at = (id(fn.body), 0)
        decls.setdefault(at, []).append(v)

    # insert declarations, highest index first so indices stay valid
    for (bid, idx) in sorted(decls, key=lambda k: -k[1]):
        blk = blocks[bid]
        vs = sorted(decls[(bid, idx)], key=lambda v: int(v.name.strip('\x01')))
        s = blk[idx]
        if isinstance(s, SAssign) and not s.local and all(isinstance(t, EVar) for t in s.targets) and \
                set(s.targets) <= set(vs) and not any(
                    x in s.targets for vexp in s.values for x in walk(vexp)):
            s.local = True
            vs = [v for v in vs if v not in s.targets]
        if vs:
            blk.insert(idx, SLocal(vs))


def renumber(text, prefix='v'):
    order = {}

    def r(m):
        k = m.group(1)
        if k not in order:
            order[k] = len(order) + 1
        return '%s%d' % (prefix, order[k])
    return re.sub('\x01(\\d+)\x01', r, text)
