"""Dataflow (reaching definitions / webs) and the cleanup passes applied to structured IR."""
from ir import *

UNDEF = 'undef'


# ====================================================================== dataflow
def regs_in(e):
    """All EReg occurrences (as numbers) in an expression, including closure captures."""
    out = []
    for x in walk(e):
        if isinstance(x, EReg) and isinstance(x.n, int):
            out.append(x.n)
        elif isinstance(x, EMultiReg):
            out.append(x.base)
    return out


def stmt_uses(s):
    r = []
    for e in stmt_exprs(s):
        r.extend(regs_in(e))
    if isinstance(s, SAssign):
        # targets' index sub-expressions already included via stmt_exprs
        pass
    return r


def stmt_defs(s):
    if isinstance(s, SAssign):
        out = []
        for t in s.targets:
            if isinstance(t, EReg):
                out.append(t.n)
            elif isinstance(t, EMultiReg):
                out.append(t.base)
        return out
    if isinstance(s, SNumFor):
        return [s.var.n]
    if isinstance(s, SGenFor):
        return [v.n for v in s.vars]
    return []


class Flow:
    """Reaching definitions over structured code. defs are (stmt_id, reg) or ('param', reg) or (UNDEF, reg)."""

    def __init__(self, fn):
        self.fn = fn
        self.use = {}          # (id(stmt), reg) -> set(def)
        self.stmt_by_id = {}
        self.parent_block = {}  # id(stmt) -> (block list, index)
        self.captured = set()   # regs captured by closures
        state = {}
        for i in range(fn.nparams):
            state[i] = frozenset([('param', i)])
        self.block(fn.body, state, None)
        self._webs()

    def rec_use(self, s, st):
        for r in stmt_uses(s):
            k = (id(s), r)
            ds = st.get(r) if st is not None else None
            if ds is None:
                ds = frozenset([(UNDEF, r)])
            self.use[k] = self.use.get(k, frozenset()) | ds
        for e in stmt_exprs(s):
            for x in walk(e):
                if isinstance(x, EClosure):
                    for c in x.caps:
                        if isinstance(c, EReg):
                            self.captured.add(c.n)

    def block(self, stmts, st, loop):
        for i, s in enumerate(stmts):
            self.stmt_by_id[id(s)] = s
            self.parent_block[id(s)] = (stmts, i)
            st = self.stmt(s, st, loop)
        return st

    @staticmethod
    def join(a, b):
        if a is None:
            return b
        if b is None:
            return a
        out = dict(a)
        for k, v in b.items():
            out[k] = out[k] | v if k in out else v
        return out

    def stmt(self, s, st, loop):
        if st is None:
            st = {}     # unreachable code: analyse anyway with empty state
        if isinstance(s, SAssign):
            self.rec_use(s, st)
            st = dict(st)
            for r in stmt_defs(s):
                st[r] = frozenset([(id(s), r)])
            return st
        if isinstance(s, (SCall, SLocal, SComment)):
            self.rec_use(s, st)
            return st
        if isinstance(s, SIf):
            self.rec_use(s, st)
            a = self.block(s.then, dict(st), loop)
            b = self.block(s.els, dict(st), loop)
            return self.join(a, b)
        if isinstance(s, SReturn):
            self.rec_use(s, st)
            return None
        if isinstance(s, SBreak):
            loop['breaks'].append(st)
            return None
        if isinstance(s, SContinue):
            loop['conts'].append(st)
            return None
        if isinstance(s, SGoto):
            return None
        if isinstance(s, (SWhile, SNumFor, SGenFor)):
            self.rec_use(s, st)       # header expressions (evaluated once for fors)
            entry = dict(st)
            back = None
            for _ in range(50):
                head = self.join(entry, back)
                if isinstance(s, SWhile):
                    self.rec_use(s, head)
                body_in = dict(head)
                for r in stmt_defs(s):
                    body_in[r] = frozenset([(id(s), r)])
                lp = {'breaks': [], 'conts': []}
                out = self.block(s.body, body_in, lp)
                nb = out
                for c in lp['conts']:
                    nb = self.join(nb, c)
                new_head = self.join(entry, nb)
                if new_head == head:
                    break
                back = nb
            ex = None
            if not (isinstance(s, SWhile) and isinstance(s.cond, EConst) and s.cond.v is True):
                ex = head
            for b in lp['breaks']:
                ex = self.join(ex, b)
            return ex
        return st

    def _webs(self):
        parent = {}

        def find(x):
            while parent.setdefault(x, x) != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        def union(a, b):
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb
        for k, ds in self.use.items():
            ds = list(ds)
            for d in ds[1:]:
                union(ds[0], d)
        self.find = find
        self.uses_of = {}      # def -> list of use keys
        for k, ds in self.use.items():
            for d in ds:
                self.uses_of.setdefault(d, []).append(k)

    def web_of_def(self, d):
        return self.find(d)

    def web_of_use(self, s, r):
        ds = self.use.get((id(s), r))
        if not ds:
            return self.find((UNDEF, r))
        return self.find(next(iter(ds)))


# ====================================================================== helpers
def count_reg(e, r):
    return sum(1 for x in walk(e) if (isinstance(x, EReg) and x.n == r) or (isinstance(x, EMultiReg) and x.base == r))


def in_closure_caps(e, r):
    for x in walk(e):
        if isinstance(x, EClosure) and any(isinstance(c, EReg) and c.n == r for c in x.caps):
            return True
    return False


def replace_reg(e, r, val):
    def f(x):
        if isinstance(x, EReg) and x.n == r:
            return val
        if isinstance(x, EMultiReg) and x.base == r:
            return val
        return None
    return subst(e, f)


def is_pure(e):
    for x in walk(e):
        if isinstance(x, (ECall, EResult, EMultiReg)):
            return False
    return True


def blocks_of(fn):
    """All statement lists in the function (pre-order)."""
    out = [fn.body]
    i = 0
    while i < len(out):
        for s in out[i]:
            out.extend(stmt_blocks(s))
        i += 1
    return out


# ====================================================================== inlining
def inline_once(fn):
    fl = Flow(fn)
    for blk in blocks_of(fn):
        for i in range(len(blk) - 2, -1, -1):
            D, U = blk[i], blk[i + 1]
            if not isinstance(D, SAssign) or D.local:
                continue
            if len(D.values) != 1:
                continue
            # --- multi-assign feeding a generic for header
            if len(D.targets) > 1 and isinstance(U, SGenFor) and all(isinstance(t, EReg) for t in D.targets):
                regs = [t.n for t in D.targets]
                if list(U.exprs) == [EReg(n) for n in regs] and all(
                        fl.uses_of.get((id(D), n), []) == [(id(U), n)] and fl.use[(id(U), n)] == {(id(D), n)}
                        for n in regs):
                    U.exprs = [D.values[0]]
                    del blk[i]
                    return True
                continue
            if len(D.targets) != 1:
                continue
            t = D.targets[0]
            if isinstance(t, EReg):
                r = t.n
            elif isinstance(t, EMultiReg):
                r = t.base
            else:
                continue
            if r in fl.captured and isinstance(t, EReg):
                if any(in_closure_caps(e, r) for s in (U,) for e in stmt_exprs(s)):
                    continue
            d = (id(D), r)
            uses = fl.uses_of.get(d, [])
            if uses != [(id(U), r)]:
                continue
            if fl.use[(id(U), r)] != {d}:
                continue
            if isinstance(U, SWhile) or isinstance(U, (SLocal, SComment)):
                continue
            exprs = stmt_exprs(U)
            n = sum(count_reg(e, r) for e in exprs)
            if n != 1 or any(in_closure_caps(e, r) for e in exprs):
                continue
            val = D.values[0]
            if isinstance(t, EReg) and isinstance(val, EMultiReg):
                continue
            # a multi value may only be used as the last call argument
            map_stmt_exprs(U, lambda e: replace_reg(e, r, val))
            del blk[i]
            return True
    return False


# ====================================================================== dead code
def dce_once(fn):
    fl = Flow(fn)
    changed = False
    for blk in blocks_of(fn):
        i = 0
        while i < len(blk):
            s = blk[i]
            if isinstance(s, SAssign) and all(isinstance(t, (EReg, EMultiReg)) for t in s.targets) and \
                    all(is_pure(v) for v in s.values) and not s.local:
                regs = stmt_defs(s)
                if all(not fl.uses_of.get((id(s), r)) for r in regs):
                    del blk[i]
                    changed = True
                    continue
            if isinstance(s, SIf) and not s.then and not s.els and is_pure(s.cond):
                del blk[i]
                changed = True
                continue
            if isinstance(s, SComment) and s.text.startswith('dead'):
                del blk[i]
                continue
            i += 1
    return changed


# ====================================================================== peepholes
def norm_expr(e):
    def f(x):
        if isinstance(x, EUn) and x.op == 'not' and isinstance(x.a, EBin) and x.a.op in ('==', '~='):
            return EBin('~=' if x.a.op == '==' else '==', x.a.a, x.a.b)
        if isinstance(x, EUn) and x.op == 'not' and isinstance(x.a, EUn) and x.a.op == 'not' and \
                isinstance(x.a.a, EBin) and x.a.a.op in ('==', '~=', '<', '<=', '>', '>='):
            return x.a.a
        if isinstance(x, EBin) and x.op in ('==', '~=') and isinstance(x.a, EConst) and not isinstance(x.b, EConst):
            return EBin(x.op, x.b, x.a)
        if isinstance(x, EIndex) and x.obj == EGlobal(b'_G') and isinstance(x.key, EConst) and \
                isinstance(x.key.v, bytes):
            from emit import is_ident
            if is_ident(x.key.v):
                return EGlobal(x.key.v)
        return None
    return subst(e, f)


def is_bool_expr(e):
    return (isinstance(e, EBin) and e.op in ('==', '~=', '<', '<=', '>', '>=')) or \
        (isinstance(e, EUn) and e.op == 'not') or (isinstance(e, EConst) and isinstance(e.v, bool))


def peephole(fn):
    changed = False
    for blk in blocks_of(fn):
        for s in blk:
            before = repr(stmt_exprs(s))
            map_stmt_exprs(s, norm_expr)
            if repr(stmt_exprs(s)) != before:
                changed = True
        i = 0
        while i < len(blk):
            s = blk[i]
            if isinstance(s, SIf):
                # if c then else X end  ->  if not c then X end
                if not s.then and s.els:
                    s.cond, s.then, s.els = norm_expr(EUn('not', s.cond)), s.els, []
                    changed = True
                # if c then R = false else R = true end  ->  R = not c
                if len(s.then) == 1 and len(s.els) == 1 and all(isinstance(x, SAssign) for x in s.then + s.els):
                    a, b = s.then[0], s.els[0]
                    if a.targets == b.targets and len(a.targets) == 1 and len(a.values) == 1 and len(b.values) == 1 \
                            and isinstance(a.values[0], EConst) and isinstance(b.values[0], EConst) and \
                            {a.values[0].v, b.values[0].v} == {True, False} and \
                            all(type(v.v) is bool for v in (a.values[0], b.values[0])):
                        c = s.cond
                        if a.values[0].v is False:
                            c = norm_expr(EUn('not', c))
                        elif not is_bool_expr(c):
                            c = EUn('not', EUn('not', c))
                        blk[i] = SAssign(a.targets, [c])
                        changed = True
                        continue
                # R = a ; if not R then R = b end   ->  R = a or b
                if i > 0 and not s.els and len(s.then) == 1 and isinstance(s.then[0], SAssign):
                    p, a = blk[i - 1], s.then[0]
                    if isinstance(p, SAssign) and len(p.targets) == 1 and len(p.values) == 1 and \
                            isinstance(p.targets[0], EReg) and a.targets == p.targets and len(a.values) == 1:
                        R = p.targets[0]
                        op = 'or' if s.cond == EUn('not', R) else 'and' if s.cond == R else None
                        if op and count_reg(a.values[0], R.n) == 0:
                            blk[i - 1] = SAssign(p.targets, [EBin(op, p.values[0], a.values[0])])
                            del blk[i]
                            changed = True
                            continue
            i += 1
    # trailing bare return
    if fn.body and isinstance(fn.body[-1], SReturn) and not fn.body[-1].values:
        fn.body.pop()
        changed = True
    return changed


# ====================================================================== state-machine removal
class PEFail(Exception):
    pass


def state_webs(fn, fl):
    """Webs that behave like dispatcher state variables."""
    info = {}
    bad = set()

    def mark(w, ok):
        if not ok:
            bad.add(w)
        info.setdefault(w, {'reg': None})
    for blk in blocks_of(fn):
        for s in blk:
            for r in stmt_defs(s):
                w = fl.web_of_def((id(s), r))
                ok = isinstance(s, SAssign) and len(s.targets) == 1 and len(s.values) == 1 and \
                    isinstance(s.values[0], EConst) and isinstance(s.values[0].v, float)
                mark(w, ok)
                info[w]['reg'] = r
            for r in set(stmt_uses(s)):
                w = fl.web_of_use(s, r)
                ok = isinstance(s, SIf) and state_cmp(s.cond) is not None and state_cmp(s.cond)[0] == r
                mark(w, ok)
    for i in range(fn.nparams):
        bad.add(fl.find(('param', i)))
    for r in fl.captured:
        for w in list(info):
            if info[w]['reg'] == r:
                bad.add(w)
    return {w for w in info if w not in bad and info[w]['reg'] is not None}


def state_cmp(c):
    """cond of form R == K / R ~= K  (K number)  -> (reg, op, value)"""
    if isinstance(c, EBin) and c.op in ('==', '~='):
        a, b = c.a, c.b
        if isinstance(b, EReg) and isinstance(a, EConst):
            a, b = b, a
        if isinstance(a, EReg) and isinstance(a.n, int) and isinstance(b, EConst) and isinstance(b.v, float):
            return a.n, c.op, b.v
    return None


class Deflattener:
    def __init__(self, fn):
        self.fn = fn
        self.fl = Flow(fn)
        self.sw = state_webs(fn, self.fl)
        self.reg_of = {}

    def run(self):
        if not self.sw:
            return False
        try:
            out, oc, env = self.pe(self.fn.body, {}, False)
        except PEFail:
            return False
        self.fn.body = out
        return True

    def assigned_webs(self, stmts):
        ws = set()
        for s in all_stmts(stmts):
            for r in stmt_defs(s):
                w = self.fl.web_of_def((id(s), r))
                if w in self.sw:
                    ws.add(w)
        return ws

    def used_webs(self, stmts):
        ws = set()
        for s in all_stmts(stmts):
            for r in set(stmt_uses(s)):
                w = self.fl.web_of_use(s, r)
                if w in self.sw:
                    ws.add(w)
        return ws

    def materialize(self, env, stmts):
        """Re-create assignments for known state values used by kept code."""
        out = []
        for w in self.used_webs(stmts):
            if w in env:
                r = self.web_reg(w)
                out.append(SAssign([EReg(r)], [EConst(env[w])]))
        return out

    def web_reg(self, w):
        for blk in blocks_of(self.fn):
            for s in blk:
                for r in stmt_defs(s):
                    if self.fl.web_of_def((id(s), r)) == w:
                        return r
        raise PEFail()

    def pe(self, stmts, env, unroll):
        out = []
        env = dict(env)
        for s in stmts:
            if isinstance(s, SAssign):
                defs = stmt_defs(s)
                if len(defs) == 1 and self.fl.web_of_def((id(s), defs[0])) in self.sw:
                    env[self.fl.web_of_def((id(s), defs[0]))] = s.values[0].v
                    continue
                out.append(s)
                continue
            if isinstance(s, SIf):
                sc = state_cmp(s.cond)
                if sc is not None:
                    w = self.fl.web_of_use(s, sc[0])
                    if w in self.sw:
                        if w not in env:
                            raise PEFail()
                        val = env[w] == sc[2]
                        if sc[1] == '~=':
                            val = not val
                        o, oc, env2 = self.pe(s.then if val else s.els, env, unroll)
                        out.extend(o)
                        if oc != 'fall':
                            return out, oc, env2
                        env = env2
                        continue
                t, toc, tenv = self.pe(s.then, env, unroll)
                e, eoc, eenv = self.pe(s.els, env, unroll)
                if unroll and (toc in ('break', 'cont') or eoc in ('break', 'cont')):
                    raise PEFail()
                out.append(SIf(s.cond, t, e))
                falls = [x for x, oc in ((tenv, toc), (eenv, eoc)) if oc == 'fall']
                if not falls:
                    return out, 'term', env
                if len(falls) == 2 and falls[0] != falls[1]:
                    raise PEFail()
                env = falls[0]
                continue
            if isinstance(s, SWhile) and isinstance(s.cond, EConst) and s.cond.v is True:
                r = self.unroll(s, env)
                if r is not None:
                    o, oc, env = r
                    out.extend(o)
                    if oc != 'fall':
                        return out, oc, env
                    continue
                out.extend(self.keep_loop(s, env))
                for w in self.assigned_webs(s.body):
                    env.pop(w, None)
                continue
            if isinstance(s, (SWhile, SNumFor, SGenFor)):
                if isinstance(s, SWhile) and self.used_webs([SIf(s.cond, [], [])]):
                    raise PEFail()
                out.extend(self.keep_loop(s, env))
                for w in self.assigned_webs(s.body):
                    env.pop(w, None)
                continue
            if isinstance(s, SBreak):
                if unroll:
                    return out, 'break', env
                out.append(s)
                return out, 'term', env
            if isinstance(s, SContinue):
                if unroll:
                    return out, 'cont', env
                out.append(s)
                return out, 'term', env
            if isinstance(s, (SReturn, SGoto)):
                out.append(s)
                return out, 'ret', env
            out.append(s)
        return out, 'fall', env

    def unroll(self, s, env):
        seen = set()
        out = []
        env = dict(env)
        try:
            for _ in range(2000):
                key = tuple(sorted(env.items(), key=repr))
                if key in seen:
                    return None
                seen.add(key)
                o, oc, env2 = self.pe(s.body, env, True)
                out.extend(o)
                env = env2
                if oc == 'break':
                    return out, 'fall', env
                if oc in ('ret', 'term'):
                    return out, 'ret', env
            return None
        except PEFail:
            return None

    def keep_loop(self, s, env):
        inner_env = {w: v for w, v in env.items() if w not in self.assigned_webs(s.body)}
        try:
            body, oc, _ = self.pe(s.body, inner_env, False)
        except PEFail:
            body = s.body
            inner_env = {}
        if isinstance(s, SWhile):
            ns = SWhile(s.cond, body)
        elif isinstance(s, SNumFor):
            ns = SNumFor(s.var, s.init, s.limit, s.step, body)
        else:
            ns = SGenFor(s.vars, s.exprs, body)
        pre = self.materialize(env, [ns]) if body is s.body else self.materialize(
            {w: v for w, v in env.items() if w in self.assigned_webs(s.body)}, [ns])
        return pre + [ns]


# ====================================================================== constant table folding
def fold_const_tables(fn):
    """local t = {} ; t[K] = "str" ... ; use t[K]   ->  use "str" directly."""
    fl = Flow(fn)
    changed = False
    for blk in blocks_of(fn):
        for i, s in enumerate(blk):
            if not (isinstance(s, SAssign) and len(s.targets) == 1 and isinstance(s.targets[0], EReg) and
                    s.values == [ETable(())]):
                continue
            r = s.targets[0].n
            d = (id(s), r)
            uses = fl.uses_of.get(d, [])
            ok = True
            consts = {}
            sets = []
            reads = []
            for (sid, rr) in uses:
                u = fl.stmt_by_id[sid]
                if fl.use[(sid, rr)] != {d}:
                    ok = False
                    break
                if isinstance(u, SAssign) and len(u.targets) == 1 and isinstance(u.targets[0], EIndex) and \
                        u.targets[0].obj == EReg(r) and isinstance(u.targets[0].key, EConst) and \
                        len(u.values) == 1 and isinstance(u.values[0], EConst) and \
                        count_reg(u.values[0], r) == 0 and fl.parent_block[sid][0] is blk:
                    k = u.targets[0].key.v
                    if k in consts:
                        ok = False
                        break
                    consts[k] = u.values[0]
                    sets.append(u)
                    continue
                # every other occurrence must be a read t[K]
                for e in stmt_exprs(u):
                    for x in walk(e):
                        if isinstance(x, EReg) and x.n == r:
                            pass
                cnt_idx = sum(1 for e in stmt_exprs(u) for x in walk(e)
                              if isinstance(x, EIndex) and x.obj == EReg(r) and isinstance(x.key, EConst))
                if cnt_idx != sum(count_reg(e, r) for e in stmt_exprs(u)):
                    ok = False
                    break
                if isinstance(u, SAssign) and any(isinstance(t, EIndex) and t.obj == EReg(r) for t in u.targets):
                    ok = False
                    break
                reads.append(u)
            if not ok or not sets:
                continue
            # all sets must come before every read in program order (sets are in blk)
            last_set = max(blk.index(x) for x in sets)
            order = {id(x): n for n, x in enumerate(all_stmts(fn.body))}
            last_set_order = order[id(blk[last_set])]
            if any(order[id(u)] <= last_set_order for u in reads):
                continue
            if any(x.key.v not in consts for u in reads for e in stmt_exprs(u) for x in walk(e)
                   if isinstance(x, EIndex) and x.obj == EReg(r)):
                continue

            def f(x):
                if isinstance(x, EIndex) and x.obj == EReg(r) and isinstance(x.key, EConst):
                    return consts[x.key.v]
                return None
            for u in reads:
                map_stmt_exprs(u, lambda e: subst(e, f))
            for x in sets:
                blk.remove(x)
            changed = True
            return changed
    return changed
