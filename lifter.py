"""Load a LuaObfuscator (Ferib) VM script, run its own deserializer, then lift each instruction by
symbolically executing the interpreter's handler code with concrete operands."""
import luaparse
import lualib
from interp import (Interp, Scope, LuaFunction, LuaTable, MultiMarker, SymStack, SymEnv, SymUpv, SymVarargs,
                    Unsupported, LuaError, StepLimit, lift, is_sym)
from ir import *


class LiftError(Exception):
    pass


class Captured(Exception):
    pass


# ------------------------------------------------------------------ AST helpers
def ast_walk(n):
    if isinstance(n, luaparse.Node):
        yield n
        for x in (n.a, n.b, n.c, n.d, n.e):
            yield from ast_walk(x)
    elif isinstance(n, (list, tuple)):
        for x in n:
            yield from ast_walk(x)


def names_in(n):
    return {x.a for x in ast_walk(n) if x.k == 'Name'}


def find_loader(stmts):
    """Locate `local function L(...) ... return W(D(), {}, env)(...) end`."""
    for s in ast_walk(stmts):
        if s.k in ('LocalFunction', 'Assign', 'Local'):
            f = s.b if s.k == 'LocalFunction' else None
            if f is None:
                continue
            body = f.c
            if not body or body[-1].k != 'Return' or not body[-1].a:
                continue
            r = body[-1].a[0]
            if r.k == 'Call' and r.a.k == 'Call' and r.a.a.k == 'Name' and len(r.a.b) >= 3:
                wargs = r.a.b
                didx = [i for i, x in enumerate(wargs) if x.k == 'Call']
                tidx = [i for i, x in enumerate(wargs) if x.k == 'Table']
                if len(didx) == 1 and len(tidx) == 1:
                    env_idx = [i for i in range(len(wargs)) if i not in didx and i not in tidx][0]
                    return f, r.a.a.a, didx[0], tidx[0], env_idx
    raise LiftError('could not find the VM loader (not a LuaObfuscator VM script?)')


def find_local_function(stmts, name):
    for s in ast_walk(stmts):
        if s.k == 'LocalFunction' and s.a == name:
            return s.b
    raise LiftError('function %s not found' % name)


# ------------------------------------------------------------------ symbolic run context
class RunCtx:
    def __init__(self, lifter, script):
        self.L = lifter
        self.script = script
        self.decisions = []
        self.effects = []

    def pc(self):
        return int(self.L.pc_scope.vars[self.L.pc_name])

    def decide(self, expr):
        expr = simplify_cond(expr)
        if isinstance(expr, EConst):
            v = expr.v
            return v is not None and v is not False
        i = len(self.decisions)
        val = self.script[i] if i < len(self.script) else True
        self.decisions.append((expr, val, self.pc()))
        return val

    def record(self, eff):
        self.effects.append(eff)

    def symcall(self, f, args):
        cid = self.L.new_call_id()
        ir_args = []
        for i, a in enumerate(args):
            if isinstance(a, MultiMarker):
                if i != len(args) - 1:
                    a = a.single()
                else:
                    ir_args.append(multi_ir(a))
                    continue
            ir_args.append(lift(a))
        self.record(('call', cid, ECall(lift(f), tuple(ir_args))))
        return [MultiMarker(cid)]

    def symfor(self, I, s, sc, a, b, c):
        if not isinstance(b, ECount) or is_sym(a) or c != 1:
            raise Unsupported('symbolic for-loop shape')
        start = int(a)
        saved = self.effects
        self.effects = []
        inner = Scope(sc)
        inner.vars[s.a] = EIter(start)
        r = I.exec_block(s.e, inner)
        body_effs = self.effects
        self.effects = saved
        if r is not None:
            raise Unsupported('control flow in multi loop')
        sets = [e for e in body_effs if e[0] == 'set' and isinstance(e[1], EReg) and not isinstance(e[1].n, int)]
        if sets and len(sets) == len(body_effs):
            self.record(('setmulti', start, b.src))
            return None
        raise Unsupported('unknown multi-value loop (%d effects)' % len(body_effs))


def multi_ir(m):
    src = m.src
    if src == 'vararg':
        return EVararg()
    if isinstance(src, tuple) and src[0] == 'reg':
        return EMultiReg(src[1])
    return EResult(src, '*')


def simplify_cond(e):
    """Remove constant junk from conditions: x or false -> x, true and x -> x, etc."""
    def f(x):
        if isinstance(x, EBin) and x.op in ('and', 'or'):
            a, b = x.a, x.b
            if isinstance(a, EConst):
                t = a.v is not None and a.v is not False
                if x.op == 'and':
                    return b if t else a
                return a if t else b
            if isinstance(b, EConst):
                t = b.v is not None and b.v is not False
                if x.op == 'and':
                    return a if t else EConst(False)
                return EConst(True) if t else a
        if isinstance(x, EUn) and x.op == 'not' and isinstance(x.a, EConst):
            return EConst(not (x.a.v is not None and x.a.v is not False))
        if isinstance(x, EBin) and isinstance(x.a, EConst) and isinstance(x.b, EConst) and \
                x.op in ('==', '<', '<=') and isinstance(x.a.v, float) and isinstance(x.b.v, float):
            return EConst({'==': x.a.v == x.b.v, '<': x.a.v < x.b.v, '<=': x.a.v <= x.b.v}[x.op])
        return None
    return subst(e, f)


# ------------------------------------------------------------------ nodes
class Node:
    """IR node at a bytecode position. kind in: stmts, cond, forprep, forloop, tforloop, ret, bad"""

    def __init__(self, kind, pos, size, **kw):
        self.kind, self.pos, self.size = kind, pos, size
        self.stmts = kw.get('stmts', [])
        self.next = kw.get('next', pos + size)
        self.__dict__.update(kw)

    def __repr__(self):
        d = {k: v for k, v in self.__dict__.items() if k not in ('kind', 'pos', 'size')}
        return '<%s @%d+%d %r>' % (self.kind, self.pos, self.size, d)


class Proto:
    def __init__(self, pid, table):
        self.pid, self.table = pid, table
        self.nodes = {}
        self.nparams = 0
        self.ninstr = 0
        self.uses_vararg = False
        self.warnings = []


# ------------------------------------------------------------------ the lifter
class Lifter:
    def __init__(self, src_bytes):
        self.ast = luaparse.parse(src_bytes)
        self.I = Interp()
        lualib.make_env(self.I)
        self.call_ids = 0
        self.protos = {}        # id(table) -> Proto
        self.order = []
        self._load()

    def new_call_id(self):
        self.call_ids += 1
        return self.call_base + self.call_ids

    # ---- stage 1: run the obfuscator's own loader/deserializer
    def _load(self):
        loader, wname, didx, tidx, eidx = find_loader(self.ast)
        self.wrapper_node = find_local_function(loader.c, wname)
        self.w_proto_idx, self.w_upv_idx, self.w_env_idx = didx, tidx, eidx
        cap = {}
        I = self.I

        def hook(f, args):
            if isinstance(f, LuaFunction) and f.node is self.wrapper_node:
                cap['f'], cap['args'] = f, args
                raise Captured()
            return None
        I.call_hook = hook
        sc = Scope()
        sc.vars['...'] = []
        try:
            I.exec_block(self.ast, sc)
        except Captured:
            pass
        I.call_hook = None
        if 'f' not in cap:
            raise LiftError('VM entry was never reached')
        self.wrapper = cap['f']
        self.root_table = cap['args'][self.w_proto_idx]
        I.steps = 0

    # ---- stage 2: build the handler execution environment for a proto
    def _make_frame(self, ptable):
        I = self.I
        args = [None] * 3
        args[self.w_proto_idx] = ptable
        args[self.w_upv_idx] = SymUpv()
        args[self.w_env_idx] = SymEnv()
        inner = I.run_function(self.wrapper, args)[0]
        if not isinstance(inner, LuaFunction):
            raise LiftError('wrapper did not return a function')
        body = inner.node.c
        d = None
        for i, s in enumerate(body):
            if s.k == 'While' and s.a.k == 'True' and s.b and s.b[0].k == 'Assign' and \
                    s.b[0].b[0].k == 'Index' and s.b[0].b[0].a.k == 'Name' and s.b[0].b[0].b.k == 'Name':
                d = i
                break
        if d is None:
            raise LiftError('dispatch loop not found')
        first = body[d].b[0]
        self.ins_name = first.a[0].a
        self.code_name = first.b[0].a.a
        self.pc_name = first.b[0].b.a
        self.loopbody = body[d].b
        prologue = body[:d]
        sc = Scope(inner.scope)
        sc.vars['...'] = []
        for s in prologue:
            I.exec(s, sc)
        # identify stack / varargs / vararg-count from the argument-copy loop
        stk = va = np_name = None
        for s in ast_walk(prologue):
            if s.k == 'NumFor':
                ifs = [x for x in s.e if x.k == 'If']
                if not ifs:
                    continue
                iff = ifs[0]
                br = [iff.b[0], iff.c or []]
                tgts = []
                for b in br:
                    asg = [x for x in b if x.k == 'Assign' and x.a[0].k == 'Index']
                    tgts.append(asg[0].a[0] if asg else None)
                if None in tgts:
                    continue
                cmp_names = names_in(iff.a[0]) - {s.a}
                for t in tgts:
                    idx_names = names_in(t.b)
                    if idx_names & cmp_names:
                        va = t.a.a
                        np_name = list(idx_names & cmp_names)[0]
                    else:
                        stk = t.a.a
                break
        if stk is None or va is None:
            raise LiftError('could not identify VM stack/varargs')
        vacount = None
        for s in prologue:
            if s.k == 'Local' and s.b and len(s.a) == 1 and np_name in names_in(s.b) and s.a[0] not in (stk, va):
                vacount = s.a[0]
        sc.find(stk).vars[stk] = SymStack()
        sc.find(va).vars[va] = SymVarargs()
        if vacount:
            sc.find(vacount).vars[vacount] = ECount('vararg', 0)
        self.frame = sc
        self.pc_scope = sc.find(self.pc_name)
        code = sc.find(self.code_name).vars[self.code_name]
        nparams = sc.find(np_name).vars[np_name]
        return code, int(nparams or 0)

    # ---- stage 3: lift
    def lift_all(self):
        self.proto_of(self.root_table)
        i = 0
        while i < len(self.order):
            self._lift_proto(self.order[i])
            i += 1
        return self.order

    def proto_of(self, table):
        p = self.protos.get(id(table))
        if p is None:
            p = Proto(len(self.order), table)
            self.protos[id(table)] = p
            self.order.append(p)
        return p

    def _lift_proto(self, P):
        code, P.nparams = self._make_frame(P.table)
        self.cur_pid = P.pid
        n = code.length()
        mx = max([k for k in code.d if isinstance(k, int)] or [0])
        P.ninstr = max(n, mx)
        self.code = code
        pos = 1
        while pos <= P.ninstr:
            if code.rawget(pos) is None:
                pos += 1
                continue
            try:
                nodes = self._lift_at(P, pos)
            except (Unsupported, LuaError, StepLimit, LiftError, KeyError, TypeError, AttributeError, ValueError) as ex:
                P.warnings.append('instruction %d: %s' % (pos, ex))
                nodes = [Node('bad', pos, 1, msg=str(ex))]
            for nd in nodes:
                P.nodes[nd.pos] = nd
            last = nodes[-1]
            pos = last.pos + last.size
        return P

    def _run_once(self, pos, script, snapshot):
        I = self.I
        self.frame_restore(snapshot)
        self.pc_scope.vars[self.pc_name] = float(pos)
        ctx = RunCtx(self, script)
        self.call_base = pos * 1000 + getattr(self, 'cur_pid', 0) * 10_000_000
        self.call_ids = 0
        reads = {pos}
        code = self.code

        def ih(t, k):
            if t is code and isinstance(k, (int, float)):
                reads.add(int(k))
        I.ctx = ctx
        I.index_hook = ih
        I.call_hook = self._wrapper_hook
        I.steps = 0
        I.max_steps = 2_000_000
        try:
            r = I.exec_block(self.loopbody, self.frame)
        finally:
            I.ctx = None
            I.index_hook = None
            I.call_hook = None
        ret = None
        end_pc = None
        if r is not None and r[0] == 'ret':
            ret = r[1]
        else:
            end_pc = int(self.pc_scope.vars[self.pc_name])
        return ctx, ret, end_pc, reads

    def frame_snapshot(self):
        snap = []
        s = self.frame
        while s is not None and s is not self.wrapper.scope:
            snap.append((s, dict(s.vars)))
            s = s.parent
        return snap

    def frame_restore(self, snap):
        for s, v in snap:
            s.vars = dict(v)

    def _wrapper_hook(self, f, args):
        if isinstance(f, LuaFunction) and f.node is self.wrapper_node:
            pt = args[self.w_proto_idx] if self.w_proto_idx < len(args) else None
            if not isinstance(pt, LuaTable):
                raise Unsupported('closure of non-proto')
            child = self.proto_of(pt)
            upv = args[self.w_upv_idx] if self.w_upv_idx < len(args) else None
            caps = self._captures(upv)
            return [EClosure(child.pid, tuple(caps))]
        return None

    def _captures(self, upv):
        if upv is None or isinstance(upv, SymUpv):
            return []
        if not isinstance(upv, LuaTable) or upv.meta is None:
            raise Unsupported('unknown upvalue container')
        h = upv.meta.rawget(b'__index')
        if not isinstance(h, LuaFunction):
            raise Unsupported('unknown upvalue proxy')
        # the proxy's __index reads  CAPS[key]  -> find the captured table variable
        idx = [x for x in ast_walk(h.node.c) if x.k == 'Index' and x.a.k == 'Name']
        tbl = None
        for x in idx:
            s = h.scope.find(x.a.a)
            if s is not None and isinstance(s.vars[x.a.a], LuaTable):
                tbl = s.vars[x.a.a]
                break
        if tbl is None:
            raise Unsupported('capture list not found')
        caps = []
        k = 0
        while True:
            ent = tbl.rawget(k)
            if ent is None:
                break
            where, i = ent.rawget(1), ent.rawget(2)
            if isinstance(where, SymStack):
                caps.append(EReg(int(i)))
            elif isinstance(where, SymUpv):
                caps.append(EUpval(int(i)))
            else:
                raise Unsupported('capture source')
            k += 1
        return caps

    def _lift_at(self, P, pos):
        snap = self.frame_snapshot()
        pending = [[]]
        paths = []
        while pending:
            script = pending.pop()
            ctx, ret, end_pc, reads = self._run_once(pos, script, snap)
            for i in range(len(script), len(ctx.decisions)):
                alt = [d[1] for d in ctx.decisions[:i]] + [not ctx.decisions[i][1]]
                pending.append(alt)
            paths.append(dict(dec=ctx.decisions, eff=ctx.effects, ret=ret, end=end_pc, reads=reads))
            if len(paths) > 64:
                raise Unsupported('too many paths')
        # keep frame state of first path (e.g. multret TOP) for the next instruction
        self._run_once(pos, [d[1] for d in paths[0]['dec']], snap)
        for p in paths:
            for e in p['eff']:
                for x in effect_exprs(e):
                    if any(isinstance(y, (EVararg, EVarargAt)) for y in walk(x)):
                        P.uses_vararg = True
        return classify(pos, paths)


def effect_exprs(e):
    if e[0] == 'set':
        return [e[1], e[2]]
    if e[0] == 'call':
        return [e[2]]
    if e[0] == 'ret':
        return list(e[1])
    return []


# ------------------------------------------------------------------ classification
def eff_key(e):
    return repr(e)


def classify(pos, paths):
    size = max(max(p['reads']) for p in paths) - pos + 1
    if len(paths) == 1:
        p = paths[0]
        if p['ret'] is not None:
            vals = [multi_ir(v) if isinstance(v, MultiMarker) else lift(v) for v in p['ret']]
            return [Node('ret', pos, size, stmts=effects_to_stmts(list(p['eff']) + [('ret', vals)]))]
        stmts = effects_to_stmts(p['eff'])
        return [Node('stmts', pos, size, stmts=stmts, next=p['end'])]
    # common effect prefix
    k = 0
    while all(len(p['eff']) > k for p in paths) and len({eff_key(p['eff'][k]) for p in paths}) == 1:
        k += 1
    prefix = paths[0]['eff'][:k]
    forkpc = paths[0]['dec'][0][2]
    out = []

    pre = []

    def prefix_node(stmts):
        if forkpc > pos:
            out.append(Node('stmts', pos, forkpc - pos, stmts=stmts))
            return forkpc
        pre.extend(stmts)
        return pos

    # FORLOOP: R[a] = R[a] + R[a+2] then conditional jump back
    for e in prefix:
        if e[0] == 'set' and isinstance(e[1], EReg) and isinstance(e[2], EBin) and e[2].op == '+' and \
                e[2].a == e[1] and isinstance(e[2].b, EReg) and e[2].b.n == e[1].n + 2:
            a = e[1].n
            backs = [p['end'] for p in paths if p['end'] != forkpc + 1]
            loop_prefix = [x for x in prefix if x is not e]
            at = prefix_node(effects_to_stmts(loop_prefix))
            out.append(Node('forloop', at, pos + size - at, a=a, back=backs[0], next=at + 1, pre=pre))
            return out
    # TFORLOOP: call R[a](R[a+1], R[a+2]) and branch on first result
    for e in prefix:
        if e[0] == 'call' and isinstance(e[2].fn, EReg) and len(e[2].args) == 2 and \
                e[2].args[0] == EReg(e[2].fn.n + 1) and e[2].args[1] == EReg(e[2].fn.n + 2) and \
                any(isinstance(x, EResult) and x.id == e[1] for d in paths[0]['dec'] for x in walk(d[0])):
            a = e[2].fn.n
            nvars = sum(1 for x in prefix if x[0] == 'set' and isinstance(x[1], EReg) and isinstance(x[2], EResult)
                        and x[2].id == e[1])
            tpath = [p for p in paths if p['dec'][0][1]][0]
            fpath = [p for p in paths if not p['dec'][0][1]][0]
            out.append(Node('tforloop', pos, size, a=a, nvars=max(nvars, 1), back=tpath['end'], exit=fpath['end'], pre=[]))
            return out
    # FORPREP: entering path copies R[a] into R[a+3] and continues at forkpc+1
    for p in paths:
        for e in p['eff'][k:]:
            if e[0] == 'set' and isinstance(e[1], EReg) and isinstance(e[1].n, int) and e[2] == EReg(e[1].n - 3) \
                    and p['end'] == forkpc + 1:
                a = e[1].n - 3
                exits = [q['end'] for q in paths if q['end'] != forkpc + 1]
                at = prefix_node(effects_to_stmts(prefix))
                out.append(Node('forprep', at, pos + size - at, a=a, exit=exits[0], next=at + 1, pre=pre))
                return out
    # generic conditional branch on one decision
    decs = {repr(p['dec'][0][0]) for p in paths}
    if len(decs) == 1 and len(paths) == 2 and all(len(p['dec']) == 1 for p in paths):
        cond = paths[0]['dec'][0][0]
        tp = [p for p in paths if p['dec'][0][1]][0]
        fp = [p for p in paths if not p['dec'][0][1]][0]
        if tp['ret'] is None and fp['ret'] is None:
            at = prefix_node(effects_to_stmts(prefix))
            tst = effects_to_stmts(tp['eff'][k:])
            fst = effects_to_stmts(fp['eff'][k:])
            out.append(Node('cond', at, pos + size - at, cond=cond, t=tp['end'], f=fp['end'],
                            tstmts=tst, fstmts=fst, next=at + 1, pre=pre))
            return out
    raise Unsupported('unrecognised branching handler (%d paths)' % len(paths))


def effects_to_stmts(effs):
    out = []
    temps = {}
    i = 0
    effs = list(effs)

    def fix(x):
        def f(y):
            if isinstance(y, EResult) and y.id in temps:
                if y.k == '*':
                    return temps[y.id][1]
                if y.k == 1:
                    return ETemp(y.id)
            return None
        return subst(x, f)
    while i < len(effs):
        e = effs[i]
        if e[0] == 'call':
            cid, call = e[1], fix(e[2])
            j = i + 1
            targets = []
            while j < len(effs) and effs[j][0] == 'set' and isinstance(effs[j][1], EReg) and \
                    isinstance(effs[j][2], EResult) and effs[j][2].id == cid and effs[j][2].k == len(targets) + 1:
                targets.append(effs[j][1])
                j += 1
            if j < len(effs) and effs[j][0] == 'setmulti' and effs[j][2] == cid:
                targets.append(EMultiReg(effs[j][1]))
                j += 1
            if targets:
                out.append(SAssign(targets, [call]))
                i = j
                continue
            later = [x for ee in effs[i + 1:] for xe in effect_exprs(ee) for x in walk(xe)]
            used = [x for x in later if isinstance(x, EResult) and x.id == cid]
            if used and all(x.k == '*' for x in used):
                temps[cid] = ('inline', call)
            elif used:
                temps[cid] = ('temp', call)
                out.append(SAssign([ETemp(cid)], [call]))
            else:
                out.append(SCall(call))
            i += 1
            continue
        if e[0] == 'set':
            out.append(SAssign([fix(e[1])], [fix(e[2])]))
        elif e[0] == 'ret':
            out.append(SReturn([fix(v) for v in e[1]]))
        elif e[0] == 'setmulti':
            if e[2] != 'vararg':
                raise Unsupported('setmulti without call')
            out.append(SAssign([EMultiReg(e[1])], [EVararg()]))
        i += 1
    return out
