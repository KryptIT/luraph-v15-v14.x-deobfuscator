"""
Loop recognition for the devirtualizer, on the raw CFG (before expression
cleanup), where Luraph's loop protocol is still visible:

numeric for (FORPREP / FORLOOP handlers):
    prep:    Z_d = step + 0 ; P_d = limit + 0 ; a_d = start - Z_d ; goto H
    H:       a_d = a_d + Z_d
             if Z_d <= 0 then (if a_d >= P_d then rX = a_d; goto BODY else goto EXIT)
                         else (if a_d <= P_d then rX = a_d; goto BODY else goto EXIT)
generic for (coroutine-driven iterator):
    prep:    a_d = geniter(vm, f, s, ctl) ; goto H
    H:       T = a_d() ; if T[1] then rA = T[2]; rB = T[3]; goto BODY else goto EXIT

Both become a block of kind "for"/"forin" whose successors are [BODY, EXIT];
the structurer turns it into a `for` statement. Pseudo loop-state
assignments left over (saving/restoring the VM's loop stack) are dropped.
"""
from luasym import Const, Reg, Pseudo, Bin, TempVal


def is_pseudo(e, name=None, depth=None):
    return isinstance(e, Pseudo) and (name is None or e.name == name) and (depth is None or e.depth == depth)


def recognize(entry, blocks, D):
    found = {"for": 0, "forin": 0}
    for h in list(blocks.values()):
        if h.id not in blocks:
            continue
        if try_numeric(h, blocks, D):
            found["for"] += 1
        elif try_generic(h, blocks, D):
            found["forin"] += 1
    # drop VM loop bookkeeping (LPH_JIT loop variables stay while a loop
    # that was not recognized still reads them)
    read = set()
    for b in blocks.values():
        todo = [b.cond, getattr(b, "values", None)]
        for s in b.stmts:
            todo += [x for x in s.__dict__.values() if not isinstance(x, Pseudo)]
        while todo:
            x = todo.pop()
            if isinstance(x, Pseudo):
                read.add((x.name, x.depth))
            elif isinstance(x, (list, tuple)):
                todo += list(x)
            elif hasattr(x, "__dict__") and not isinstance(x, type):
                todo += list(x.__dict__.values())
    for b in blocks.values():
        b.stmts = [s for s in b.stmts if not (isinstance(s, D.Assign) and isinstance(s.target, Pseudo)
                                              and not (s.target.name.startswith("JIT")
                                                       and (s.target.name, s.target.depth) in read))]
    return found


def find_prep(h, blocks, D, names, depth):
    """Predecessor blocks of h (outside the loop) that assign the pseudo prep values."""
    preps = []
    for p in h.preds:
        pb = blocks[p]
        vals = {}
        for s in pb.stmts:
            if isinstance(s, D.Assign) and isinstance(s.target, Pseudo) and s.target.depth == depth:
                vals[s.target.name] = s.value
        if all(n in vals for n in names):
            preps.append((pb, vals))
    return preps


def _pure_moves(pre, D):
    return all(isinstance(s, D.Assign) and isinstance(s.target, (Reg, Pseudo))
               and isinstance(s.value, (Const, Reg, Pseudo)) for s in pre)


def _moves_to_latches(h, pb, pre, blocks):
    """Register moves at the loop head (before the iterator call / counter
    step) run before every header evaluation: once after the prep and at the
    end of every iteration that continues (a new block per back edge, so
    conditional latches work too)."""
    import copy
    import structure
    for lb in [blocks[p] for p in h.preds if p != pb.id]:
        nb = structure.Block(max(blocks) + 1)
        nb.stmts = [copy.copy(s) for s in pre]
        nb.kind = "goto"
        nb.succ = [h.id]
        nb.origin = lb.origin
        blocks[nb.id] = nb
        lb.succ = [nb.id if x == h.id else x for x in lb.succ]
    _recompute(blocks)


def try_numeric(h, blocks, D):
    if h.kind != "cond" or not h.stmts:
        return False
    # register resets Luraph puts before the counter step (`r2 = nil`)
    pre = h.stmts[:-1]
    s = h.stmts[-1]
    if not (isinstance(s, D.Assign) and is_pseudo(s.target) and isinstance(s.value, Bin) and s.value.op == "Add"
            and is_pseudo(s.value.a, s.target.name, s.target.depth) and is_pseudo(s.value.b)):
        return False
    if not _pure_moves(pre, D):
        # a loop whose body never comes back (it always returns): no back
        # edge, so the prep and the header are one straight-line block. It
        # runs at most once: plain ifs on the prep values, not a `for` (the
        # structurer copies a latch-less for loop without end)
        return _run_once_for(h, s, blocks, D)
    a, z = s.target, s.value.b
    d = a.depth
    c = h.cond
    if not (isinstance(c, Bin) and c.op == "CompareLe" and is_pseudo(c.a, z.name, d) and isinstance(c.b, Const)
            and c.b.v == 0):
        return False
    body = exit_ = var = None
    for side in h.succ:
        sb = blocks[side]
        if sb.kind != "cond" or sb.stmts:
            return False
        cc = sb.cond
        if not (isinstance(cc, Bin) and cc.op in ("CompareGe", "CompareLe") and is_pseudo(cc.a, a.name, d)
                and is_pseudo(cc.b)):
            return False
        lim = cc.b
        t, e = [blocks[x] for x in sb.succ]
        if not (t.kind == "goto" and len(t.stmts) == 1 and isinstance(t.stmts[0], D.Assign)
                and isinstance(t.stmts[0].target, Reg) and is_pseudo(t.stmts[0].value, a.name, d)):
            return False
        if var is not None and (var != t.stmts[0].target.n or body != t.succ[0] or exit_ != e.id):
            return False
        var, body, exit_ = t.stmts[0].target.n, t.succ[0], e.id
    preps = find_prep(h, blocks, D, (z.name, lim.name, a.name), d)
    if len(preps) > 1:
        names = (z.name, lim.name, a.name)
        nb = join_preps(h, blocks, [pb for pb, _ in preps],
                        lambda x: isinstance(x, D.Assign) and is_pseudo(x.target, None, d) and x.target.name in names)
        if nb is not None:
            preps = find_prep(h, blocks, D, names, d)
    if len(preps) != 1:
        return False
    pb, vals = preps[0]
    start = vals[a.name]
    step = strip_plus0(vals[z.name])
    limit = strip_plus0(vals[lim.name])
    # start - Z  ->  start (LPH_JIT loops compute start - step before the
    # push: the step's expression, or both folded to constants)
    if isinstance(start, Bin) and start.op == "Sub" and (is_pseudo(start.b, z.name, d) or
                                                        _same(start.b, step)):
        start = start.a
    elif isinstance(start, Const) and isinstance(step, Const) and _num(start.v) and _num(step.v):
        start = Const(start.v + step.v)
    else:
        return False
    for side in h.succ:
        sb = blocks[side]
        for x in sb.succ:
            blocks.pop(x, None) if blocks.get(x) is not None and blocks[x].kind == "goto" and \
                blocks[x].succ == [body] else None
        blocks.pop(side, None)
    h.stmts = []
    h.kind = "for"
    h.cond = None
    h.succ = [body, exit_]
    lst = LoopExprs([start, limit, step])
    h.values = (var, lst)
    place_prep(pb, lst, D, lambda s: isinstance(s, D.Assign) and isinstance(s.target, Pseudo)
               and s.target.depth == d and s.target.name in (z.name, lim.name, a.name))
    _recompute(blocks)
    if pre:
        import copy
        _moves_to_latches(h, pb, pre, blocks)
        pb.stmts += [copy.copy(x) for x in pre]
    return True


def _run_once_for(h, s, blocks, D):
    """try_numeric's header with the prep in the same block: substitute the
    prep values (start, limit, step) for the VM's loop slots in the header
    and its two compare blocks. Returns False (not a `for`)."""
    d = s.target.depth
    vals = {x.target.name: x.value for x in h.stmts[:-1]
            if isinstance(x, D.Assign) and is_pseudo(x.target, None, d)}
    a, z = s.target.name, s.value.b.name
    if a not in vals or z not in vals:
        return False
    step, start = strip_plus0(vals[z]), vals[a]
    if not (isinstance(start, Bin) and start.op == "Sub" and is_pseudo(start.b, z, d)):
        return False
    sub = {nm: strip_plus0(v) for nm, v in vals.items()}
    sub[a], sub[z] = start.a, step
    import codegen

    def fn(x):
        return sub.get(x.name) if isinstance(x, Pseudo) and x.depth == d and x.name in sub else None
    h.stmts = [x for x in h.stmts[:-1] if not (isinstance(x, D.Assign) and is_pseudo(x.target, None, d))]
    h.cond = codegen.map_expr(h.cond, fn)
    for side in h.succ:
        sb = blocks[side]
        if sb.cond is not None:
            sb.cond = codegen.map_expr(sb.cond, fn)
        for t in sb.succ:
            for st in blocks[t].stmts:
                if isinstance(st, D.Assign):
                    st.value = codegen.map_expr(st.value, fn)
    def const_of(x):
        # a register the block set to a constant (`r9 = 182`) before the prep
        if isinstance(x, Reg):
            for st in reversed(h.stmts):
                if isinstance(st, D.Assign) and isinstance(st.target, Reg) and st.target.n == x.n:
                    return st.value if isinstance(st.value, Const) else None
        return x
    cmp = blocks[h.succ[0]].cond
    lim, step, first = const_of(getattr(cmp, "b", None)), const_of(step), const_of(start.a)
    if all(isinstance(x, Const) and _num(x.v) for x in (first, step, lim)):
        # constant bounds: whether it runs is known (`for i = 1, 182`)
        side = blocks[h.succ[0] if step.v <= 0 else h.succ[1]]
        runs = first.v >= lim.v if step.v <= 0 else first.v <= lim.v
        h.kind, h.cond, h.succ = "goto", None, [side.succ[0] if runs else side.succ[1]]
        _recompute(blocks)
    return False


def _num(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool)


def _same(a, b):
    import ir
    return ir.fmt_expr(a) == ir.fmt_expr(b)


def strip_plus0(e):
    if isinstance(e, Bin) and e.op == "Add" and isinstance(e.b, Const) and e.b.v == 0:
        return e.a
    return e


def try_generic(h, blocks, D):
    if h.kind != "cond" or not h.stmts or not isinstance(h.stmts[-1], D.CallStmt):
        return False
    call = h.stmts[-1]
    # register moves before the iterator call (Luraph resets registers there)
    # run before every call: equivalently once before the loop and at the end
    # of every iteration that continues (the latches), as long as they are pure
    pre = h.stmts[:-1]
    if not _pure_moves(pre, D):
        return False
    if not (is_pseudo(call.fn, "a") or is_pseudo(call.fn)) or call.args.items or call.args.tail is not None:
        return False
    it = call.fn
    if not (isinstance(h.cond, TempVal) and h.cond.t == call.t and h.cond.i == 1):
        return False
    bb = blocks[h.succ[0]]
    vars_ = []
    rest = []
    for s in bb.stmts:
        if not rest and isinstance(s, D.Assign) and isinstance(s.target, Reg) and isinstance(s.value, TempVal) \
                and s.value.t == call.t and s.value.i == len(vars_) + 2:
            vars_.append(s.target.n)
        else:
            rest.append(s)
    if not vars_:
        return False
    # the rest of the body must not use the temp any more
    preps = []
    for p in h.preds:
        pb = blocks[p]
        for s in pb.stmts:
            if isinstance(s, D.Assign) and isinstance(s.target, Pseudo) and s.target.name == it.name and \
                    s.target.depth == it.depth and isinstance(s.value, D.GenIter):
                preps.append((pb, s))
    if len(preps) > 1:
        def is_it(x):
            return isinstance(x, D.Assign) and isinstance(x.target, Pseudo) and x.target.name == it.name \
                and x.target.depth == it.depth and isinstance(x.value, D.GenIter)
        nb = join_preps(h, blocks, [pb for pb, _ in preps], is_it)
        if nb is not None:
            preps = [(nb, nb.stmts[-1])]
    if len(preps) != 1:
        return False
    pb, ps = preps[0]
    args = ps.value.args
    items = list(args.items[1:]) if args is not None else []   # drop the VM object
    if pre:
        # the iterator expressions are evaluated before the moves (loop prep first)
        written = {s.target.n for s in pre if isinstance(s.target, Reg)}
        if any(isinstance(x, Reg) and x.n in written for e in (args.items if args else []) for x in _walk(e)):
            return False
    bb.stmts = rest
    if pre:
        _moves_to_latches(h, pb, pre, blocks)
    h.stmts = []
    h.kind = "forin"
    h.cond = None
    if args is not None and args.tail is not None:
        import codegen
        items.append(codegen.TailRef(args.tail))      # for k, v in pairs(t): f, s, ctl from a call
    lst = LoopExprs(items)
    h.values = (vars_, lst)
    place_prep(pb, lst, D, lambda s: s is ps)
    if pre:
        import copy
        pb.stmts += [copy.copy(s) for s in pre]
    return True


def _walk(e):
    st = [e]
    while st:
        x = st.pop()
        yield x
        if hasattr(x, "__dict__"):
            st += [v for v in x.__dict__.values() if hasattr(v, "__dict__") and not isinstance(v, type)]


class LoopExprs(list):
    """The expressions of a for header (start, limit, step / the iterator
    triple). They are evaluated once, before the loop: the prep block holds a
    ForPrep statement that owns them (uses, renaming, inlining), the header
    keeps this same list for rendering."""


def place_prep(pb, lst, D, is_prep):
    """Put ForPrep(lst) in the prep block after its last loop-prep statement."""
    at = None
    for i, s in enumerate(pb.stmts):
        if is_prep(s):
            at = i
    pb.stmts.insert(len(pb.stmts) if at is None else at + 1, D.ForPrep(lst))


def join_preps(h, blocks, pbs, is_prep):
    """Several predecessors of loop header h end with the same prep
    statements (the header was reached with two front end states, merged
    later): move the prep into one new block that they all go to. Returns
    that block, or None if the preps differ or are not the blocks' last
    statements before a plain jump to h."""
    import ir
    import structure
    tails = []
    for pb in pbs:
        if pb.kind != "goto" or pb.succ != [h.id]:
            return None
        k = len(pb.stmts)
        while k > 0 and is_prep(pb.stmts[k - 1]):
            k -= 1
        if k == len(pb.stmts) or any(is_prep(x) for x in pb.stmts[:k]):
            return None
        tails.append(k)
    texts = {tuple(ir.fmt_stmt(x) for x in pb.stmts[k:]) for pb, k in zip(pbs, tails)}
    if len(texts) != 1:
        return None
    nb = structure.Block(max(blocks) + 1)
    nb.stmts = list(pbs[0].stmts[tails[0]:])
    nb.kind = "goto"
    nb.succ = [h.id]
    nb.origin = pbs[0].origin
    blocks[nb.id] = nb
    for pb, k in zip(pbs, tails):
        del pb.stmts[k:]
        pb.succ = [nb.id]
    _recompute(blocks)
    return nb


def _recompute(blocks):
    for b in blocks.values():
        b.preds = []
    for b in blocks.values():
        for s in b.succ:
            if s in blocks:
                blocks[s].preds.append(b.id)
