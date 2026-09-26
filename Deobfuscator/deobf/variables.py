"""
Variable recovery for the devirtualizer.

The VM reuses registers for unrelated locals, so register numbers are not
variables. Here:

  webs()        per register, reaching definitions over the CFG; every use
                joins the definitions that reach it (union-find). Each web
                is one source variable. Registers read with no definition
                reaching them are nil (Luraph relies on fresh frames).
  rename()      Reg(n) occurrences -> LocalName(web name); for-loop variables
                and closure captures included.
  declare()     on the structured AST: each variable gets `local` in the
                innermost block that contains all its occurrences (at its
                first plain assignment there, `local x = v`), hoisted out of
                loops whose iterations carry its value.
"""
import codegen as CG
import structure as ST
from luasym import Reg, Const, Pseudo, ClosureExpr, LTable, Global


# --------------------------------------------------------------------------
# occurrences on the CFG

def closure_regs(c):
    """Parent registers a ClosureExpr captures by reference (boxes)."""
    out = []
    for e in c.upvals:
        if type(e).__name__ == "MaybeBox":
            out.append(e.reg)
        elif isinstance(e, LTable):
            vals = list(e.h.values())
            if any(type(v).__name__ == "RegFile" for v in vals):
                out += [v for v in vals if isinstance(v, int)][:1]
        elif isinstance(e, Reg):
            out.append(e.n)
    return out + list(getattr(c, "frame_regs", ()))


def closure_ref_regs(c):
    """Only the by-reference captures (these keep the local shared)."""
    out = []
    for e in c.upvals:
        if type(e).__name__ == "MaybeBox":
            out.append(e.reg)
        elif isinstance(e, LTable):
            vals = list(e.h.values())
            if any(type(v).__name__ == "RegFile" for v in vals):
                out += [v for v in vals if isinstance(v, int)][:1]
    return out + list(getattr(c, "frame_regs", ()))


def expr_reg_occ(e):
    """Registers read by an expression, including closure captures."""
    out = []
    for x in CG.walk(e):
        if isinstance(x, Reg):
            out.append(x.n)
        elif isinstance(x, ClosureExpr):
            out += closure_regs(x)
    return out


def stmt_io(st):
    """(uses, defs) of registers for one simplified statement."""
    uses, defs = [], []
    if isinstance(st, CG.AssignS):
        for t in st.targets:
            if isinstance(t, Reg):
                defs.append(t.n)
            elif not isinstance(t, Pseudo):
                uses += expr_reg_occ(t)
        for v in st.values.items:
            uses += expr_reg_occ(v)
        if st.values.tail is not None:
            uses += expr_reg_occ(CG.TailRef(st.values.tail))
    elif isinstance(st, (CG.CallS, CG.TempDef)):
        uses += expr_reg_occ(st.call)
    elif isinstance(st, CG.SetListS):
        uses += expr_reg_occ(st.tbl)
        for v in st.values.items:
            uses += expr_reg_occ(v)
        if st.values.tail is not None:
            uses += expr_reg_occ(CG.TailRef(st.values.tail))
    elif isinstance(st, CG.ForPrepS):
        for v in st.exprs:
            uses += expr_reg_occ(v)
    return uses, defs


def term_io(b):
    uses, defs = [], []
    if b.kind == "cond":
        uses += expr_reg_occ(b.cond)
    elif b.kind == "ret" and b.values is not None:
        for v in b.values.items:
            uses += expr_reg_occ(v)
        if b.values.tail is not None:
            uses += expr_reg_occ(CG.TailRef(b.values.tail))
    elif b.kind == "for":
        defs.append(b.values[0])
    elif b.kind == "forin":
        defs += list(b.values[0])
    return uses, defs


class UF:
    def __init__(self):
        self.p = {}

    def find(self, x):
        p = self.p
        p.setdefault(x, x)
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.p[b] = a


def stmt_caps(st):
    """(captured-by-reference registers, closed registers) of a statement."""
    caps, closes = [], []
    if isinstance(st, CG.CloseS):
        closes.append(st.reg)
    else:
        for v in stmt_exprs(st):
            for x in CG.walk(v):
                if isinstance(x, ClosureExpr):
                    caps += closure_ref_regs(x)
    return caps, closes


def stmt_exprs(st):
    """Every expression of a simplified statement (targets included)."""
    out = []
    if isinstance(st, CG.AssignS):
        out += [t for t in st.targets if not isinstance(t, (Reg, Pseudo))]
        out += list(st.values.items)
        if st.values.tail is not None:
            out.append(CG.TailRef(st.values.tail))
    elif isinstance(st, (CG.CallS, CG.TempDef)):
        out.append(st.call)
    elif isinstance(st, CG.SetListS):
        out.append(st.tbl)
        out += list(st.values.items)
        if st.values.tail is not None:
            out.append(CG.TailRef(st.values.tail))
    elif isinstance(st, CG.ForPrepS):
        out += list(st.exprs)
    return out


def term_exprs(b):
    out = []
    if b.kind == "cond":
        out.append(b.cond)
    elif b.kind == "ret" and b.values is not None:
        out += list(b.values.items)
        if b.values.tail is not None:
            out.append(CG.TailRef(b.values.tail))
    return out


def webs(entry, blocks):
    """Returns (use_web, def_web): maps from occurrence ids to web ids.
    Occurrence ids: ("d", block, idx, reg) for defs (idx = len(stmts) for the
    terminator), ("u", block, idx, reg) for uses. A use with no reaching
    definition maps to None (nil).
    A local captured by reference stays one variable while it is open: from
    the closure creation until Luraph's close op, redefinitions of that
    register join the captured web (the closure sees them)."""
    events = {}
    for b in blocks.values():
        ev = []
        for i, st in enumerate(b.stmts):
            u, d = stmt_io(st)
            caps, closes = stmt_caps(st)
            for r in caps:
                ev.append((i, "c", r))
            for r in u:
                ev.append((i, "u", r))
            for r in d:
                ev.append((i, "d", r))
            for r in closes:
                ev.append((i, "x", r))
        u, d = term_io(b)
        for v in term_exprs(b):
            for x in CG.walk(v):
                if isinstance(x, ClosureExpr):
                    for r in closure_ref_regs(x):
                        ev.append((len(b.stmts), "c", r))
        for r in u:
            ev.append((len(b.stmts), "u", r))
        for r in d:
            ev.append((len(b.stmts), "d", r))
        events[b.id] = ev
    order = ST.rpo(entry, lambda n: blocks[n].succ)
    preds = {bid: [] for bid in blocks}
    for b in blocks.values():
        for s_ in b.succ:
            if s_ in preds:
                preds[s_].append(b.id)

    def transfer(bid, inn):
        cur = dict(inn)
        for i, k, r in events[bid]:
            if k == "d":
                cur[r] = frozenset([("d", bid, i, r)])
            elif k == "c":
                if not cur.get(r):
                    # captured before any assignment: the local exists (nil)
                    cur[r] = frozenset([("c", bid, i, r)])
                cur[("o", r)] = cur.get(("o", r), frozenset()) | cur.get(r, frozenset())
            elif k == "x":
                cur.pop(("o", r), None)
        return cur

    IN = {bid: {} for bid in blocks}
    OUT = {bid: {} for bid in blocks}
    changed = True
    while changed:
        changed = False
        for bid in order:
            inn = {}
            for p in preds[bid]:
                for r, ds in OUT[p].items():
                    cur = inn.get(r)
                    inn[r] = ds if cur is None else (cur | ds)
            IN[bid] = inn
            out = transfer(bid, inn)
            if out != OUT[bid]:
                OUT[bid] = out
                changed = True
    uf = UF()
    use_web = {}
    def_web = {}
    for bid, ev in events.items():
        cur = dict(IN[bid])
        for i, k, r in ev:
            if k == "u":
                ds = cur.get(r)
                key = ("u", bid, i, r)
                if ds:
                    ds = list(ds)
                    for d in ds[1:]:
                        uf.union(ds[0], d)
                    use_web[key] = ds[0]
                else:
                    use_web[key] = None
            elif k == "c":
                if not cur.get(r):
                    syn = ("c", bid, i, r)
                    uf.find(syn)
                    cur[r] = frozenset([syn])
                ds = list(cur.get(r, ()))
                for d in ds[1:]:
                    uf.union(ds[0], d)
                cur[("o", r)] = cur.get(("o", r), frozenset()) | cur.get(r, frozenset())
            elif k == "d":
                d = ("d", bid, i, r)
                uf.find(d)
                for o in cur.get(("o", r), ()):
                    uf.union(o, d)
                cur[r] = frozenset([d])
                def_web[d] = d
            elif k == "x":
                cur.pop(("o", r), None)
    for k, v in use_web.items():
        if v is not None:
            use_web[k] = uf.find(v)
    for k in def_web:
        def_web[k] = uf.find(k)
    return use_web, def_web


def rename(entry, blocks, prefix, captured):
    """Replace registers by LocalName variables. Returns {web: name}.
    `captured`: registers captured by closures (never split: one variable)."""
    use_web, def_web = webs(entry, blocks)
    names = {}
    counter = {}
    # webs defined by for-loop headers stay separate variables
    forwebs = set()
    for b in blocks.values():
        if b.kind in ("for", "forin"):
            regs = [b.values[0]] if b.kind == "for" else list(b.values[0])
            for r in regs:
                d = ("d", b.id, len(b.stmts), r)
                if d in def_web:
                    forwebs.add(def_web[d])

    def name_of(web, reg):
        if reg in captured and web not in forwebs:
            web = ("cap", reg)
        if web is None:
            return None
        n = names.get(web)
        if n is None:
            k = counter.get(reg, 0)
            counter[reg] = k + 1
            n = names[web] = "%s%d" % (prefix, reg) + ("" if k == 0 else "_%d" % k)
        return n

    def ren_use(bid, i):
        def fn(x):
            if isinstance(x, Reg):
                w = use_web.get(("u", bid, i, x.n), "missing")
                if w == "missing":
                    return None
                nm = name_of(w, x.n)
                return Const(None) if nm is None else CG.LocalName(nm)
            if isinstance(x, ClosureExpr):
                x.capnames = {}
                for r in closure_regs(x):
                    w = use_web.get(("u", bid, i, r))
                    x.capnames[r] = name_of(w, r) or "nil"
                return x
            return None
        return fn

    def ren_def(bid, i, reg):
        return CG.LocalName(name_of(def_web[("d", bid, i, reg)], reg))

    used = {w for w in use_web.values() if w is not None}

    def dead(bid, i, reg):
        w = def_web.get(("d", bid, i, reg))
        return w is not None and w not in used and reg not in captured

    for b in blocks.values():
        # dead stores: a register assignment nobody reads (Luraph clears
        # registers when locals go out of scope)
        keep = []
        for i, st in enumerate(b.stmts):
            if isinstance(st, CG.AssignS) and len(st.targets) == 1 and isinstance(st.targets[0], Reg)                     and dead(b.id, i, st.targets[0].n):
                vals = st.values
                # Luraph's vararg pack (table.pack(...)) is pure
                pure_pack = len(vals.items) == 1 and isinstance(vals.items[0], CG.CallE) and \
                    isinstance(vals.items[0].fn, Global) and vals.items[0].fn.name == "table.pack"
                if vals.tail is None and len(vals.items) == 1 and (pure_pack or (
                        not CG.has_side_effects(vals.items[0])
                        and not any(isinstance(x, ClosureExpr) for x in CG.walk(vals.items[0])))):
                    keep.append(None)
                    continue
                if vals.tail is not None and not vals.items and isinstance(vals.tail, CG.InlineTail):
                    keep.append(CG.CallS(vals.tail.call))
                    continue
                if len(vals.items) == 1 and vals.tail is None and isinstance(vals.items[0], CG.CallE):
                    keep.append(CG.CallS(vals.items[0]))
                    continue
            keep.append(st)
        b.stmts = [x if x is not None else CG.CommentS("") for x in keep]
    for b in blocks.values():
        for i, st in enumerate(b.stmts):
            fu = ren_use(b.id, i)
            if isinstance(st, CG.AssignS):
                tg = []
                for t in st.targets:
                    if isinstance(t, Reg):
                        tg.append(ren_def(b.id, i, t.n))
                    elif isinstance(t, Pseudo):
                        tg.append(t)
                    else:
                        tg.append(CG.map_expr(t, fu))
                b.stmts[i] = CG.AssignS(tg, CG.map_multi(st.values, fu))
            else:
                b.stmts[i] = CG.map_stmt(st, lambda e: CG.map_expr(e, fu), lambda m: CG.map_multi(m, fu))
        n = len(b.stmts)
        fu = ren_use(b.id, n)
        if b.kind == "cond":
            b.cond = CG.map_expr(b.cond, fu)
        elif b.kind == "ret" and b.values is not None:
            b.values = CG.map_multi(b.values, fu)
        elif b.kind == "for":
            # (the header expressions were renamed with their ForPrepS)
            b.values = (ren_def(b.id, n, b.values[0]), b.values[1])
        elif b.kind == "forin":
            b.values = ([ren_def(b.id, n, v) for v in b.values[0]], b.values[1])
    return names


# --------------------------------------------------------------------------
# declarations on the structured AST

def names_in_expr(e):
    out = []
    for x in CG.walk(e):
        if isinstance(x, CG.LocalName):
            out.append(x.name)
        elif isinstance(x, CG.FuncE):
            out += list(getattr(x, "captures", ()))
    return out


def stmt_names(st):
    """(names read, names written) directly by a simple statement."""
    reads, writes = [], []
    if isinstance(st, CG.AssignS):
        for t in st.targets:
            if isinstance(t, CG.LocalName):
                writes.append(t.name)
            else:
                reads += names_in_expr(t)
        for v in st.values.items:
            reads += names_in_expr(v)
        if st.values.tail is not None:
            reads += names_in_expr(CG.TailRef(st.values.tail))
    elif isinstance(st, (CG.CallS, CG.TempDef)):
        reads += names_in_expr(st.call)
    elif isinstance(st, CG.SetListS):
        reads += names_in_expr(st.tbl)
        for v in st.values.items:
            reads += names_in_expr(v)
        if st.values.tail is not None:
            reads += names_in_expr(CG.TailRef(st.values.tail))
    elif isinstance(st, CG.ForPrepS):
        for v in st.exprs:
            reads += names_in_expr(v)
    elif isinstance(st, ST.SReturn) and st.values is not None:
        for v in st.values.items:
            reads += names_in_expr(v)
        if st.values.tail is not None:
            reads += names_in_expr(CG.TailRef(st.values.tail))
    return reads, writes


def occurrences(stmts, path, occ):
    """occ[name] -> list of paths (tuple of (block id, index)) where the name occurs."""
    for i, st in enumerate(stmts):
        here = path + ((id(stmts), i),)
        if isinstance(st, ST.SIf):
            for n in names_in_expr(st.cond):
                occ.setdefault(n, []).append(here)
            occurrences(st.then, here, occ)
            occurrences(st.els, here, occ)
        elif isinstance(st, ST.SLoop):
            if st.kind == "for":
                for e in st.forinfo[1]:
                    for n in names_in_expr(e):
                        occ.setdefault(n, []).append(here)
            elif st.kind == "forin":
                for e in st.forinfo[1]:
                    for n in names_in_expr(e):
                        occ.setdefault(n, []).append(here)
            if st.cond is not None:
                for n in names_in_expr(st.cond):
                    occ.setdefault(n, []).append(here)
            occurrences(st.body, here, occ)
        elif isinstance(st, DoBlock):
            occurrences(st.body, here, occ)
        else:
            r, w = stmt_names(st)
            for n in r + w:
                occ.setdefault(n, []).append(here)


def loop_vars(stmts, out):
    for st in stmts:
        if isinstance(st, ST.SIf):
            loop_vars(st.then, out)
            loop_vars(st.els, out)
        elif isinstance(st, ST.SLoop):
            if st.kind == "for":
                out.add(st.forinfo[0].name)
            elif st.kind == "forin":
                out |= {v.name for v in st.forinfo[0]}
            loop_vars(st.body, out)


def exposed_reads(stmts):
    """Names read before being definitely assigned (in execution order)."""
    exposed = set()

    def run(block, assigned):
        a = set(assigned)
        for st in block:
            if isinstance(st, ST.SIf):
                exposed.update(set(names_in_expr(st.cond)) - a)
                t = run(st.then, a)
                e = run(st.els, a)
                a = t & e
            elif isinstance(st, ST.SLoop):
                if st.kind == "for":
                    for x in st.forinfo[1]:
                        exposed.update(set(names_in_expr(x)) - a)
                    run(st.body, a | {st.forinfo[0].name})
                elif st.kind == "forin":
                    for x in st.forinfo[1]:
                        exposed.update(set(names_in_expr(x)) - a)
                    run(st.body, a | {v.name for v in st.forinfo[0]})
                else:
                    run(st.body, a)
            else:
                r, w = stmt_names(st)
                exposed.update(set(r) - a)
                a |= set(w)
        return a
    run(stmts, set())
    return exposed


def declare(body, params=(), own=None):
    """Insert `local` declarations; returns the body. `own`: the names of
    this function's variables (anything else is an upvalue: not declared)."""
    occ = {}
    occurrences(body, (), occ)
    fvars = set()
    loop_vars(body, fvars)
    blocks_by_id = {}
    carried = {}       # loop body block id -> names carried across iterations

    def index(stmts):
        blocks_by_id[id(stmts)] = stmts
        for st in stmts:
            if isinstance(st, ST.SIf):
                index(st.then)
                index(st.els)
            elif isinstance(st, ST.SLoop):
                carried[id(st.body)] = exposed_reads(st.body)
                index(st.body)
    index(body)
    decls = {}
    assigned = set()
    assigned_names(body, assigned)
    for name, paths in occ.items():
        # (a register captured by reference keeps one name: it can be a
        # loop variable somewhere and a plain local elsewhere)
        if (name in fvars and name not in assigned) or name in params or (own is not None and name not in own):
            continue
        common = list(paths[0])
        for p in paths[1:]:
            k = 0
            while k < len(common) and k < len(p) and common[k] == p[k]:
                k += 1
            del common[k:]
        # start at the root block: where do all occurrences continue?
        blk = id(body)
        at = None
        depth = 0
        while True:
            nxt = {p[depth] for p in paths if len(p) > depth}
            nb = {bid for bid, _ in nxt}
            if len(nb) != 1 or any(len(p) <= depth for p in paths):
                break
            bid = nb.pop()
            if bid != blk:
                # entering a sub-block of the common statement above
                if bid in carried and name in carried[bid]:
                    break
                blk = bid
            at = (blk, min(i for b_, i in nxt))
            if depth < len(common):
                depth += 1
                continue
            break
        if at is None:
            at = (id(body), min(p[0][1] for p in paths))
        decls.setdefault(at[0], []).append((at[1], name))
    for bid, lst in decls.items():
        stmts = blocks_by_id[bid]
        at = {}
        for idx, name in lst:
            at.setdefault(idx, []).append(name)
        # from the end, so earlier insertions don't shift later indexes
        for idx in sorted(at, reverse=True):
            names = at[idx]
            st = stmts[idx] if idx < len(stmts) else None
            if isinstance(st, CG.AssignS) and not getattr(st, "is_local", False)                     and all(isinstance(t, CG.LocalName) for t in st.targets)                     and sorted(t.name for t in st.targets) == sorted(names)                     and len(set(names)) == len(names)                     and not set(names) & set(stmt_names_values(st)):
                # `local a, b = f()`: every target is declared right here
                st.is_local = True
                continue
            if isinstance(st, CG.AssignS) and not getattr(st, "is_local", False) and len(st.targets) == 1                     and isinstance(st.targets[0], CG.LocalName) and st.targets[0].name in names                     and st.targets[0].name not in stmt_names_values(st):
                st.is_local = True
                names = [n for n in names if n != st.targets[0].name]
            if names:
                stmts.insert(idx, CG.LocalS(names, None))
    return body


def stmt_names_values(st):
    """Names an assignment reads (its values and the lvalue sub-expressions)."""
    return stmt_names(st)[0]


# --------------------------------------------------------------------------
# Luau allows 200 active locals per function. The original source used
# scopes (do ... end, nested blocks) that leave no trace in the bytecode, so
# a big block can end up with too many declarations: wrap closed segments
# (every variable declared inside is dead after it) in do ... end.

class DoBlock:
    def __init__(self, body):
        self.body = body


def assigned_names(stmts, out, bound=frozenset()):
    """Names plain assignments write outside the loops that bind them as
    loop variables."""
    for st in stmts:
        if isinstance(st, ST.SIf):
            assigned_names(st.then, out, bound)
            assigned_names(st.els, out, bound)
        elif isinstance(st, ST.SLoop):
            b = set(bound)
            if st.kind == "for":
                b.add(st.forinfo[0].name)
            elif st.kind == "forin":
                b |= {v.name for v in st.forinfo[0]}
            assigned_names(st.body, out, b)
        elif isinstance(st, DoBlock):
            assigned_names(st.body, out, bound)
        elif isinstance(st, CG.AssignS):
            out.update(t.name for t in st.targets if isinstance(t, CG.LocalName) and t.name not in bound)


def declared_here(st):
    if isinstance(st, CG.LocalS):
        return list(st.names)
    if isinstance(st, CG.AssignS) and getattr(st, "is_local", False):
        return [t.name for t in st.targets if isinstance(t, CG.LocalName)]
    return []


def names_anywhere(st):
    occ = {}
    occurrences(st.body if isinstance(st, DoBlock) else [st], (), occ)
    return set(occ)


def limit_locals(stmts, outer=0, budget=180):
    """Keep the locals active at any point (enclosing blocks' + this block's)
    under Luau's limit of 200: cut the block into do ... end segments."""
    total = sum(len(declared_here(s)) for s in stmts)
    if outer + total > budget:
        stmts = fit_locals(stmts, budget - outer)
    # recurse with the number of locals active at each nested statement
    active = outer
    for st in stmts:
        if isinstance(st, ST.SIf):
            st.then[:] = limit_locals(st.then, active, budget)
            st.els[:] = limit_locals(st.els, active, budget)
        elif isinstance(st, ST.SLoop):
            extra = 1 if st.kind == "for" else len(st.forinfo[0]) if st.kind == "forin" else 0
            st.body[:] = limit_locals(st.body, active + extra, budget)
        elif isinstance(st, DoBlock):
            st.body[:] = limit_locals(st.body, active, budget)
        active += len(declared_here(st))
    return stmts


def _hoistable(st):
    """Names this statement declares that can be declared earlier instead
    (a bare `local a, b` or `local a, b = ...` assignment)."""
    if isinstance(st, CG.LocalS) and st.values is None:
        return list(st.names)
    if isinstance(st, CG.AssignS) and getattr(st, "is_local", False):
        return [t.name for t in st.targets if isinstance(t, CG.LocalName)]
    return []


def _unlocalize(stmts, hoisted):
    """The statements with the declarations of `hoisted` names removed: they
    become plain assignments (the names are declared in front instead)."""
    out = []
    for st in stmts:
        if isinstance(st, CG.LocalS) and st.values is None:
            names = [x for x in st.names if x not in hoisted]
            if names:
                out.append(CG.LocalS(names, None))
            continue
        if isinstance(st, CG.AssignS) and getattr(st, "is_local", False) and \
                any(isinstance(t, CG.LocalName) and t.name in hoisted for t in st.targets):
            keep = [t.name for t in st.targets if isinstance(t, CG.LocalName) and t.name not in hoisted]
            if keep:
                out.append(CG.LocalS(keep, None))
            st.is_local = False
        out.append(st)
    return out


def fit_locals(stmts, room):
    """The block with at most `room` locals active at once (as far as
    possible): small do ... end segments (wrap_segments) when they get there,
    else a split into a closed prefix and the rest (split_block)."""
    if sum(len(declared_here(s)) for s in stmts) <= room:
        return stmts
    if wrap_segments(stmts, room, dry=True) > room:
        got = split_block(stmts, room)
        if got is not None:
            return got
    return wrap_segments(stmts, room)


def split_block(stmts, room):
    """Cut a block with too many locals into a closed prefix, wrapped in
    do ... end, and the rest. The cut goes where the fewest locals live
    across it (they are declared, without a value, in front of the prefix)
    and the peak count is lowest: e.g. a loader part and the script it runs,
    whose locals the original kept in separate scopes. Recursive on both
    parts; None if no cut lowers the peak."""
    n = len(stmts)
    decl_at = [declared_here(s) for s in stmts]
    total = sum(len(d) for d in decl_at)
    if total <= room:
        return stmts
    last, first, hoistable = {}, {}, set()
    for i, s in enumerate(stmts):
        for nm in names_anywhere(s):
            last[nm] = i
        for nm in decl_at[i]:
            first.setdefault(nm, i)
        hoistable.update(_hoistable(s))
    # names declared in stmts[:k] and used in stmts[k:], per k (difference arrays)
    cross_d = [0] * (n + 2)
    bad_d = [0] * (n + 2)
    for nm, f in first.items():
        lst = last.get(nm, f)
        if lst > f:
            cross_d[f + 1] += 1
            cross_d[lst + 1] -= 1
            if nm not in hoistable:
                bad_d[f + 1] += 1
                bad_d[lst + 1] -= 1
    best = None
    cross = bad = left = 0
    for k in range(1, n):
        cross += cross_d[k]
        bad += bad_d[k]
        left += len(decl_at[k - 1])
        if bad or left <= cross:
            continue
        peak = max(left, cross + total - left)
        if best is None or (peak, cross) < best[0]:
            best = ((peak, cross), k)
    if best is None or best[0][0] >= total:
        return None
    k = best[1]
    hoisted = {nm for nm, f in first.items() if f < k <= last.get(nm, f)}
    room2 = room - len(hoisted)
    pre = sorted(hoisted, key=lambda nm: first[nm])
    out = [CG.LocalS(pre[j:j + 10], None) for j in range(0, len(pre), 10)]
    out.append(DoBlock(fit_locals(_unlocalize(stmts[:k], hoisted), room2)))
    return out + fit_locals(stmts[k:], room2)


def _segments(stmts, decl_at, last, hoisted):
    """Maximal closed segments: no variable declared inside (and not hoisted)
    is used after the segment. Returns [(start, end_exclusive, n_decls)]."""
    segs = []
    start, cnt, reach = 0, 0, -1
    for i in range(len(stmts)):
        for n in decl_at[i]:
            if n in hoisted:
                continue
            cnt += 1
            reach = max(reach, last.get(n, i))
        if i >= reach:
            segs.append((start, i + 1, cnt))
            start, cnt, reach = i + 1, 0, -1
    if start < len(stmts):
        segs.append((start, len(stmts), cnt))
    return segs


def wrap_segments(stmts, room, chunk=None, dry=False):
    """The original source used scopes (do ... end, nested blocks) that leave
    no trace in the bytecode. Rebuild some: closed segments of the block (every
    local declared inside is dead after it) become do ... end. Locals that
    live long (the script's top-level functions, say) would keep a segment
    from closing: those are declared (without a value) in front of their
    segment instead, longest-lived first, until every segment is small."""
    n = len(stmts)
    last = {}
    decl_at = []
    for i, s_ in enumerate(stmts):
        for nm in names_anywhere(s_):
            last[nm] = i
        decl_at.append(declared_here(s_))
    life = []
    for i, names in enumerate(decl_at):
        for nm in names:
            life.append((last.get(nm, i) - i, nm))
    life.sort(reverse=True)
    if chunk is None:
        chunk = max(20, min(80, room // 3))
    hoisted = set()
    k = 0
    while True:
        segs = _segments(stmts, decl_at, last, hoisted)
        worst = max((c for _, _, c in segs), default=0)
        if worst <= chunk or k >= len(life) or len(hoisted) + chunk >= room:
            break
        # hoist a batch of the longest-lived remaining locals
        for _ in range(max(1, len(life) // 50)):
            if k < len(life):
                hoisted.add(life[k][1])
                k += 1
    if dry:
        # (no changes made) an upper bound of the locals active at once afterwards
        def wraps(a, b, c):
            return c >= 1 and 1 < b - a < n
        inner = [c for a, b, c in segs if wraps(a, b, c)]
        return len(hoisted) + sum(c for a, b, c in segs if not wraps(a, b, c)) + max(inner, default=0)
    rest = {}   # un-localized `local a, b = f()` -> its targets that stay put
    if hoisted:
        # only hoist what actually lets a segment close; keep the rest in place
        for st in stmts:
            if isinstance(st, CG.LocalS):
                st.names = [x for x in st.names if x not in hoisted]
            elif isinstance(st, CG.AssignS) and getattr(st, "is_local", False) and \
                    any(isinstance(t, CG.LocalName) and t.name in hoisted for t in st.targets):
                st.is_local = False
                keep = [t.name for t in st.targets if isinstance(t, CG.LocalName) and t.name not in hoisted]
                if keep:
                    rest[id(st)] = keep
    for min_cnt in (2, 1):
        out = []
        for a, b, cnt in segs:
            seg = []
            for st in stmts[a:b]:
                if isinstance(st, CG.LocalS) and not st.names:
                    continue
                if id(st) in rest:
                    seg.append(CG.LocalS(rest[id(st)], None))
                seg.append(st)
            pre = [nm for i in range(a, b) for nm in decl_at[i] if nm in hoisted]
            for j in range(0, len(pre), 10):
                out.append(CG.LocalS(pre[j:j + 10], None))
            if cnt >= min_cnt and 1 < len(seg) and (b - a) < n:
                out.append(DoBlock(seg))
            else:
                out += seg
        if sum(len(declared_here(s_)) for s_ in out) <= room - 10:
            break
    return out


# --------------------------------------------------------------------------
# parameters: Luraph functions take `...` and copy their parameters out of it
# first thing. Leading `local x = <vararg i>` (i = 1, 2, ...) become params.

def extract_params(body):
    """Luraph functions take `...` and copy their parameters out of it first
    thing: leading `local x = <vararg i>` become named parameters (gaps get
    argN). Every other vararg read is renumbered for the shorter `...`."""
    from luasym import Vararg, VarargTail
    lead = {}
    i = 0
    while i < len(body):
        st = body[i]
        if isinstance(st, CG.AssignS) and getattr(st, "is_local", False) and len(st.targets) == 1                 and len(st.values.items) == 1 and st.values.tail is None                 and isinstance(st.values.items[0], Vararg) and st.values.items[0].i not in lead                 and st.targets[0].name not in lead.values():
            lead[st.values.items[0].i] = st.targets[0].name
            i += 1
            continue
        if isinstance(st, CG.CommentS) and not st.text:
            i += 1
            continue
        break
    # (a parameter may be reassigned later: parameters are plain locals)
    idx, tails = [], []
    vararg_uses(body[i:], idx, tails)
    top = max(list(lead) + idx + [0])
    if tails:
        top = min(top, min(tails) - 1)
    lead = {k: nm for k, nm in lead.items() if k <= top}
    n = top
    names = []
    used = set(lead.values())
    for j in range(1, n + 1):
        nm = lead.get(j)
        if nm is None:
            nm = "arg%d" % j
            while nm in used:
                nm += "_"
            used.add(nm)
        names.append(nm)
    keep = [st for st in body[:i] if not (isinstance(st, CG.AssignS) and len(st.values.items) == 1
                                         and isinstance(st.values.items[0], Vararg)
                                         and st.values.items[0].i in lead)]
    body[:i] = keep

    def fn(x):
        if isinstance(x, Vararg):
            return CG.LocalName(names[x.i - 1]) if x.i <= n else Vararg(x.i - n)
        if isinstance(x, CG.TailRef) and isinstance(x.tail, VarargTail):
            return CG.TailRef(VarargTail(x.tail.start - n))
        return None
    if n:
        map_body(body, fn, set())
    params = names
    if uses_varargs(body):
        params = params + ["..."]
    return params


def written_names(stmts, out):
    for st in stmts:
        if isinstance(st, ST.SIf):
            written_names(st.then, out)
            written_names(st.els, out)
        elif isinstance(st, ST.SLoop):
            written_names(st.body, out)
            if st.kind == "for":
                out.add(st.forinfo[0].name)
            elif st.kind == "forin":
                out |= {v.name for v in st.forinfo[0]}
        elif isinstance(st, DoBlock):
            written_names(st.body, out)
        else:
            out |= set(stmt_names(st)[1])


def vararg_uses(stmts, idx, tails):
    from luasym import Vararg, VarargTail

    def f(x):
        if isinstance(x, Vararg):
            idx.append(x.i)
        elif isinstance(x, CG.TailRef) and isinstance(x.tail, VarargTail):
            tails.append(x.tail.start)
        return None
    map_body(stmts, f, set(), inspect_only=True)


def map_body(stmts, fn, done, inspect_only=False):
    """Apply CG.map_expr(e, fn) to every expression of a structured body
    (not into nested functions, which are rendered already)."""
    def me(e):
        if e is None:
            return None
        if inspect_only:
            for x in CG.walk(e):
                fn(x)
            return e
        return CG.map_expr(e, fn)

    def mm(m):
        if m is None:
            return None
        if inspect_only:
            for x in m.items:
                me(x)
            if m.tail is not None:
                me(CG.TailRef(m.tail))
            return m
        return CG.map_multi(m, fn)

    def lst(exprs):
        if id(exprs) in done:
            return
        done.add(id(exprs))
        exprs[:] = [me(x) for x in exprs]
    for k, st in enumerate(stmts):
        if isinstance(st, ST.SIf):
            st.cond = me(st.cond)
            map_body(st.then, fn, done, inspect_only)
            map_body(st.els, fn, done, inspect_only)
        elif isinstance(st, ST.SLoop):
            st.cond = me(st.cond)
            if st.kind in ("for", "forin"):
                lst(st.forinfo[1])
            map_body(st.body, fn, done, inspect_only)
        elif isinstance(st, DoBlock):
            map_body(st.body, fn, done, inspect_only)
        elif isinstance(st, ST.SReturn):
            st.values = mm(st.values)
        elif isinstance(st, CG.ForPrepS):
            lst(st.exprs)
        elif isinstance(st, CG.LocalS):
            st.values = mm(st.values)
        elif isinstance(st, CG.AssignS):
            st.targets = [t if isinstance(t, (CG.LocalName, Pseudo)) else me(t) for t in st.targets]
            st.values = mm(st.values)
        elif isinstance(st, (CG.CallS, CG.TempDef)):
            st.call = me(st.call)
        elif isinstance(st, CG.SetListS):
            st.tbl = me(st.tbl)
            st.values = mm(st.values)


def uses_varargs(stmts):
    from luasym import Vararg, VarargTail
    found = [False]

    def ex(e):
        for x in CG.walk(e):
            if isinstance(x, Vararg) or (isinstance(x, CG.TailRef) and isinstance(x.tail, VarargTail)):
                found[0] = True

    def multi(m):
        if m is None:
            return
        for x in m.items:
            ex(x)
        if m.tail is not None:
            ex(CG.TailRef(m.tail))

    def blk(stmts):
        for st in stmts:
            if isinstance(st, CG.AssignS):
                for t in st.targets:
                    ex(t)
                multi(st.values)
            elif isinstance(st, (CG.CallS, CG.TempDef)):
                ex(st.call)
            elif isinstance(st, CG.SetListS):
                ex(st.tbl)
                multi(st.values)
            elif isinstance(st, ST.SIf):
                ex(st.cond)
                blk(st.then)
                blk(st.els)
            elif isinstance(st, ST.SLoop):
                blk(st.body)
                if st.kind == "for":
                    for x in st.forinfo[1]:
                        ex(x)
                elif st.kind == "forin":
                    for x in st.forinfo[1]:
                        ex(x)
            elif isinstance(st, ST.SReturn):
                multi(st.values)
            elif isinstance(st, DoBlock):
                blk(st.body)
    blk(stmts)
    return found[0]
