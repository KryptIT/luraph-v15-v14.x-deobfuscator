"""
Readability passes on the structured AST of a lifted function (after
structuring and renaming, before `local` declarations are placed).

  and_or()   The VM compiles `a and b` / `a or b` into branches that store into
             one register. These patterns become expressions again:
               if x then x = A end                  ->  x = x and A
               if not x then x = B end              ->  x = x or B
               if c then x = A else x = c end       ->  x = c and A
               if not c then x = B else x = c end   ->  x = c or B
               x = V; x = x and A                   ->  x = V and A   (same for or)
               x = c; if c then x = A end           ->  x = c and A
               if not c then x = c end              ->  x = c and x   (the result
                   written over an operand's register: Luraph reuses registers)
             Each rewrite is an exact equivalence (short-circuit order kept).
  fold_single_use()  temps back into the statement that reads them (see there).
"""
import codegen as CG
import structure as ST
from luasym import Un, Bin, Const


def key(e):
    k = CG.expr_key(e)
    return None if k.startswith("X") else k


def single_assign(stmts):
    """stmts is exactly `x = v` (one local target, one value): (name, value)."""
    if len(stmts) != 1:
        return None
    st = stmts[0]
    if isinstance(st, CG.AssignS) and len(st.targets) == 1 and isinstance(st.targets[0], CG.LocalName) \
            and len(st.values.items) == 1 and st.values.tail is None and not getattr(st, "is_local", False):
        return st.targets[0].name, st.values.items[0]
    return None


def reads(e, name):
    return any(isinstance(x, CG.LocalName) and x.name == name for x in CG.walk(e))


def assign(name, value):
    return CG.AssignS([CG.LocalName(name)], CG.Multi([value]))


def match_if(st):
    """An if statement that is really `x = <and/or expression>`, or None."""
    t = single_assign(st.then)
    if t is None:
        return None
    name, a = t
    c = st.cond
    neg = isinstance(c, Un) and c.op == "Not"
    base = c.a if neg else c
    op = "Or" if neg else "And"
    if not st.els:
        # if x then x = A end
        if isinstance(base, CG.LocalName) and base.name == name:
            return assign(name, Bin(op, CG.LocalName(name), a))
        # the and/or result written over an operand's register (Luraph reuses them):
        # if not c then x = c end  ->  x = c and x;  if c then x = c end  ->  x = c or x
        kb = key(base)
        if kb is not None and key(a) == kb:
            return assign(name, Bin("And" if neg else "Or", base, CG.LocalName(name)))
        return None
    e = single_assign(st.els)
    if e is None or e[0] != name:
        return None
    kb = key(base)
    if kb is not None and key(e[1]) == kb:
        # if c then x = A else x = c end
        return assign(name, Bin(op, base, a))
    if kb is not None and key(a) == kb:
        # if c then x = c else x = B end  ->  x = c or B
        # if not c then x = c else x = B end  ->  x = c and B
        return assign(name, Bin("And" if neg else "Or", base, e[1]))
    return None


def and_or(stmts):
    out = ST.SBlock()
    for st in stmts:
        if isinstance(st, ST.SIf):
            st.then = and_or(st.then)
            st.els = and_or(st.els)
            r = match_if(st)
            if r is not None:
                st = r
        elif isinstance(st, ST.SLoop):
            st.body = and_or(st.body)
        prev = single_assign([out[-1]]) if out and isinstance(out[-1], CG.AssignS) else None
        # x = c; if c then x = A end  ->  x = c and A   (if not c ...: x = c or B)
        if prev and isinstance(st, ST.SIf) and not st.els:
            t = single_assign(st.then)
            neg = isinstance(st.cond, Un) and st.cond.op == "Not"
            base = st.cond.a if neg else st.cond
            kb = key(base)
            if t and t[0] == prev[0] and kb is not None and key(prev[1]) == kb \
                    and not reads(base, t[0]) and not reads(t[1], t[0]):
                out[-1] = assign(t[0], Bin("Or" if neg else "And", prev[1], t[1]))
                continue
        # x = V; x = x and A  ->  x = V and A
        if prev and isinstance(st, CG.AssignS):
            cur = single_assign([st])
            if cur and cur[0] == prev[0]:
                v = cur[1]
                if isinstance(v, Bin) and v.op in ("And", "Or") and isinstance(v.a, CG.LocalName) \
                        and v.a.name == cur[0] and not reads(v.b, cur[0]):
                    out[-1] = assign(cur[0], Bin(v.op, prev[1], v.b))
                    continue
        out.append(st)
    return out


def _stmt_exprs(st):
    """Expressions a statement evaluates (not nested statement blocks)."""
    out = []
    if isinstance(st, CG.AssignS):
        out += [t for t in st.targets if not isinstance(t, CG.LocalName)]
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
    elif isinstance(st, ST.SIf):
        out.append(st.cond)
    elif isinstance(st, ST.SLoop):
        if st.cond is not None:
            out.append(st.cond)
        if st.forinfo:
            out += [x for x in st.forinfo[1] if x is not None]
    elif isinstance(st, ST.SReturn) and st.values is not None:
        out += list(st.values.items)
        if st.values.tail is not None:
            out.append(CG.TailRef(st.values.tail))
    return [e for e in out if e is not None]


def _sub_blocks(st):
    if isinstance(st, ST.SIf):
        return [st.then, st.els]
    if isinstance(st, ST.SLoop):
        return [st.body]
    return []


def name_counts(stmts, reads=None, writes=None, text=None):
    """Reads / writes of every LocalName in a function body; `text` collects
    the source of nested functions (FuncE, already rendered)."""
    import re
    if reads is None:
        reads, writes, text = {}, {}, []
    for st in stmts:
        if isinstance(st, CG.AssignS):
            for t in st.targets:
                if isinstance(t, CG.LocalName):
                    writes[t.name] = writes.get(t.name, 0) + 1
        if isinstance(st, ST.SLoop) and st.forinfo:
            for v in (st.forinfo[0] if isinstance(st.forinfo[0], (list, tuple)) else [st.forinfo[0]]):
                if isinstance(v, CG.LocalName):
                    writes[v.name] = writes.get(v.name, 0) + 2
        for e in _stmt_exprs(st):
            for x in CG.walk(e):
                if isinstance(x, CG.LocalName):
                    reads[x.name] = reads.get(x.name, 0) + 1
                elif isinstance(x, CG.FuncE):
                    text.append("\n".join(x.lines))
        for b in _sub_blocks(st):
            name_counts(b, reads, writes, text)
    if not hasattr(name_counts, "_re"):
        name_counts._re = re
    return reads, writes, text


def _first_leaf(e):
    """The sub-expression Luau evaluates first."""
    while True:
        if isinstance(e, (Bin, Un)):
            e = e.a
        elif isinstance(e, CG.Index):
            e = e.obj
        elif isinstance(e, CG.CallE):
            e = e.fn
        else:
            return e


def _positions(body):
    """Pre-order numbering of the statements: id -> [index, last index of its
    subtree, the block holding it, the statement holding that block], plus
    the read sites (name -> ids of the statements whose own expressions read
    it, once per read) and write sites (name -> AssignS statements). None if
    the body has a state machine (no textual order)."""
    pos, rsites, wsites = {}, {}, {}
    n = [0]

    def walk(stmts, parent):
        for st in stmts:
            if isinstance(st, (ST.SStateMachine, ST.SGotoState)):
                raise ValueError
            i = n[0]
            n[0] += 1
            info = [i, i, stmts, parent]
            pos[id(st)] = info
            for e in _stmt_exprs(st):
                for x in CG.walk(e):
                    if isinstance(x, CG.LocalName):
                        rsites.setdefault(x.name, []).append(id(st))
            if isinstance(st, CG.AssignS):
                for t in st.targets:
                    if isinstance(t, CG.LocalName):
                        wsites.setdefault(t.name, []).append(st)
            for b in _sub_blocks(st):
                walk(b, st)
            info[1] = n[0] - 1
    try:
        walk(body, None)
    except ValueError:
        return None
    return pos, rsites, wsites


def _same_text(a, b):
    if a is b:
        return True
    r = CG.Renderer()
    return r.expr(a) == r.expr(b)


def _eval_list(st):
    """What a statement evaluates, in Luau order (post-order nodes), or None.
    A subtree shared by a NAMECALL's object and self argument (`f(x):M()`)
    runs once: only its first occurrence counts."""
    seen = set()
    out = []

    def order(e):
        if e is None:
            return
        kids = CG.children(e)
        if kids and not isinstance(e, CG.ClosureExpr):
            if id(e) in seen:
                return
            seen.add(id(e))
            if isinstance(e, CG.CallE) and isinstance(e.fn, CG.Index) and e.args.items \
                    and type(e.fn.obj) is type(e.args.items[0]) and CG.children(e.fn.obj) \
                    and _same_text(e.fn.obj, e.args.items[0]):
                # f(x):M(...): the object is evaluated once (the renderer's method form)
                order(e.fn)
                for c in kids[2:]:
                    order(c)
            elif isinstance(e, CG.NewTableE):
                for k, v in e.items:      # key then value, item by item
                    order(k)
                    order(v)
                if e.tail is not None:
                    order(CG.TailRef(e.tail))
            else:
                for c in kids:          # children() lists operands in evaluation order
                    order(c)
        out.append(e)
    if isinstance(st, ST.SIf):
        order(st.cond)
    elif isinstance(st, CG.CallS):
        order(st.call)
    elif isinstance(st, CG.AssignS):
        for t in st.targets:
            if isinstance(t, CG.Index):
                order(t.obj)
                order(t.key)
        for x in st.values.items:
            order(x)
        if st.values.tail is not None:
            order(CG.TailRef(st.values.tail))
    elif isinstance(st, ST.SReturn) and st.values is not None:
        for x in st.values.items:
            order(x)
        if st.values.tail is not None:
            order(CG.TailRef(st.values.tail))
    else:
        return None
    return out


def _conditional(e, acc):
    """ids of the nodes of e that are evaluated only sometimes (and/or right sides)."""
    def mark(x):
        for y in CG.walk(x):
            acc.add(id(y))
    if isinstance(e, Bin) and e.op in ("And", "Or"):
        mark(e.b)
    elif isinstance(e, CG.IfExp):
        mark(e.a)
        mark(e.b)
    for c in CG.children(e):
        _conditional(c, acc)
    return acc


def _fold_table_store(prev_st, st):
    """x = {...}; x.k = V  ->  x = {..., k = V} (codegen's fold_tables does this
    on the CFG; a V built from and/or branches only becomes one expression
    after structuring). Adjacent statements, V and k don't read x, the table
    has no multret tail; a number key only as the next array slot (explicit
    number keys and positional items don't mix in a constructor)."""
    if not (isinstance(prev_st, CG.AssignS) and len(prev_st.targets) == 1
            and isinstance(prev_st.targets[0], CG.LocalName) and len(prev_st.values.items) == 1
            and prev_st.values.tail is None and isinstance(prev_st.values.items[0], CG.NewTableE)):
        return False
    tbl = prev_st.values.items[0]
    name = prev_st.targets[0].name
    if tbl.tail is not None or not (isinstance(st, CG.AssignS) and len(st.targets) == 1
                                    and len(st.values.items) == 1 and st.values.tail is None):
        return False
    t = st.targets[0]
    if not (isinstance(t, CG.Index) and isinstance(t.obj, CG.LocalName) and t.obj.name == name
            and isinstance(t.key, CG.Const)):
        return False
    v = st.values.items[0]
    if reads(v, name):
        return False
    k = t.key.v
    if isinstance(k, (str, bytes)):
        if any(isinstance(kk, CG.Const) and kk.v == k for kk, _ in tbl.items):
            return False
        prev_st.values = CG.Multi([CG.NewTableE(tbl.items + [(t.key, v)])])
        return True
    if isinstance(k, (int, float)) and not isinstance(k, bool) and k == CG.count_array(tbl) + 1 \
            and not any(kk is not None for kk, _ in tbl.items if not (isinstance(kk, CG.Const) and isinstance(kk.v, (str, bytes)))):
        prev_st.values = CG.Multi([CG.NewTableE(tbl.items + [(None, v)])])
        return True
    return False


def _last_value(e, x):
    """Is x the last value of call e's arguments / constructor e's array items?"""
    if isinstance(e, CG.CallE):
        return e.args.tail is None and bool(e.args.items) and e.args.items[-1] is x
    if isinstance(e, CG.NewTableE):
        return e.tail is None and bool(e.items) and e.items[-1][0] is None and e.items[-1][1] is x
    return False


def fold_single_use(body):
    """x = V; <stmt reading x once>  ->  <stmt with V>
      local flag = a and b; if flag then   ->  if a and b then
      local u = _G.U; local t = u or {}    ->  local t = _G.U or {}
      local o = up; o.k = a and b or c     ->  up.k = a and b or c
    Consecutive temps fold one after another into the same statement
    (`local f = o.M; local a = g(); f(o, a)`  ->  `o:M(g())`).
    V moves past no call: in the statement's evaluation order only reads,
    indexing and and/or/not come before the read of x (codegen's
    `call_before` rule), and a V with calls is never moved into an and/or
    right side. x is read nowhere else afterwards (also not in closures):
    other reads must come textually before `x = V`, and inside a loop x
    must be written earlier in the same iteration by a statement every
    path to `x = V` runs (Luraph reuses registers, so one variable can
    hold several short-lived values: `x = x and y; use(x)`)."""
    import re
    nreads, writes, text = name_counts(body)
    alltext = "\n".join(text)
    where = _positions(body)

    def in_text(name):
        return re.search(r"(?<![\w.])%s(?!\w)" % re.escape(name), alltext) is not None

    def dead_after(name, prev_st, st, n_in_v):
        """Is the value `prev_st` gives x read only by st (and x's other reads harmless)?"""
        others = nreads.get(name, 0) - n_in_v
        if where is None:
            return False
        pos, rsites, wsites = where
        sites = rsites.get(name, [])
        ip = pos[id(prev_st)][0]
        idxs = [pos[s][0] for s in sites if s != id(st)]
        if len(sites) != others + n_in_v:
            return False        # counts disagree (nested closures, stale sites): be safe
        if any(i > ip for i in idxs):
            return False
        # innermost loop around x = V
        chain = []
        cur = prev_st
        loop = None
        while True:
            info = pos.get(id(cur))
            if info is None:
                return False
            chain.append(info[2])
            parent = info[3]
            if parent is None:
                break
            if isinstance(parent, ST.SLoop):
                loop = parent
                break
            cur = parent
        if loop is None:
            return True
        lo, hi = pos[id(loop)][0], pos[id(loop)][1]
        outer = pos[id(loop)][3]
        while outer is not None and not isinstance(outer, ST.SLoop):
            outer = pos[id(outer)][3]
        inside = [i for i in idxs if lo <= i <= hi]
        if len(inside) != len(idxs) and (outer is not None or any(i > lo for i in idxs if i not in inside)):
            return False
        # an unconditional write of x earlier in the iteration, before all of its reads
        first = min(inside) if inside else None
        for w in wsites.get(name, []):
            info = pos.get(id(w))
            if info is None or not any(info[2] is b for b in chain):
                continue
            iw = info[0]
            if w is prev_st:
                if n_in_v == 0 and (first is None or first > iw):
                    return True
                continue
            if iw < ip and (first is None or first > iw) and \
                    not any(reads(e, name) for e in _stmt_exprs(w)):
                return True
        return False

    def try_fold(prev_st, st):
        prev = single_assign([prev_st])
        if prev is None:
            return False
        name, v = prev
        if in_text(name):
            return False
        if isinstance(v, (CG.FuncE, CG.ClosureExpr)):
            return False        # (function() ... end)(x) reads worse than a named local
        order = _eval_list(st)
        if order is None:
            return False
        hits = [x for x in order if isinstance(x, CG.LocalName) and x.name == name]
        if not hits:
            return False
        # x:m(...) reads x once (the self argument is the same read)
        n_self = sum(1 for x in order if isinstance(x, CG.CallE) and isinstance(x.fn, CG.Index)
                     and isinstance(x.fn.obj, CG.LocalName) and x.fn.obj.name == name and x.args.items
                     and isinstance(x.args.items[0], CG.LocalName) and x.args.items[0].name == name)
        if len(hits) - n_self != 1:
            return False
        if CG.expands(v) and any(_last_value(x, hits[0]) for x in order):
            return False        # f((g())) reads worse than a named local (codegen.truncated_use)
        if isinstance(st, ST.SReturn) and CG.expands(v) and st.values.tail is None \
                and st.values.items and st.values.items[-1] is hits[0]:
            return False        # `return g()` would return all of g's values
        for x in order:
            if x is hits[0]:
                break
            if isinstance(x, (CG.CallE, CG.ClosureExpr, CG.FuncE)):
                return False
        if CG.has_side_effects(v):
            cond = set()
            for e in _stmt_exprs(st):
                _conditional(e, cond)
            if id(hits[0]) in cond:
                return False
        n_in_v = sum(1 for x in CG.walk(v) if isinstance(x, CG.LocalName) and x.name == name)
        raw_in_st = sum(1 for e in _stmt_exprs(st) for x in CG.walk(e) if isinstance(x, CG.LocalName) and x.name == name)
        simple_case = writes.get(name) == 1 and n_in_v == 0 and nreads.get(name) == raw_in_st
        if not simple_case and not dead_after(name, prev_st, st, n_in_v):
            return False

        def sub(e):
            return CG.map_expr(e, lambda x: v if isinstance(x, CG.LocalName) and x.name == name else None)
        if isinstance(st, ST.SIf):
            st.cond = sub(st.cond)
        elif isinstance(st, CG.CallS):
            st.call = sub(st.call)
        elif isinstance(st, ST.SReturn):
            st.values = CG.map_multi(st.values, lambda x: v if isinstance(x, CG.LocalName)
                                     and x.name == name else None)
        else:
            st.targets = [t if isinstance(t, CG.LocalName) else sub(t) for t in st.targets]
            st.values = CG.map_multi(st.values, lambda x: v if isinstance(x, CG.LocalName)
                                     and x.name == name else None)
        # bookkeeping: x's reads in st are gone, V's reads now happen in st
        nreads[name] = nreads.get(name, 0) - raw_in_st
        writes[name] = writes.get(name, 0) - 1
        if where is not None:
            pos, rsites, wsites = where
            sites = rsites.get(name, [])
            sites[:] = [s for s in sites if s != id(st)]
            for x in CG.walk(v):
                if isinstance(x, CG.LocalName):
                    lst = rsites.get(x.name, [])
                    lst[:] = [id(st) if s == id(prev_st) else s for s in lst]
            ws = wsites.get(name, [])
            ws[:] = [w for w in ws if w is not prev_st]
        return True

    def try_coalesce(prev_st, st):
        """a, x = f(); y = x  ->  a, y = f()  (x's value read only by the copy).
        Multiple results can't be inlined, and x's register is often reused
        later, so copy propagation leaves the copy."""
        if not (isinstance(prev_st, CG.AssignS) and isinstance(st, CG.AssignS)) \
                or getattr(prev_st, "is_local", False) or getattr(st, "is_local", False):
            return False
        if len(prev_st.targets) < 2 or len(st.targets) != 1 or len(st.values.items) != 1:
            return False
        y, x = st.targets[0], st.values.items[0]
        if not (isinstance(y, CG.LocalName) and isinstance(x, CG.LocalName)) or x.name == y.name:
            return False
        tnames = [t.name for t in prev_st.targets if isinstance(t, CG.LocalName)]
        if len(tnames) != len(prev_st.targets) or tnames.count(x.name) != 1 or y.name in tnames:
            return False
        if in_text(x.name):
            return False        # a closure reads x
        if any(isinstance(e, CG.LocalName) and e.name in (x.name, y.name)
               for v in prev_st.values.items for e in CG.walk(v)):
            return False
        if not dead_after(x.name, prev_st, st, 0):
            return False
        prev_st.targets[tnames.index(x.name)] = y
        nreads[x.name] = nreads.get(x.name, 0) - 1
        writes[x.name] = writes.get(x.name, 0) - 1
        if where is not None:
            _pos, rsites, wsites = where
            lst = rsites.get(x.name, [])
            lst[:] = [s for s in lst if s != id(st)]
            ws = wsites.get(x.name, [])
            ws[:] = [w for w in ws if w is not prev_st]
            ws = wsites.get(y.name, [])
            ws[:] = [prev_st if w is st else w for w in ws]
        return True

    def run(stmts):
        out = []
        for st in stmts:
            for b in _sub_blocks(st):
                b[:] = run(b)
            if out and try_coalesce(out[-1], st):
                continue
            # (blank-line markers between x = V and its use are no statement)
            blanks = []
            if not isinstance(st, CG.CommentS):
                while out and isinstance(out[-1], CG.CommentS) and not out[-1].text:
                    blanks.append(out.pop())
            folded = False
            while out and isinstance(out[-1], CG.AssignS) and not getattr(out[-1], "is_local", False) \
                    and try_fold(out[-1], st):
                out.pop()
                folded = True
            if not folded:
                out += reversed(blanks)
            # (a call in V could reach x through a closure: then x must exist first)
            if out and not (isinstance(st, CG.AssignS) and len(st.targets) == 1
                            and isinstance(st.targets[0], CG.Index)
                            and isinstance(st.targets[0].obj, CG.LocalName)
                            and in_text(st.targets[0].obj.name)
                            and any(CG.has_side_effects(x) for x in st.values.items)) \
                    and _fold_table_store(out[-1], st):
                # bookkeeping: st's reads now happen in out[-1]; its read of x is gone
                tname = st.targets[0].obj.name
                nreads[tname] = nreads.get(tname, 0) - 1
                if where is not None:
                    rs = where[1]
                    lst = rs.get(tname, [])
                    if id(st) in lst:
                        lst.remove(id(st))
                    for lst in rs.values():
                        lst[:] = [id(out[-1]) if s == id(st) else s for s in lst]
                continue
            out.append(st)
        return ST.SBlock(out) if isinstance(stmts, ST.SBlock) else out

    return run(body)


def loop_vars(stmts):
    """for k, v in f() where v is never read -> for k in f(); an unused first
    variable before a used one becomes `_`."""
    import re
    for st in stmts:
        for b in _sub_blocks(st):
            loop_vars(b)
        if isinstance(st, ST.SLoop) and st.kind == "forin" and st.forinfo and len(st.forinfo[0]) > 1:
            vs, it = st.forinfo
            rd, _, text = name_counts(st.body)
            alltext = "\n".join(text)

            def used(v):
                return rd.get(v.name, 0) > 0 or re.search(r"(?<![\w.])%s(?!\w)" % re.escape(v.name), alltext)

            vs = list(vs)
            while len(vs) > 1 and isinstance(vs[-1], CG.LocalName) and not used(vs[-1]):
                vs.pop()
            if len(vs) > 1 and isinstance(vs[0], CG.LocalName) and not used(vs[0]):
                vs[0] = CG.LocalName("_")
            st.forinfo = (vs, it)
    return stmts


def _truth(e):
    """Simplify an expression used only for its truthiness."""
    if isinstance(e, Bin) and e.op in ("And", "Or"):
        a, b = _truth(e.a), _truth(e.b)
        if e.op == "And" and isinstance(b, CG.Const) and b.v is True:
            return a                        # x and true
        if e.op == "Or" and isinstance(b, CG.Const) and b.v is False:
            return a                        # x or false
        return Bin(e.op, a, b)
    if isinstance(e, Un) and e.op == "Not" and isinstance(e.a, Un) and e.a.op == "Not":
        return _truth(e.a.a)                # not not x
    return e


def conditions(stmts):
    for st in stmts:
        if isinstance(st, ST.SIf):
            st.cond = _truth(st.cond)
        elif isinstance(st, ST.SLoop) and st.cond is not None and st.kind in ("whilecond", "repeat"):
            st.cond = _truth(st.cond)
        for b in _sub_blocks(st):
            conditions(b)
    return stmts


def _has_continue(stmts):
    """A `continue` of the enclosing loop (not of loops nested in stmts)."""
    for st in stmts:
        if isinstance(st, ST.SContinue):
            return True
        if isinstance(st, ST.SIf) and (_has_continue(st.then) or _has_continue(st.els)):
            return True
    return False


def _only_break(block):
    real = [x for x in block if not (isinstance(x, CG.CommentS) and not x.text)]
    return len(real) == 1 and isinstance(real[0], ST.SBreak)


def while_cond(stmts):
    """while true do if C then break end ... end  ->  while not C do ... end
    (also `if C then <body> else break end`,
     `if C then <body> continue end break`  ->  while C do <body> end,
     `<body> if C then break end`  ->  repeat <body> until C)."""
    for st in stmts:
        if isinstance(st, ST.SIf):
            while_cond(st.then)
            while_cond(st.els)
        elif isinstance(st, ST.SLoop):
            while_cond(st.body)
            if st.kind != "while" or not st.body:
                continue
            # (empty comments are blank-line markers)
            body = [x for x in st.body if not (isinstance(x, CG.CommentS) and not x.text)]
            if not body:
                continue
            first = body[0]
            if isinstance(first, ST.SIf):
                # (empty comments are blank-line markers)
                first.then[:] = [x for x in first.then if not (isinstance(x, CG.CommentS) and not x.text)]                     if _only_break(first.then) else first.then
                first.els[:] = [x for x in first.els if not (isinstance(x, CG.CommentS) and not x.text)]                     if _only_break(first.els) else first.els
            if isinstance(first, ST.SIf) and len(first.then) == 1 and isinstance(first.then[0], ST.SBreak):
                st.kind, st.cond = "whilecond", ST.negate(first.cond)
                st.body = ST.SBlock(list(first.els) + list(body[1:]))
            elif isinstance(first, ST.SIf) and len(first.els) == 1 and isinstance(first.els[0], ST.SBreak):
                st.kind, st.cond = "whilecond", first.cond
                st.body = ST.SBlock(list(first.then) + list(body[1:]))
            elif len(body) == 2 and isinstance(first, ST.SIf) and isinstance(body[1], ST.SBreak)                     and not first.els and first.then and isinstance(first.then[-1], ST.SContinue):
                st.kind, st.cond = "whilecond", first.cond
                st.body = ST.SBlock(list(first.then[:-1]))
            elif len(body) >= 2 and isinstance(body[-1], ST.SIf) and not body[-1].els                     and len(body[-1].then) == 1 and isinstance(body[-1].then[0], ST.SBreak)                     and not _has_continue(body[:-1]):
                st.kind, st.cond = "repeat", body[-1].cond
                st.body = ST.SBlock(list(body[:-1]))
    return stmts


def strip_trailing_continue(stmts):
    """A `continue` that is the last thing an iteration does says nothing."""
    def tail(block):
        if block and isinstance(block[-1], ST.SContinue):
            block.pop()
        elif block and isinstance(block[-1], ST.SIf):
            tail(block[-1].then)
            tail(block[-1].els)
    for st in stmts:
        if isinstance(st, ST.SLoop):
            tail(st.body)
        for b in _sub_blocks(st):
            strip_trailing_continue(b)
    return stmts


def strip_trailing_return(body):
    """A bare `return` as the last statement of a function says nothing."""
    if body and isinstance(body[-1], ST.SReturn) and (
            body[-1].values is None or (not body[-1].values.items and body[-1].values.tail is None)):
        body.pop()
    return body


def _map_stmt_exprs(st, fn):
    """replace sub-expressions of a statement's own expressions (fn as in
    CG.map_expr); nested blocks are not visited"""
    if isinstance(st, CG.AssignS):
        st.targets = [t if isinstance(t, CG.LocalName) else CG.map_expr(t, fn) for t in st.targets]
        st.values = CG.map_multi(st.values, fn)
    elif isinstance(st, CG.CallS):
        st.call = CG.map_expr(st.call, fn)
    elif isinstance(st, CG.TempDef):
        st.call = CG.map_expr(st.call, fn)
    elif isinstance(st, CG.SetListS):
        st.tbl = CG.map_expr(st.tbl, fn)
        st.values = CG.map_multi(st.values, fn)
    elif isinstance(st, CG.ForPrepS):
        st.exprs[:] = [CG.map_expr(x, fn) for x in st.exprs]
    elif isinstance(st, ST.SIf):
        st.cond = CG.map_expr(st.cond, fn)
    elif isinstance(st, ST.SLoop):
        if st.cond is not None:
            st.cond = CG.map_expr(st.cond, fn)
        if st.forinfo:
            lst = st.forinfo[1]
            lst[:] = [CG.map_expr(x, fn) if x is not None else None for x in lst]
    elif isinstance(st, ST.SReturn) and st.values is not None:
        st.values = CG.map_multi(st.values, fn)


def _map_body(stmts, fn):
    for st in stmts:
        _map_stmt_exprs(st, fn)
        for b in _sub_blocks(st):
            _map_body(b, fn)


def inline_const_locals(body, params=()):
    """A local written once, with a number, boolean or short string literal,
    and read only after that write in the same block: its reads become the
    literal. Luau's
    compiler folds such locals itself, so in Luau bytecode a register that
    holds a literal is the compiler's or the obfuscator's (a constant hoisted
    out of a loop: `local n = 1 ... t[i][n]`), never the author's name.
    Opt-in (IR module flag INLINE_CONST_LOCALS)."""
    reads, writes, text = name_counts(body)
    nested = "\n".join(text)
    import re

    def candidates(stmts):
        out = []
        for i, st in enumerate(stmts):
            if isinstance(st, CG.AssignS) and len(st.targets) == 1 and isinstance(st.targets[0], CG.LocalName) \
                    and len(st.values.items) == 1 and st.values.tail is None \
                    and isinstance(st.values.items[0], Const):
                v = st.values.items[0].v
                nm = st.targets[0].name
                ok = isinstance(v, bool) or (isinstance(v, (int, float)) and v == v and abs(v) != float("inf")) \
                    or (isinstance(v, bytes) and (len(v) <= 40 or reads.get(nm, 0) <= 1))
                if ok and writes.get(nm) == 1 and nm not in params \
                        and not re.search(r"\b%s\b" % re.escape(nm), nested):
                    after, _, _ = name_counts(stmts[i + 1:])
                    if after.get(nm, 0) == reads.get(nm, 0):
                        out.append((stmts, i, nm, v))
            for b in _sub_blocks(st):
                out += candidates(b)
        return out

    for _ in range(8):
        cands = candidates(body)
        if not cands:
            break
        for stmts, i, nm, v in reversed(cands):
            def fn(x, nm=nm, v=v):
                return Const(v) if isinstance(x, CG.LocalName) and x.name == nm else None
            _map_body(stmts[i + 1:], fn)
            del stmts[i]
        # (a copy of an inlined local is a literal now: `b = a` -> `b = 1`)
        reads, writes, text = name_counts(body)
        nested = "\n".join(text)
    return body


def _blank(block):
    return all(isinstance(x, CG.CommentS) and not x.text for x in block)


def drop_blank_branches(stmts):
    """An if branch holding only blank-line markers (empty comments: code
    that was dropped, e.g. an obfuscator's junk) is empty: no `else end`;
    an empty then-branch with a real else becomes `if not c then`."""
    for st in stmts:
        if isinstance(st, ST.SIf):
            drop_blank_branches(st.then)
            drop_blank_branches(st.els)
            for b in (st.then, st.els):
                while b and isinstance(b[-1], CG.CommentS) and not b[-1].text and not _blank(b):
                    b.pop()
                if not _blank(b) and sum(1 for x in b if not isinstance(x, CG.CommentS)) <= 2:
                    b[:] = [x for x in b if not (isinstance(x, CG.CommentS) and not x.text)]
            if st.els and _blank(st.els):
                st.els[:] = []
            if st.then and _blank(st.then) and st.els:
                st.cond = ST.negate(st.cond)
                st.then[:], st.els[:] = list(st.els), []
        elif isinstance(st, ST.SLoop):
            drop_blank_branches(st.body)
    return stmts

