"""
Source instrumentation for the ironbrew1 capture (capture.luau) and the
spin watchdog.

  * every function expression outside the VM interpreters becomes
    `__IBF(function ... end, "LOC")` (`local function f` statements get
    `__IBF(f, "LOC")` after them): closure -> AST location, so the dump can
    name the VM's Lua helpers (closure maker, vararg packer, ...);
  * each closure maker (the function that returns the interpreter, see
    find_vms) calls `__IBC("MK", {params}, {["LOC"] = local, ...})` right
    before `return function(...)`: every local visible there, keyed by its
    declaration location (luasym's scope keys).

Only calls are added, no locals (CLAUDE.md, Environment fidelity).
"""


def loc_start(loc):
    a = loc.split(" - ")[0].split(",")
    return int(a[0]), int(a[1])


def loc_end(loc):
    b = loc.split(" - ")[1].split(",")
    return int(b[0]), int(b[1])


def iter_nodes(n):
    st = [n]
    while st:
        x = st.pop()
        if isinstance(x, list):
            st += reversed(x)
        elif isinstance(x, dict):
            yield x
            for k, v in reversed(list(x.items())):
                if k not in ("local", "location") and isinstance(v, (dict, list)):
                    st.append(v)


def dispatch_loop(fn):
    """the interpreter's `while true do x = code[pc] ...` loop, or None"""
    for s in fn["body"]["body"]:
        if s["type"] != "AstStatWhile":
            continue
        c = s["condition"]
        if not (c["type"] == "AstExprConstantBool" and c["value"]):
            continue
        body = s["body"]["body"]
        if body and body[0]["type"] == "AstStatAssign" and body[0]["values"][0]["type"] == "AstExprIndexExpr":
            return s
    return None


def find_vms(root):
    """[(maker function node, interpreter function node)]"""
    out = []
    for x in iter_nodes(root):
        if x.get("type") != "AstExprFunction":
            continue
        body = x["body"]["body"]
        if not body or body[-1]["type"] != "AstStatReturn" or not body[-1]["list"]:
            continue
        inner = body[-1]["list"][0]
        if inner["type"] == "AstExprFunction" and inner.get("vararg") and dispatch_loop(inner) is not None:
            out.append((x, inner))
    return out


# ---------------------------------------------------------------------------
# visible locals at a statement

class _Found(Exception):
    def __init__(self, names):
        self.names = names


def _exprs_of(node):
    """function expressions directly inside a statement (not in nested blocks)"""
    st = [node]
    while st:
        x = st.pop()
        if isinstance(x, list):
            st += x
        elif isinstance(x, dict):
            t = x.get("type", "")
            if t == "AstExprFunction":
                yield x
                continue
            if t.startswith("AstStat") and x is not node:
                continue
            for k, v in x.items():
                if k not in ("local", "location", "body", "thenbody", "elsebody") and isinstance(v, (dict, list)):
                    st.append(v)


def _function(fn, scope, target):
    sc = dict(scope)
    if fn.get("self"):
        sc["self"] = fn["self"]["location"]
    for a in fn["args"]:
        sc[a["name"]] = a["location"]
    _block(fn["body"]["body"], sc, target)


def _block(stmts, scope, target):
    sc = dict(scope)
    for s in stmts:
        if s is target:
            raise _Found(sc)
        t = s["type"]
        if t == "AstStatLocalFunction":
            sc[s["name"]["name"]] = s["name"]["location"]
            _function(s["func"], sc, target)
            continue
        if t == "AstStatFunction":
            _function(s["func"], sc, target)
            continue
        for f in _exprs_of(s):
            _function(f, sc, target)
        if t == "AstStatLocal":
            for v in s["vars"]:
                sc[v["name"]] = v["location"]
        elif t == "AstStatBlock":
            _block(s["body"], sc, target)
        elif t == "AstStatIf":
            _block(s["thenbody"]["body"], sc, target)
            e = s.get("elsebody")
            if e is not None:
                _block([e] if e["type"] == "AstStatIf" else e["body"], sc, target)
        elif t in ("AstStatWhile", "AstStatRepeat"):
            _block(s["body"]["body"], sc, target)
        elif t == "AstStatFor":
            inner = dict(sc)
            inner[s["var"]["name"]] = s["var"]["location"]
            _block(s["body"]["body"], inner, target)
        elif t == "AstStatForIn":
            inner = dict(sc)
            for v in s["vars"]:
                inner[v["name"]] = v["location"]
            _block(s["body"]["body"], inner, target)


def visible_at(root, target):
    """{name: declaration location} of the locals visible at statement `target`"""
    try:
        _block(root["body"], {}, target)
    except _Found as f:
        return f.names
    return None


# ---------------------------------------------------------------------------
# text edits by AST location (luau-ast columns are byte offsets)

SPIN = "__SPIN.n=__SPIN.n+1;if __SPIN.n>=__SPIN.step then __SPIN.f()end;"


def insert_at(src, edits):
    """src (latin-1 str) with (line, col, text) insertions applied; texts at
    one position keep their list order"""
    lines = src.split("\n")
    order = sorted(range(len(edits)), key=lambda i: (edits[i][0], edits[i][1], -i), reverse=True)
    for i in order:
        line, col, text = edits[i]
        s = lines[line]
        lines[line] = s[:col] + text + s[col:]
    return "\n".join(lines)


def spin_edits(root):
    """Spin watchdog (envlog's --cfg spin): each interpreter's dispatch loop
    body starts by counting a step (table operations plus a rare call, no
    locals). Only the dispatch loops: the VM's startup (decoding, probes) runs
    well over the watchdog's step limit without touching the environment."""
    edits = []
    for _, interp in find_vms(root):
        loop = dispatch_loop(interp)
        edits.append(loc_start(loop["body"]["location"]) + (" " + SPIN + " ",))
    return edits


def patch_spin(src, root=None):
    if root is None:
        import luauast
        root = luauast.parse(src)
    return insert_at(src, spin_edits(root))


def capture_edits(root):
    """(edits, makers): function registration and maker capture calls"""
    vms = find_vms(root)
    interps = {id(f) for _, f in vms}
    edits = []
    # function registration, outside the interpreters
    st = [root]
    while st:
        x = st.pop()
        if isinstance(x, list):
            st += x
            continue
        if not isinstance(x, dict):
            continue
        t = x.get("type")
        if t == "AstExprFunction" and id(x) in interps:
            continue
        if t in ("AstStatLocalFunction", "AstStatFunction"):
            fn = x["func"]
            if t == "AstStatLocalFunction":
                edits.append(loc_end(x["location"]) + (' __IBF(%s,"%s") ' % (x["name"]["name"], fn["location"]),))
            st.append(fn["body"])
            continue
        if t == "AstExprFunction":
            edits.append(loc_start(x["location"]) + ("__IBF(",))
            edits.append(loc_end(x["location"]) + (',"%s")' % x["location"],))
        for k, v in x.items():
            if k not in ("local", "location") and isinstance(v, (dict, list)):
                st.append(v)
    makers = []
    for mk, interp in vms:
        ret = mk["body"]["body"][-1]
        names = visible_at(root, ret)
        if names is None:
            continue
        params = [a["name"] for a in mk["args"]]
        fields = ",".join('["%s"]=%s' % (loc, nm) for nm, loc in sorted(names.items(), key=lambda kv: kv[1]))
        text = '__IBC("%s",{%s},{%s}) ' % (mk["location"], ",".join(params), fields)
        edits.append(loc_start(ret["location"]) + (text,))
        makers.append({"maker": mk["location"], "interp": interp["location"]})
    return edits, makers


def instrument(src, spin=True):
    """(patched source, makers) for the capture run"""
    import luauast
    root = luauast.parse(src)
    edits, makers = capture_edits(root)
    if spin:
        edits += spin_edits(root)
    return insert_at(src, edits), makers
