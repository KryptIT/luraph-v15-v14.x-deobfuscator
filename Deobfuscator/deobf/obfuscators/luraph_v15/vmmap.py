"""
Static helper: maps every Luraph interpreter dispatch loop to its opcode
handlers (opcode -> handler source) using luau-ast's JSON output.

Usage: python obfuscators/luraph_v15/vmmap.py <protected.luau> [dispatch_index] [opcode...]
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))     # deobf/ (bin/luau-ast)


def load_ast(path):
    exe = os.path.join(ROOT, "bin", "luau-ast.exe" if os.name == "nt" else "luau-ast")
    r = subprocess.run([exe, path], capture_output=True)
    errs = r.stderr.decode("latin-1").strip().splitlines()
    if r.returncode != 0 or (errs and errs[0].startswith("Parse errors")):
        raise SyntaxError("not valid Luau (%s)" % (errs[1].strip() if len(errs) > 1 else "luau-ast exit %#x"
                                                   % (r.returncode & 0xFFFFFFFF)))
    out = r.stdout
    return json.loads(out.decode("latin-1"))["root"]


def loc(node):
    a, b = node["location"].split(" - ")
    l1, c1 = map(int, a.split(","))
    l2, c2 = map(int, b.split(","))
    return l1, c1, l2, c2


def text_of(lines, node):
    l1, c1, l2, c2 = loc(node)
    if l1 == l2:
        return lines[l1][c1:c2]
    parts = [lines[l1][c1:]] + lines[l1 + 1:l2] + [lines[l2][:c2]]
    return "\n".join(parts)


def walk(node, fn):
    if isinstance(node, dict):
        fn(node)
        for v in node.values():
            walk(v, fn)
    elif isinstance(node, list):
        for v in node:
            walk(v, fn)


def local_name(expr):
    if expr.get("type") == "AstExprLocal":
        return expr["local"]["name"]
    return None


def find_dispatchers(root):
    """while true do local op = ARR[PC]; if-tree ... end"""
    found = []

    def visit(n):
        if n.get("type") != "AstStatWhile":
            return
        cond = n["condition"]
        if cond.get("type") != "AstExprConstantBool" or not cond.get("value"):
            return
        body = n["body"]["body"]
        # `local op = ARR[PC]` or `op = ARR[PC]` (op declared by the VM function);
        # extra targets may follow and are set to nil (`local op,x=ARR[PC]`,
        # `op,x=ARR[PC]`)
        if len(body) < 2 or body[0]["type"] not in ("AstStatLocal", "AstStatAssign"):
            return
        st = body[0]
        if len(st["values"]) != 1:
            return
        if st["type"] == "AstStatLocal":
            opname = st["vars"][0]["name"]
        else:
            opname = local_name(st["vars"][0])
            if not opname:
                return
        v = st["values"][0]
        if v["type"] != "AstExprIndexExpr":
            return
        arr, pc = local_name(v["expr"]), local_name(v["index"])
        if not arr or not pc or body[1]["type"] != "AstStatIf":
            return
        found.append({"node": n, "op": opname, "arr": arr, "pc": pc, "tree": body[1],
                      "rest": body[2:]})

    walk(root, visit)
    return found


OPS = {"CompareLt": lambda a, b: a < b, "CompareLe": lambda a, b: a <= b,
       "CompareGt": lambda a, b: a > b, "CompareGe": lambda a, b: a >= b,
       "CompareEq": lambda a, b: a == b, "CompareNe": lambda a, b: a != b}
FLIP = {"CompareLt": "CompareGt", "CompareLe": "CompareGe", "CompareGt": "CompareLt",
        "CompareGe": "CompareLe", "CompareEq": "CompareEq", "CompareNe": "CompareNe"}


def eval_cond(cond, var, value):
    """Evaluate `var <op> const` for a concrete opcode value; None if not such a test."""
    if cond["type"] != "AstExprBinary" or cond["op"] not in OPS:
        return None
    l, r = cond["left"], cond["right"]
    op = cond["op"]
    if local_name(l) == var and r["type"] == "AstExprConstantNumber":
        return OPS[op](value, r["value"])
    if local_name(r) == var and l["type"] == "AstExprConstantNumber":
        return OPS[FLIP[op]](value, l["value"])
    return None


def resolve(tree, var, value):
    """Follow the if-tree for one opcode value and return the handler block."""
    node = tree
    while True:
        if node["type"] == "AstStatBlock":
            if len(node["body"]) >= 1 and node["body"][0]["type"] == "AstStatIf" \
                    and eval_cond(node["body"][0]["condition"], var, value) is not None:
                node = node["body"][0]
                continue
            return node
        if node["type"] == "AstStatIf":
            r = eval_cond(node["condition"], var, value)
            if r is None:
                return node
            if r:
                node = node["thenbody"]
            else:
                e = node.get("elsebody")
                if e is None:
                    return None
                node = e
            continue
        return node


def handler_map(disp, lines, max_op=256):
    handlers = {}
    for op in range(max_op):
        blk = resolve(disp["tree"], disp["op"], op)
        if blk is None:
            continue
        key = blk["location"]
        handlers.setdefault(key, {"ops": [], "node": blk})["ops"].append(op)
    return handlers


def main():
    path = sys.argv[1]
    root = load_ast(path)
    with open(path, encoding="latin-1") as f:
        lines = f.read().split("\n")
    disps = find_dispatchers(root)
    if len(sys.argv) == 2:
        for i, d in enumerate(disps, 1):
            h = handler_map(d, lines)
            print("dispatch %d: op=%s arr=%s pc=%s handlers=%d at %s" % (i, d["op"], d["arr"], d["pc"], len(h),
                                                                        d["node"]["location"]))
        return
    d = disps[int(sys.argv[2]) - 1]
    want = set(int(x) for x in sys.argv[3:])
    for op in sorted(want):
        blk = resolve(d["tree"], d["op"], op)
        print("---- op %d" % op)
        print(text_of(lines, blk) if blk else "<none>")


if __name__ == "__main__":
    main()


def instrument(src, disp_index, probes, root=None, tmp_path=None):
    """Insert Lua code at the start of chosen opcode handlers of one dispatch loop.

    probes: {opcode: "lua code"}; returns modified source. Only single-line
    sources (like Luraph output) are supported.
    """
    lines = src.split("\n")
    if root is None:
        root = load_ast(tmp_path)
    d = find_dispatchers(root)[disp_index - 1]
    inserts = []
    for op, code in probes.items():
        blk = resolve(d["tree"], d["op"], op)
        if blk is None:
            continue
        l1, c1, _, _ = loc(blk)
        # block location starts right at the handler's first statement
        inserts.append((l1, c1, code))
    for l1, c1, code in sorted(inserts, reverse=True):
        s = lines[l1]
        lines[l1] = s[:c1] + " " + code + " " + s[c1:]
    return "\n".join(lines)


def instrument_post(src, disp_index, root, make_code, reg="Z", pc="W"):
    """Append logging after simple `REG[..]=...` handlers. make_code(op, dest_expr) -> lua."""
    import re as _re
    lines = src.split("\n")
    d = find_dispatchers(root)[disp_index - 1]
    h = handler_map(d, lines)
    inserts = []
    for key, v in h.items():
        blk = v["node"]
        text = text_of(lines, blk)
        if (pc + "=") in text.replace(pc + "==", "") or "return" in text or "break" in text \
                or (pc + "+=") in text or (pc + "-=") in text:
            continue
        m = _re.match(r"\s*(" + reg + r"\[[A-Za-z_]+\[" + pc + r"\]\])=", text)
        if not m:
            continue
        l1, c1, l2, c2 = loc(blk)
        inserts.append((l2, c2, make_code(v["ops"][0], m.group(1))))
    for l2, c2, code in sorted(inserts, reverse=True):
        s = lines[l2]
        lines[l2] = s[:c2] + " " + code + " " + s[c2:]
    return "\n".join(lines)


def loop_names(disp):
    """(register array, pc variable) used by a dispatch loop's handlers."""
    return ("Z", "W") if disp["pc"] == "W" else ("l", "O")


def post_inserts(src_lines, disp, make_code):
    import re as _re
    reg, pc = loop_names(disp)
    out = []
    for v in handler_map(disp, src_lines).values():
        text = text_of(src_lines, v["node"])
        if (pc + "=") in text.replace(pc + "==", "") or "return" in text or "break" in text \
                or (pc + "+=") in text or (pc + "-=") in text:
            continue
        m = _re.match(r"\s*(" + reg + r"\[[A-Za-z_]+\[" + pc + r"\]\])=", text)
        if not m:
            continue
        l1, c1, l2, c2 = loc(v["node"])
        out.append((l2, c2, make_code(v["ops"][0], m.group(1), pc)))
    return out


def instrument_everything(src, root, make_post, make_loop):
    """Post-log simple handlers in every loop and log each dispatched instruction."""
    import re as _re
    lines = src.split("\n")
    inserts = []
    for d in find_dispatchers(root):
        inserts += post_inserts(lines, d, make_post)
    for l2, c2, code in sorted(inserts, reverse=True):
        s = lines[l2]
        lines[l2] = s[:c2] + " " + code + " " + s[c2:]
    out = "\n".join(lines)
    k = [0]

    def rep(m):
        k[0] += 1
        return m.group(0) + make_loop(k[0], m.group(1), m.group(3))
    return _re.sub(r"while true do (?:local )?([A-Za-z_]+)(?:,[A-Za-z_]+)*=([A-Za-z_]+)\[([A-Za-z_]+)\];", rep, out)


def closure_entries(root):
    """For each VM interpreter closure: (line, col of its first statement, proto variable name)."""
    disp_nodes = [d["node"] for d in find_dispatchers(root)]
    seen = {}

    def walk(n, stack):
        if isinstance(n, dict):
            if n.get("type") == "AstExprFunction":
                stack = stack + [n]
            if n.get("type") == "AstStatWhile" and any(n is d for d in disp_nodes):
                inner = next(f for f in reversed(stack) if f.get("vararg") and not f["args"])
                outer = next(f for f in reversed(stack) if len(f["args"]) >= 2)
                l1, c1, _, _ = loc(inner["body"]["body"][0])
                # keyed by the proto parameter: parameter 1 is not always the
                # proto (function(g, upvals, proto, ...)), and an upvalue list
                # can be shared or false, which would merge protos
                seen[(l1, c1)] = outer["args"][_maker_params(outer)[0]]["name"]
            for v in n.values():
                walk(v, stack)
        elif isinstance(n, list):
            for v in n:
                walk(v, stack)
    walk(root, [])
    return [(l, c, name) for (l, c), name in seen.items()]


def closure_makers(root):
    """For each VM closure template: (line, col just after the statement that
    stores the new closure in a local, that local's name, proto variable name).
    Luraph builds every closure of a proto with `S, h = n, function(...) ... end`
    inside a maker function whose second parameter is the proto."""
    disp_nodes = [d["node"] for d in find_dispatchers(root)]
    seen = {}

    def walk(n, stack, stmts):
        if isinstance(n, dict):
            t = n.get("type")
            if t == "AstExprFunction":
                stack = stack + [n]
            if t and t.startswith("AstStat"):
                stmts = stmts + [(n, len(stack))]
            if t == "AstStatWhile" and any(n is d for d in disp_nodes):
                oi = max(i for i, f in enumerate(stack) if len(f["args"]) >= 2)
                if oi + 1 < len(stack):
                    clo = stack[oi + 1]
                    st = [s for s, d in stmts if d == oi + 1]
                    st = st[-1] if st else None
                    if st and st["type"] == "AstStatAssign":
                        for v, e in zip(st["vars"], st["values"]):
                            if e is clo and local_name(v):
                                _, _, l2, c2 = loc(st)
                                seen[(l2, c2)] = (local_name(v), stack[oi]["args"][1]["name"])
            for v in n.values():
                walk(v, stack, stmts)
        elif isinstance(n, list):
            for v in n:
                walk(v, stack, stmts)
    walk(root, [], [])
    return [(l, c, var, pv) for (l, c), (var, pv) in seen.items()]


def decl_key(local):
    """Identity of a local: its declaration location."""
    return local["location"]


def maker_info(root):
    """closure_makers() plus what the runtime capture needs: for each maker,
    {"at": (line, col), "var": closure local, "proto": proto param name,
     "maker": maker AstExprFunction, "vm": the VM closure AstExprFunction,
     "captures": [maker-level local names the VM closure uses]}.
    Only names that are not shadowed at the insertion point are returned."""
    disp_nodes = [d["node"] for d in find_dispatchers(root)]
    out = {}

    def walk(n, stack, stmts):
        if isinstance(n, dict):
            t = n.get("type")
            if t == "AstExprFunction":
                stack = stack + [n]
            if t and t.startswith("AstStat"):
                stmts = stmts + [(n, len(stack))]
            if t == "AstStatWhile" and any(n is d for d in disp_nodes):
                oi = max(i for i, f in enumerate(stack) if len(f["args"]) >= 2)
                if oi + 1 < len(stack):
                    clo = stack[oi + 1]
                    st = [s for s, d in stmts if d == oi + 1]
                    st = st[-1] if st else None
                    if st and st["type"] == "AstStatAssign":
                        for v, e in zip(st["vars"], st["values"]):
                            if e is clo and local_name(v):
                                _, _, l2, c2 = loc(st)
                                if (l2, c2) not in out:
                                    pi, ui = _maker_params(stack[oi])
                                    out[(l2, c2)] = {"at": (l2, c2), "var": local_name(v),
                                                     "proto": stack[oi]["args"][pi]["name"],
                                                     "proto_index": pi, "upvals_index": ui,
                                                     # key the entry hooks number protos by (__PID);
                                                     # closure -> proto attribution must use the same
                                                     "pf_key": stack[oi]["args"][pi]["name"],
                                                     "maker": stack[oi], "vm": clo, "stmt": st}
            for v in n.values():
                walk(v, stack, stmts)
        elif isinstance(n, list):
            for v in n:
                walk(v, stack, stmts)
    walk(root, [], [])
    for info in out.values():
        info["captures"] = _captures(info)
    return list(out.values())


def _maker_params(maker):
    """(proto parameter index, upvalue-list parameter index) of a closure maker.
    Layouts differ: function(e, proto, upvals) or, with repeated names,
    function(g, d, d, d, d, j) where the proto is the last one. The proto is
    the parameter indexed through itself (P[P[k]]: its fields are keyed by
    its own entries); the upvalue list is the first other parameter the body
    uses (only the last of repeated names is visible)."""
    args = maker["args"]
    visible = {}
    for i, a in enumerate(args):
        visible[a["name"]] = i
    counts = {}
    kcounts = {}    # P[<number>]: the proto of makers that index it directly
    used = set()

    def visit(n):
        if isinstance(n, dict):
            if n.get("type") == "AstExprLocal":
                used.add(n["local"]["location"])
            if n.get("type") == "AstExprIndexExpr" and n["expr"].get("type") == "AstExprLocal" \
                    and n["index"].get("type") == "AstExprIndexExpr" \
                    and n["index"]["expr"].get("type") == "AstExprLocal" \
                    and n["index"]["expr"]["local"]["location"] == n["expr"]["local"]["location"]:
                k = n["expr"]["local"]["location"]
                counts[k] = counts.get(k, 0) + 1
            if n.get("type") == "AstExprIndexExpr" and n["expr"].get("type") == "AstExprLocal" \
                    and n["index"].get("type") == "AstExprConstantNumber":
                k = n["expr"]["local"]["location"]
                kcounts[k] = kcounts.get(k, 0) + 1
            for v in n.values():
                visit(v)
        elif isinstance(n, list):
            for v in n:
                visit(v)
    visit(maker["body"])
    cands = [i for i in visible.values() if i > 0]
    pi = max(cands, key=lambda i: (counts.get(args[i]["location"], 0), i == 1)) if cands else 1
    if not counts.get(args[pi]["location"]):
        pi = 1
        # function(v, R, R, R, g, g) with `B = R[11]`: the visible R
        kc = [i for i in cands if kcounts.get(args[i]["location"])]
        if kc:
            pi = max(kc, key=lambda i: kcounts[args[i]["location"]])
    others = sorted(i for i in visible.values() if i not in (0, pi) and args[i]["location"] in used)
    ui = others[0] if others else pi + 1
    return pi, ui


def _decls_in(fn):
    """Declaration keys of locals declared directly in fn (params and body,
    not inside nested functions)."""
    keys = {}

    def visit(n):
        if isinstance(n, dict):
            t = n.get("type")
            if t == "AstExprFunction" and n is not fn:
                return
            if t == "AstStatLocal":
                for v in n["vars"]:
                    keys[decl_key(v)] = v["name"]
            elif t == "AstStatLocalFunction":
                keys[decl_key(n["name"])] = n["name"]["name"]
            elif t in ("AstStatFor",):
                keys[decl_key(n["var"])] = n["var"]["name"]
            elif t == "AstStatForIn":
                for v in n["vars"]:
                    keys[decl_key(v)] = v["name"]
            for v in n.values():
                visit(v)
        elif isinstance(n, list):
            for v in n:
                visit(v)
    for a in fn["args"]:
        keys[decl_key(a)] = a["name"]
    visit(fn["body"])
    return keys


def _captures(info):
    maker_decls = _decls_in(info["maker"])
    used = {}

    def visit(n):
        if isinstance(n, dict):
            if n.get("type") == "AstExprLocal":
                k = decl_key(n["local"])
                if k in maker_decls:
                    used[k] = maker_decls[k]
            for v in n.values():
                visit(v)
        elif isinstance(n, list):
            for v in n:
                visit(v)
    visit(info["vm"])
    names = {}
    for k, name in used.items():
        names.setdefault(name, []).append(k)
    # a name declared twice at maker level would be ambiguous at the insertion point
    dup = {nm for nm, ks in names.items() if len(ks) > 1}
    by_name = {}
    for k, nm in maker_decls.items():
        by_name.setdefault(nm, []).append(k)
    return sorted(nm for nm in names if nm not in dup and len(by_name[nm]) == 1)
