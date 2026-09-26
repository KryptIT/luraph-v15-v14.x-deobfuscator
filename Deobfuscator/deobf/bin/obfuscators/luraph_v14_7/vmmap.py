"""
Static helper: maps every Luraph interpreter dispatch loop to its opcode
handlers (opcode -> handler source) using luau-ast's JSON output.

Usage: python obfuscators/luraph_v14_7/vmmap.py <protected.luau> [dispatch_index] [opcode...]
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


def unwrap(expr):
    """Strip parser-only wrappers that v14.x emits around ordinary expressions.

    v14.7 in particular commonly writes `local op=(ops[pc]);`; luau-ast
    represents the parentheses as AstExprGroup, while v15 usually emits the
    index expression directly.  Type assertions are harmless wrappers too.
    """
    while isinstance(expr, dict) and expr.get("type") in ("AstExprGroup", "AstExprTypeAssertion"):
        expr = expr.get("expr") or expr.get("expression")
    return expr


def local_name(expr):
    expr = unwrap(expr)
    if isinstance(expr, dict) and expr.get("type") == "AstExprLocal":
        return expr["local"]["name"]
    return None


def find_dispatchers(root):
    """while true do local op = ARR[PC]; if-tree ... end"""
    found = []

    def visit(n):
        typ = n.get("type")
        if typ == "AstStatWhile":
            cond = unwrap(n.get("condition"))
            if not isinstance(cond, dict) or cond.get("type") != "AstExprConstantBool" or not cond.get("value"):
                return
            body = n["body"]["body"]
        elif typ == "AstStatRepeat":
            # v14.8 commonly emits the real VM dispatcher as:
            #   repeat local op=(OPS[pc]); if ... end; ... until false
            cond = unwrap(n.get("condition"))
            if not isinstance(cond, dict) or cond.get("type") != "AstExprConstantBool" or cond.get("value"):
                return
            body = n["body"]["body"]
        else:
            return
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
        v = unwrap(st["values"][0])
        if not isinstance(v, dict) or v.get("type") != "AstExprIndexExpr":
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
    l, r = unwrap(cond["left"]), unwrap(cond["right"])
    op = cond["op"]
    if local_name(l) == var and isinstance(r, dict) and r.get("type") == "AstExprConstantNumber":
        return OPS[op](value, r["value"])
    if local_name(r) == var and isinstance(l, dict) and l.get("type") == "AstExprConstantNumber":
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


def instrument_post(src, disp_index, root, make_code, reg=None, pc=None):
    """Append logging after simple `REG[..]=...` handlers. make_code(op, dest_expr) -> lua."""
    import re as _re
    lines = src.split("\n")
    d = find_dispatchers(root)[disp_index - 1]
    if reg is None:
        reg = d["arr"]
    if pc is None:
        pc = d["pc"]
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
    """(opcode/register array, pc variable) used by this dispatch loop.

    v14.7/14.8/14.9 randomize these names, so never infer them from a
    version-specific hardcoded pair.
    """
    return disp["arr"], disp["pc"]


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
    return _re.sub(r"while true do (?:local )?([A-Za-z_]+)(?:,[A-Za-z_]+)*=\s*\(?([A-Za-z_]+)\[([A-Za-z_]+)\]\)?;", rep, out)


def _binding_for_closure(clo, stmts, depth=None):
    """Find the statement that binds *clo* to a local/variable.

    v14.x uses several spellings (`x=function`, `x=(function)`, and local
    assignments).  `depth` is the lexical function depth of the statement;
    when omitted every visible statement is considered.
    """
    for st, d in reversed(stmts):
        if depth is not None and d != depth:
            continue
        typ = st.get("type")
        if typ in ("AstStatAssign", "AstStatLocal"):
            for v, e in zip(st.get("vars", []), st.get("values", [])):
                if unwrap(e) is not clo:
                    continue
                name = local_name(v) if typ == "AstStatAssign" else v.get("name")
                if name:
                    return st, name
        elif typ == "AstStatLocalFunction":
            # luau-ast revisions differ on whether the function lives in
            # `func`, `value`, or `function`.
            f = unwrap(st.get("func") or st.get("value") or st.get("function"))
            if f is clo:
                name = (st.get("name") or {}).get("name")
                if name:
                    return st, name
    return None, None


def _select_vm_factory(stack, stmts, disp):
    """Select (maker-index, maker, vm, binding-stmt, variable).

    Across the supplied 14.7/14.8/14.9 layouts the stable property is not an
    exact nesting depth: the *program-counter local* belongs to the actual VM
    closure, while the opcode array may be captured from the parent factory.
    Use that to identify the VM closure, then recover its lexical parent/binding.
    """
    pc = disp.get("pc")

    # Strong path: choose the innermost ancestor function that directly
    # declares the dispatcher PC (parameter or local), then require that this
    # closure is actually bound in its lexical parent.
    for vi in range(len(stack) - 1, 0, -1):
        vm = stack[vi]
        try:
            decl_names = set(_decls_in(vm).values())
        except Exception:
            decl_names = set()
        if pc and pc not in decl_names:
            continue
        mi = vi - 1
        maker = stack[mi]
        st, var = _binding_for_closure(vm, stmts, vi)
        if st is not None and maker.get("args"):
            return mi, maker, vm, st, var

    # Flexible path: a wrapper/IIFE may sit between the factory and the VM.
    # Search any bound ancestor closure that contains the PC declaration and
    # then use its nearest argument-bearing lexical parent as the maker.
    for vi in range(len(stack) - 1, 0, -1):
        vm = stack[vi]
        try:
            decl_names = set(_decls_in(vm).values())
        except Exception:
            decl_names = set()
        if pc and pc not in decl_names:
            continue
        for mi in range(vi - 1, -1, -1):
            maker = stack[mi]
            if not maker.get("args"):
                continue
            # A direct binding in the candidate maker is preferred.  If an
            # intermediate wrapper exists, the binding can occur deeper than
            # maker depth, so accept any binding whose statement is still
            # outside the VM body itself.
            st, var = _binding_for_closure(vm, stmts, mi + 1)
            if st is None:
                st, var = _binding_for_closure(vm, stmts)
            if st is not None:
                return mi, maker, vm, st, var

    # Legacy fallback: preserve support for older samples where the PC local
    # cannot be resolved by the AST (shadowing/parser differences).
    for mi in range(len(stack) - 2, -1, -1):
        maker = stack[mi]
        if not maker.get("args"):
            continue
        for vi in range(mi + 1, len(stack)):
            vm = stack[vi]
            st, var = _binding_for_closure(vm, stmts, mi + 1)
            if st is not None:
                return mi, maker, vm, st, var
    return None


def closure_entries(root):
    """Return (line, col, proto-param-name) for each v14.x VM closure entry."""
    dispatches = find_dispatchers(root)
    by_node = {id(d["node"]): d for d in dispatches}
    seen = {}

    def walk(n, stack, stmts):
        if isinstance(n, dict):
            t = n.get("type")
            if t == "AstExprFunction":
                stack = stack + [n]
            if t and t.startswith("AstStat"):
                stmts = stmts + [(n, len(stack))]
            if t in ("AstStatWhile", "AstStatRepeat") and id(n) in by_node:
                picked = _select_vm_factory(stack, stmts, by_node[id(n)])
                if picked is not None:
                    _mi, maker, vm, _st, _var = picked
                    body = vm.get("body", {}).get("body", [])
                    if body:
                        l1, c1, _, _ = loc(body[0])
                        pi, _ui = _maker_params(maker)
                        args = maker.get("args", [])
                        if args and pi < len(args):
                            seen[(l1, c1)] = args[pi]["name"]
            for v in n.values():
                walk(v, stack, stmts)
        elif isinstance(n, list):
            for v in n:
                walk(v, stack, stmts)

    walk(root, [], [])
    return [(l, c, name) for (l, c), name in seen.items()]


def closure_makers(root):
    """Locate closure assignments for v14.x makers."""
    return [(i["at"][0], i["at"][1], i["var"], i["proto"]) for i in maker_info(root)]


def decl_key(local):
    """Identity of a local: its declaration location."""
    return local["location"]


def maker_info(root):
    """Return runtime-capture metadata for v14.7, v14.8 and v14.9 makers."""
    dispatches = find_dispatchers(root)
    by_node = {id(d["node"]): d for d in dispatches}
    out = {}

    def walk(n, stack, stmts):
        if isinstance(n, dict):
            t = n.get("type")
            if t == "AstExprFunction":
                stack = stack + [n]
            if t and t.startswith("AstStat"):
                stmts = stmts + [(n, len(stack))]
            if t in ("AstStatWhile", "AstStatRepeat") and id(n) in by_node:
                picked = _select_vm_factory(stack, stmts, by_node[id(n)])
                if picked is not None:
                    mi, maker, clo, st, var = picked
                    _, _, l2, c2 = loc(st)
                    key = (l2, c2)
                    if key not in out:
                        pi, ui = _maker_params(maker)
                        args = maker.get("args", [])
                        if args and pi < len(args):
                            proto_name = args[pi]["name"]
                            out[key] = {
                                "at": key,
                                "var": var,
                                "proto": proto_name,
                                "proto_index": pi,
                                "upvals_index": ui,
                                "pf_key": proto_name,
                                "maker": maker,
                                "vm": clo,
                                "stmt": st,
                                "maker_depth": mi,
                                "dispatch_pc": by_node[id(n)].get("pc"),
                                "dispatch_arr": by_node[id(n)].get("arr"),
                            }
            for v in n.values():
                walk(v, stack, stmts)
        elif isinstance(n, list):
            for v in n:
                walk(v, stack, stmts)

    walk(root, [], [])
    for info in out.values():
        info["captures"] = _captures(info)
        info["outer_env"] = _outer_captures(info)
    return list(out.values())

def _maker_params(maker):
    """Infer (prototype-parameter, upvalue-parameter) for v14.x makers.

    Unlike the v15 mapper, parameter 0 is a valid prototype candidate. v14.7
    samples often use `function(V, h)` where V is the prototype object itself.
    """
    args = maker.get("args", [])
    if not args:
        return 0, 0

    # Repeated names are legal in the obfuscated source; only the last visible
    # declaration of each name can be referenced from the body.
    visible = {}
    for i, a in enumerate(args):
        visible[a["name"]] = i

    direct = {}   # P[constant]
    nested = {}   # P[P[x]]
    used = set()

    def add(tab, key, amount=1):
        tab[key] = tab.get(key, 0) + amount

    def visit(n):
        if isinstance(n, dict):
            if n.get("type") == "AstExprLocal":
                local = n.get("local") or {}
                used.add(local.get("location"))

            if n.get("type") == "AstExprIndexExpr":
                base = unwrap(n.get("expr"))
                idx = unwrap(n.get("index"))
                if isinstance(base, dict) and base.get("type") == "AstExprLocal":
                    key = (base.get("local") or {}).get("location")
                    if isinstance(idx, dict) and idx.get("type") == "AstExprConstantNumber":
                        add(direct, key, 4)
                    if isinstance(idx, dict) and idx.get("type") == "AstExprIndexExpr":
                        ib = unwrap(idx.get("expr"))
                        if (isinstance(ib, dict) and ib.get("type") == "AstExprLocal"
                                and (ib.get("local") or {}).get("location") == key):
                            add(nested, key, 8)
            for v in n.values():
                visit(v)
        elif isinstance(n, list):
            for v in n:
                visit(v)

    visit(maker.get("body"))
    candidates = list(visible.values()) or list(range(len(args)))

    def score(i):
        key = args[i].get("location")
        return (nested.get(key, 0) + direct.get(key, 0), direct.get(key, 0), -i)

    pi = max(candidates, key=score)
    remaining = [i for i in candidates if i != pi]
    if remaining:
        ui = max(remaining, key=lambda i: (args[i].get("location") in used, direct.get(args[i].get("location"), 0), -i))
    else:
        ui = pi
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


def _outer_captures(info):
    """Lexical locals used by the VM maker but declared outside it.

    v15 makers are usually self-contained.  v14.7/v14.8 can install the VM
    factory from inside an initializer function, e.g. `q[59]=function(V,h)...`,
    and that factory closes over initializer locals such as q/g/helpers.

    The devirtualizer later re-executes the maker.  Record those free locals at
    runtime so the reconstructed LuaFunc gets the same parent Scope instead of
    failing with `Unsupported: unbound local ...`.

    Returns a list of dictionaries with:
      decl  - luau-ast declaration location (Scope key)
      name  - source-visible local name at the maker creation site
      field - safe field name used in the serialized proto capture
    """
    maker = info["maker"]
    own = set(_decls_in(maker))
    found = {}

    def visit(n):
        if isinstance(n, dict):
            # Do descend into nested functions: if the VM closure references an
            # outer initializer local, that binding is part of the maker's
            # lexical environment too.
            if n.get("type") == "AstExprLocal":
                loc = n.get("local") or {}
                key = decl_key(loc)
                if key not in own:
                    name = loc.get("name")
                    if name:
                        found.setdefault(key, name)
            for v in n.values():
                visit(v)
        elif isinstance(n, list):
            for v in n:
                visit(v)

    visit(maker.get("body"))

    # A duplicate visible name can refer to different shadowed declarations.
    # At the insertion point source text can only name the currently visible
    # binding, so retain only unambiguous names.
    by_name = {}
    for key, name in found.items():
        by_name.setdefault(name, []).append(key)

    out = []
    idx = 0
    for key, name in sorted(found.items(), key=lambda kv: repr(kv[0])):
        if len(by_name[name]) != 1:
            continue
        idx += 1
        out.append({"decl": key, "name": name, "field": "__venv%d" % idx})
    return out


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
