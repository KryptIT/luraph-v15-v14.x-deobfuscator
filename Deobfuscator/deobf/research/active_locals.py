"""Report the maximum number of simultaneously active locals per function
(Luau's limit is 200). Usage: python research/active_locals.py file.luau [line]"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def analyze(path, target=None):
    out = subprocess.run([os.path.join(HERE, "bin", "luau-ast.exe"), path], capture_output=True).stdout
    root = json.loads(out.decode("latin-1"))["root"]
    res = {"max": 0, "at": None, "target": None}

    def visit_block(stmts, n):
        for st in stmts:
            line = int(st["location"].split(",")[0]) + 1
            if n > res["max"]:
                res["max"], res["at"] = n, line
            if target is not None and line == target and res["target"] is None:
                res["target"] = n
            t = st["type"]
            if t == "AstStatBlock":
                visit_block(st["body"], n)
            for key in ("thenbody", "elsebody", "body"):
                b = st.get(key)
                if isinstance(b, dict) and b.get("type") == "AstStatBlock":
                    extra = 1 if t == "AstStatFor" else len(st["vars"]) if t == "AstStatForIn" else 0
                    visit_block(b["body"], n + extra)
                elif isinstance(b, dict) and b.get("type") == "AstStatIf":
                    visit_block([b], n)
            funcs(st)
            if t == "AstStatLocal":
                n += len(st["vars"])
            elif t == "AstStatLocalFunction":
                n += 1

    def funcs(node):
        stack = [v for k, v in node.items() if k not in ("thenbody", "elsebody", "body")]
        while stack:
            x = stack.pop()
            if isinstance(x, dict):
                if x.get("type") == "AstExprFunction":
                    visit_block(x["body"]["body"], len(x["args"]))
                    continue
                stack += list(x.values())
            elif isinstance(x, list):
                stack += x
    visit_block(root["body"], 0)
    return res


if __name__ == "__main__":
    print(analyze(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else None))
