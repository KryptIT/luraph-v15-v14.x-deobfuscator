"""List names read as globals that look like lifted locals (r12, s3_1, a_1, ...):
a variable used outside the scope where it was declared.
Usage: python research/scope_check.py file.luau"""
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LOCAL = re.compile(r"^[a-z]\d+(_\d+)?$|^[A-Z]\w*_\d+$|^(inf|nan)$")


def check(path):
    out = subprocess.run([os.path.join(HERE, "bin", "luau-ast.exe"), path], capture_output=True).stdout
    root = json.loads(out.decode("latin-1"))["root"]
    found = {}
    stack = [root]
    while stack:
        n = stack.pop()
        if isinstance(n, dict):
            if n.get("type") in ("AstExprGlobal",) and LOCAL.match(n["global"]):
                found.setdefault(n["global"], []).append(int(n["location"].split(",")[0]) + 1)
            elif n.get("type") == "AstStatAssign":
                pass
            stack += list(n.values())
        elif isinstance(n, list):
            stack += n
    return found


if __name__ == "__main__":
    f = check(sys.argv[1])
    for k, v in sorted(f.items(), key=lambda kv: min(kv[1])):
        print("%-10s lines %s" % (k, ", ".join(str(x) for x in sorted(v)[:8])))
    print("%d out-of-scope names" % len(f))
