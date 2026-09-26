"""Check that fold.py keeps behaviour: trace a script once, render it with and
without folding, run both outputs against research/fold_check.luau's logging
environment and compare the operation logs.

    python research/fold_check.py <script> [deob.py options...]
"""
import difflib
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
import tidy  # noqa: E402


def run_log(src, tmp):
    path = os.path.join(tmp, "check.luau")
    with open(os.path.join(HERE, "fold_check.luau"), encoding="utf-8") as f:
        checker = f.read()
    # the output under test becomes the checker's vararg
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write("return (function(...)\n" + checker + "\nend)(" + long_string(src) + ")\n")
    exe = os.path.join(ROOT, "bin", "luau.exe" if os.name == "nt" else "luau")
    r = subprocess.run([exe, path], capture_output=True)
    return r.stdout.decode("utf-8", "replace").replace("\r\n", "\n")


def leaked(src, tmp):
    """Names read as globals although the file declares a local of that name
    somewhere: a local read outside its scope (the trace records values, and
    a value can outlive the function that made it)."""
    path = os.path.join(tmp, "leak.luau")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(src)
    exe = os.path.join(ROOT, "bin", "luau-ast.exe" if os.name == "nt" else "luau-ast")
    root = json.loads(subprocess.run([exe, path], capture_output=True).stdout.decode("latin-1"))["root"]
    glob, loc = set(), set()

    def walk(n):
        if isinstance(n, dict):
            if n.get("type") == "AstExprGlobal":
                glob.add(n["global"])
            elif n.get("type") == "AstLocal":
                loc.add(n["name"])
            for v in n.values():
                walk(v)
        elif isinstance(n, list):
            for v in n:
                walk(v)
    walk(root)
    return glob & loc


def long_string(s):
    level = 0
    while ("]" + "=" * level + "]") in s:
        level += 1
    return "[" + "=" * level + "[\n" + s + "]" + "=" * level + "]"


def main():
    script = sys.argv[1]
    with tempfile.TemporaryDirectory() as tmp:
        # the raw runtime output of the last run still has fold.py's statement markers
        subprocess.run([sys.executable, os.path.join(ROOT, "deob.py"), script, "-o",
                        os.path.join(tmp, "out.luau"), "--raw", os.path.join(tmp, "full.txt")] + sys.argv[2:],
                       check=True, capture_output=True)
        with open(os.path.join(tmp, "full.txt"), encoding="utf-8") as f:
            full = f.read()
        body = full.split("\x00ENVLOG-BEGIN\n", 1)[1].split("\x00ENVLOG-END", 1)[0]
        body = body.split("\x00ENVLOG-STRINGS", 1)[0]
        body = re.sub(r"\x00CHUNK \S+\n[0-9a-f]*\n", "", body)
        body = "\n".join(l for l in body.split("\n") if not l.startswith("\x00"))
        plain = tidy.tidy(body, fold_code=False)
        folded = tidy.tidy(body, fold_code=True)
        # values read outside their scope are already in the unfolded trace;
        # folding must not add any
        leak_a, leak_b = leaked(plain, tmp), leaked(folded, tmp)
        if leak_b - leak_a:
            print("NEW out-of-scope reads after folding:", ", ".join(sorted(leak_b - leak_a)))
        # the unfolded trace can exceed Luau's 200 locals per function; its local
        # names are unique, so plain assignments behave the same (except for
        # the leaked ones, which must stay out of scope as they are)

        def unlocal(m):
            names = [x.strip() for x in m.group(2).split(",")]
            return m.group(0) if any(x in leak_a for x in names) else m.group(1) + m.group(2) + " ="
        a = run_log(re.sub(r"^(\t*)local ([\w, ]+) =", unlocal, plain, flags=re.M), tmp)
        b = run_log(folded, tmp)
    la, lb = a.split("\n"), b.split("\n")
    print("unfolded: %d lines of code, %d logged operations" % (plain.count("\n"), len(la)))
    print("folded:   %d lines of code, %d logged operations" % (folded.count("\n"), len(lb)))
    if la == lb:
        print("OK: identical behaviour logs")
        return
    diff = list(difflib.unified_diff(la, lb, "unfolded", "folded", lineterm="", n=2))
    print("\n".join(diff[:80]))
    print("DIFFERENT (%d diff lines)" % len(diff))
    sys.exit(1)


if __name__ == "__main__":
    main()
