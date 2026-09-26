"""Semantic check for the devirtualizer: run the lifted payload in the same
fake environment as the obfuscated script and compare the two traces.

    python research/devirt_check.py <script> <script>.devirt.luau [--root PID] [--keep DIR] [deob.py options...]

The lifted file defines `local function vm_root_<pid>(...)` per VM; the
payload root (the one the file ends by calling) is called like Luraph calls it.
Both runs go through deob.py with --no-fold (plain traces; the lifted run
with --no-hooks, it has no Luraph VM). Luraph's own preamble is stripped by
tidy.py in both. Identical traces mean the lifted code did the same observable
things in the same order on this run (untaken branches are not checked).
"""
import difflib
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def trace(src_path, out_path, extra):
    r = subprocess.run([sys.executable, os.path.join(ROOT, "deob.py"), src_path, "-o", out_path, "--no-fold", "--no-devirt"]
                       + extra, capture_output=True)
    err = r.stderr.decode("utf-8", "replace")
    if r.returncode != 0 or not os.path.exists(out_path):
        sys.exit("deob.py failed on %s:\n%s" % (src_path, err[-2000:]))
    status = [l for l in err.splitlines() if l.startswith("[*] run status")]
    with open(out_path, encoding="utf-8") as f:
        return f.read(), (status[-1] if status else "?")


def body_lines(text):
    """Trace statements without the header comments and with local names
    canonicalized (tidy.py numbers instances in order: Luraph's preamble
    creates some too, which shifts every number)."""
    lines = text.split("\n")
    i = 0
    while i < len(lines) and lines[i].startswith("--"):
        i += 1
    # blank lines are layout only (spacing.py)
    lines = [l.rstrip() for l in lines[i:] if l.strip() and not l.lstrip().startswith("-- [deobf]")]
    # error positions differ (VM chunk vs lifted file): keep the message only
    lines = [re.sub(r'(-- \[envlog\] error: )(?:(?:\[string "[^"]*"\]|[\w.]+):\d+: )+', r"\1", l) for l in lines]
    # the trace records a service lookup once; Luraph's preamble looks some up first
    lines = [l for l in lines if not re.match(r'^\s*local \w+ = game:GetService\("\w+"\)$', l)]
    numbered = re.compile(r"\b([A-Za-z_][A-Za-z_]*?)\d+\b")
    out = []
    for l in lines:
        # keep string contents as they are
        parts = re.split(r'("(?:[^"\\]|\\.)*")', l)
        out.append("".join(p if p.startswith('"') else numbered.sub(r"\1", p) for p in parts))
    return out


def main():
    args = sys.argv[1:]
    script, lifted = args[0], args[1]
    rest = args[2:]
    root = None
    keep = None
    if "--keep" in rest:
        i = rest.index("--keep")
        keep = rest[i + 1]
        del rest[i:i + 2]
    if "--root" in rest:
        i = rest.index("--root")
        root = rest[i + 1]
        del rest[i:i + 2]
    with open(lifted, encoding="utf-8") as f:
        src = f.read()
    roots = re.findall(r"^-- VM \S+: root proto #(\w+) \((\d+) protos captured", src, re.M)
    if root is None and "local function vm_root_" in src:
        m = re.search(r"\nreturn vm_root_(\w+)\(\.\.\.\)\s*$", src)
        root = m.group(1) if m else max(roots, key=lambda r: int(r[1]))[0]
    if root is not None:
        # (the file ends with `return vm_root_<payload>(...)`; call the chosen root instead)
        src = re.sub(r"\nreturn vm_root_\w+\(\.\.\.\)\s*$", "\n", src) + "\nreturn vm_root_%s(...)\n" % root
    # (otherwise the payload is the file's top-level code: it runs as is)
    with tempfile.TemporaryDirectory() as tmp:
        test = os.path.join(tmp, "lifted.luau")
        with open(test, "w", encoding="utf-8", newline="\n") as f:
            f.write(src)
        a, sa = trace(script, os.path.join(tmp, "orig.deobf.luau"), rest)
        b, sb = trace(test, os.path.join(tmp, "lifted.deobf.luau"), ["--obfuscator", "luraph_v15", "--no-hooks"] + rest)
        if keep:
            import shutil
            os.makedirs(keep, exist_ok=True)
            for fn in ("orig.deobf.luau", "lifted.deobf.luau", "lifted.luau"):
                shutil.copy(os.path.join(tmp, fn), os.path.join(keep, fn))
    la, lb = body_lines(a), body_lines(b)
    print("obfuscated: %s, %d trace lines" % (sa, len(la)))
    print("lifted:     %s, %d trace lines" % (sb, len(lb)))
    if la == lb:
        print("OK: identical traces")
        return
    if sorted(la) == sorted(lb):
        # pairs() over proxy keys runs in address order (differs between processes)
        print("OK: same trace lines in another order (pairs() over proxy keys)")
        return
    sm =difflib.SequenceMatcher(None, la, lb, autojunk=False)
    same = sum(bl.size for bl in sm.get_matching_blocks())
    print("matching lines: %d of %d / %d" % (same, len(la), len(lb)))
    diff = list(difflib.unified_diff(la, lb, "obfuscated", "lifted", lineterm="", n=2))
    print("\n".join(diff[:120]))
    print("DIFFERENT (%d diff lines)" % len(diff))
    sys.exit(1)


if __name__ == "__main__":
    main()
