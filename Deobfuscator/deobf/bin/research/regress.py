"""Lifter regression run over the samples, from their saved *.protos.json
(no constant rounds: run `deob.py --devirt` for those).

    python research/regress.py OUTDIR [sample ...]

Per sample: devirt.py --all -> OUTDIR/<name>.devirt.luau, then
compile_check, scope_check, active_locals and devirt_check (trace of the
lifted file vs the obfuscated script). Samples default to research/samples/* and
the repo's samples/ scripts whose .protos.json exists (next to them or in output/).
"""
import glob
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
DATA = os.path.join(REPO, "samples")


def run(cmd, timeout=3600):
    r = subprocess.run(cmd, capture_output=True, timeout=timeout)
    return (r.stdout + r.stderr).decode("utf-8", "replace")


def find_data(src):
    """(protos.json, chunk files) of a script: next to it (research/samples)
    or in the repo's output/ folder (deob.py's default)."""
    name = re.sub(r"(\.luau?|\.txt)$", "", os.path.basename(src))
    for d in (os.path.dirname(os.path.abspath(src)), os.path.join(REPO, "output")):
        pj = os.path.join(d, name + ".protos.json")
        if os.path.exists(pj):
            return pj, glob.glob(os.path.join(d, name + ".chunk_*.luau"))
    return None, []


def samples():
    out = []
    for d in (os.path.join(HERE, "samples"), DATA):
        for src in sorted(glob.glob(os.path.join(d, "*"))):
            if re.search(r"\.(luau?|txt)$", src) and not re.search(r"\.(deobf|devirt|chunk_\w+|keypath|studio)", src)                     and find_data(src)[0]:
                out.append(src)
    return out


def main():
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)
    todo = sys.argv[2:] or samples()
    for src in todo:
        base = re.sub(r"(\.luau?|\.txt)$", "", src)
        name = os.path.basename(base)
        pj, chunks = find_data(src)
        lifted = os.path.join(outdir, name + ".devirt.luau")
        cmd = [sys.executable, os.path.join(ROOT, "obfuscators", "luraph_v15", "devirt.py"), src, pj, "--all", lifted]
        for c in chunks:
            cmd += ["--chunk", c]
        print("== %s" % name, flush=True)
        print("   lift:", run(cmd).strip().replace("\n", " | "), flush=True)
        for chk in ("compile_check.py", "scope_check.py", "active_locals.py"):
            print("   %s: %s" % (chk, run([sys.executable, os.path.join(HERE, chk), lifted]).strip()
                                 .replace("\n", " | ")[:300]), flush=True)
        dc = run([sys.executable, os.path.join(HERE, "devirt_check.py"), src, lifted,
                  "--keep", os.path.join(outdir, name + ".check")])
        print("   devirt_check:", dc.strip().replace("\n", " | ")[:600], flush=True)


if __name__ == "__main__":
    main()
