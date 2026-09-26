"""Ground truth for the devirtualizer: which instructions the real VM executes.

    python obfuscators/luraph_v14_7/optrace.py <script> [--last N] [--proto-op-array] [deob.py options...]

Patches every dispatch loop head `while true do local X=Y[Z];` of the script
with table operations only (no locals, no calls: Luraph's stack-depth probe
must not change) that append "loop:arr:pc:op" to a ring buffer, runs the
trace offline and prints the last N entries. `arr` numbers the opcode arrays
(one per proto and mode) in order of first execution.

Combine with --cfg falsy=NAME / --cfg prelude=... to drive the script into a
branch the normal trace does not take, then compare with `devirt.py --raw`
(DEVIRT_TB=1 prints the opcode the lifter executed for every pc).
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(os.path.dirname(HERE)))
import harness as deob  # noqa: E402


def patch_heads(src):
    n = [0]

    def rep(m):
        n[0] += 1
        x, y, z = m.group(1), m.group(2), m.group(3)
        return (m.group(0) + "if not __TRI[%s] then __TRI.n=__TRI.n+1;__TRI[%s]=__TRI.n;end;"
                "__TR.total=__TR.total+1;__TR[(__TR.total-1)%%__TR.N+1]=\"%d:\"..__TRI[%s]..\":\"..%s..\":\"..%s;"
                % (y, y, n[0], y, z, x))
    out = re.sub(r"while true do (?:local )?([A-Za-z_]+)(?:,[A-Za-z_]+)*=\s*\(?([A-Za-z_]+)\[([A-Za-z_]+)\]\)?;", rep, src)
    return out, n[0]


def main():
    args = sys.argv[1:]
    last = 400
    if "--last" in args:
        i = args.index("--last")
        last = int(args[i + 1])
        del args[i:i + 2]
    script, rest = args[0], args[1:]
    cfg = {}
    extra_prelude = ""
    i = 0
    while i < len(rest):
        if rest[i] == "--cfg":
            k, v = rest[i + 1].split("=", 1)
            if k == "prelude":
                extra_prelude = v
            else:
                cfg[k] = True if v in ("", "true") else False if v == "false" else int(v) if re.fullmatch(r"-?\d+", v) else v
            i += 2
        else:
            i += 1
    with open(script, encoding="latin-1", newline="") as f:
        src = f.read()
    patched, nheads = patch_heads(src)
    print("[*] patched %d loop heads" % nheads, file=sys.stderr)
    cache = re.sub(r"(\.luau?|\.txt)?$", ".path2d", script, count=1)
    if os.path.exists(cache):
        with open(cache, encoding="utf-8") as f:
            for line in f:
                k, _, v = line.rstrip("\n").partition("\t")
                if k:
                    deob.P2D_CACHE[k] = v
    cfg["prelude"] = "env.__TR={total=0,N=%d};env.__TRI={n=0};" % max(last, 1) + extra_prelude
    harness = deob.build_harness(patched, cfg)
    hpath = os.path.join(HERE, "_optrace_harness.luau")
    with open(hpath, "w", encoding="latin-1", newline="\n") as f:
        f.write(harness)
    out = subprocess.run([deob.find_luau(), hpath], capture_output=True, timeout=600).stdout.decode("latin-1")
    os.remove(hpath)
    st = re.search(r"-- run status: ([^\r\n]*)", out)
    print("[*] run status:", st.group(1) if st else "?", file=sys.stderr)
    for line in out.split("\n"):
        if line.startswith("\0TR "):
            print(line[4:].rstrip("\r"))


if __name__ == "__main__":
    main()
