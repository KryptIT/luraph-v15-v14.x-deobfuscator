"""Compile-check a Luau file with the real compiler (loadstring), without running it.
Usage: python research/compile_check.py file.luau"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def check(path):
    src = open(path, encoding="utf-8", errors="replace").read()
    eq = "=" * 8
    while ("]" + eq + "]") in src:
        eq += "="
    prog = "local f, e = loadstring([%s[%s]%s])\nprint(f and 'COMPILE OK' or ('COMPILE ERROR: ' .. tostring(e)))\n" % (
        eq, src, eq)
    tmp = path + ".check.luau"
    with open(tmp, "w", encoding="utf-8", newline="\n") as f:
        f.write(prog)
    try:
        out = subprocess.run([os.path.join(HERE, "bin", "luau.exe"), tmp], capture_output=True, timeout=120)
    finally:
        os.remove(tmp)
    return (out.stdout + out.stderr).decode("utf-8", "replace").strip()


if __name__ == "__main__":
    print(check(sys.argv[1]))
