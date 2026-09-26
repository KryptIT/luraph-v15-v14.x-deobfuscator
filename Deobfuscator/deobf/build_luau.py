"""
Builds bin/luau(.exe) from Luau source with one patch: the vector type's
metatable is left writable (stock Luau freezes it in lveclib.cpp).

In Roblox, Vector3 *is* the native vector type and the engine gives it a
metatable with the Vector3 members (Magnitude, Unit, Dot, Cross, Lerp, ...).
envlog.luau installs the same members on the local VM's vector metatable;
with a stock (frozen) build, `v:Dot(w)` or `v.Magnitude` on a Vector3 value
fails with "attempt to index vector with 'Dot'".

Needs git, cmake and a C++ compiler (MSVC via a developer prompt, or gcc,
e.g. MSYS2's; Ninja is used when installed).
    python deobf/build_luau.py [--tag 0.739] [--src DIR] [--portable]
"""
import argparse
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "bin")
REPO = "https://github.com/luau-lang/luau.git"
TAG = "0.739"
FREEZE = "    lua_setreadonly(L, -1, true);\n    lua_pop(L, 1); // pop the metatable\n"
PATCHED = "    // deobf: left writable, envlog.luau adds Roblox's Vector3 members\n    lua_pop(L, 1); // pop the metatable\n"


def run(cmd, cwd=None):
    print("[*] " + " ".join(cmd), file=sys.stderr)
    subprocess.run(cmd, cwd=cwd, check=True)


def patch(src):
    path = os.path.join(src, "VM", "src", "lveclib.cpp")
    with open(path, encoding="utf-8") as f:
        text = f.read()
    if PATCHED in text:
        return
    if text.count(FREEZE) != 1:
        sys.exit("[!] lveclib.cpp changed upstream: patch createmetatable() by hand")
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text.replace(FREEZE, PATCHED))


def main():
    ap = argparse.ArgumentParser(description=__doc__.strip().splitlines()[0])
    ap.add_argument("--tag", default=TAG, help="Luau release tag (default %(default)s)")
    ap.add_argument("--src", help="existing checkout to use (default: fresh clone in a temp folder)")
    ap.add_argument("--portable", action="store_true",
                    help="gcc: no -march=native (for a binary copied to another machine)")
    args = ap.parse_args()
    tmp = None
    src = args.src
    if not src:
        tmp = tempfile.mkdtemp(prefix="luau-build-")
        src = os.path.join(tmp, "luau")
        run(["git", "clone", "-q", "--depth", "1", "--branch", args.tag, REPO, src])
    patch(src)
    build = os.path.join(src, "build-deobf")
    cfg = ["cmake", "-S", src, "-B", build, "-DCMAKE_BUILD_TYPE=Release",
           "-DLUAU_BUILD_TESTS=OFF", "-DLUAU_STATIC_CRT=ON"]
    if shutil.which("ninja"):
        cfg += ["-G", "Ninja"]
    if not shutil.which("cl") and shutil.which("g++"):
        # MinGW/Linux gcc; static so the binary needs no compiler runtime DLLs.
        # Plain -O3 ran the pipeline ~30% slower than the official MSVC build;
        # with -march=native + LTO it is a bit faster (fetched.lua 33 s vs 35 s).
        opt = "-O3 -flto" + ("" if args.portable else " -march=native")
        cfg += ["-DCMAKE_C_COMPILER=gcc", "-DCMAKE_CXX_COMPILER=g++",
                "-DCMAKE_C_FLAGS_RELEASE=%s -DNDEBUG" % opt,
                "-DCMAKE_CXX_FLAGS_RELEASE=%s -DNDEBUG" % opt,
                "-DCMAKE_EXE_LINKER_FLAGS=-static " + opt]
    run(cfg)
    run(["cmake", "--build", build, "--config", "Release", "--target", "Luau.Repl.CLI",
         "--parallel"])
    exe = "luau.exe" if os.name == "nt" else "luau"
    for cand in (os.path.join(build, "Release", exe), os.path.join(build, exe)):
        if os.path.exists(cand):
            os.makedirs(BIN, exist_ok=True)
            shutil.copy2(cand, os.path.join(BIN, exe))
            print("[+] wrote " + os.path.join(BIN, exe), file=sys.stderr)
            break
    else:
        sys.exit("[!] built binary not found under " + build)
    if tmp:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()
