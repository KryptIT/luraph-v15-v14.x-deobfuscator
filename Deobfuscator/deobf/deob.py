"""
deobf: dynamic deobfuscator for Roblox Luau scripts.

Usage:
    python deob.py <input>                one input -> one output file:
                                          <input folder>/output/<input name>
    python deob.py <input> --no-devirt    faster: only the behaviour trace
    python deob.py <input> --debug        every intermediate file in output/
    python deob.py <input> --detect       only print which obfuscator it is

The input's obfuscator is detected (obfuscators/: one plugin per
obfuscator; --obfuscator NAME forces one) and its plugin runs the pipeline.
Unrecognized inputs get the generic behaviour trace: the script runs in the
real Luau VM against a fake Roblox/executor environment (envlog.luau) and
everything it does is rendered back as Luau. Nothing touches the network or
Roblox (--studio optionally runs the harness inside Roblox Studio).

Exit status: 0 with a result file, 1 on failure, 2 on bad usage.
"""
import argparse
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import obfuscators  # noqa: E402
from obfuscators.base import Job  # noqa: E402

# Lifting is pure Python (luasym's symbolic interpreter): PyPy runs it ~2x
# faster once its JIT has warmed up, which costs a few seconds. Worth it only
# for big scripts; the obfuscated file's size is a good proxy (Luraph's VM
# alone is ~230 KB).
PYPY_MIN_SIZE = 350_000


def find_pypy():
    import glob
    import shutil
    p = shutil.which("pypy3")
    if p:
        return p
    # winget installs it here; PATH may not be refreshed yet
    pat = os.path.join(os.environ.get("LOCALAPPDATA", ""), "Microsoft", "WinGet", "Packages",
                       "PyPy.PyPy.3*", "*", "pypy3.exe")
    found = sorted(glob.glob(pat))
    return found[-1] if found else None


def maybe_reexec_pypy(args):
    """Run this whole command under PyPy instead (see PYPY_MIN_SIZE)."""
    import platform
    if platform.python_implementation() == "PyPy" or args.no_pypy or args.no_devirt or args.detect:
        return
    if not args.pypy and os.path.getsize(args.input) < PYPY_MIN_SIZE:
        return
    pypy = find_pypy()
    if not pypy:
        if args.pypy:
            print("[!] --pypy: PyPy not found (winget install PyPy.PyPy.3.11); using this Python",
                  file=sys.stderr)
        return
    print("[*] big script: running under PyPy (%s; --no-pypy to turn off)" % pypy, file=sys.stderr)
    sys.stderr.flush()
    sys.exit(subprocess.call([pypy, os.path.abspath(__file__)] + sys.argv[1:]))


def parser():
    ap = argparse.ArgumentParser(description="Deobfuscate a protected Roblox Luau script.")
    ap.add_argument("input")
    ap.add_argument("-o", "--output", help="result file (default: <input folder>/output/<input name>)")
    ap.add_argument("--obfuscator", metavar="NAME",
                    help="skip detection and use this plugin (%s)" % ", ".join(p.name for p in obfuscators.PLUGINS))
    ap.add_argument("--detect", action="store_true",
                    help="only print the detected obfuscator (NAME<tab>confidence<tab>label) and exit")
    ap.add_argument("--timeout", type=int, default=90, help="hard timeout per run in seconds")
    ap.add_argument("--budget", type=int, default=30, help="soft time budget for the traced script")
    ap.add_argument("--executor", default="Wave", help="name returned by identifyexecutor()")
    ap.add_argument("--keep-harness", action="store_true", help="keep the generated harness file")
    ap.add_argument("--input-text", help="text that TextBoxes contain when event handlers are traced "
                                         "(exercises e.g. key-check branches)")
    ap.add_argument("--cfg", action="append", default=[], metavar="KEY=VALUE",
                    help="extra runtime option for envlog.luau, e.g. --cfg prelude=... (see CLAUDE.md)")
    ap.add_argument("--strings", action="store_true", help="also dump every string the script builds")
    ap.add_argument("--no-tidy", action="store_true",
                    help="write the raw trace (skip the readability pass in tidy.py)")
    ap.add_argument("--no-fold", action="store_true",
                    help="do not fold repeated helper calls and unrolled loops back into functions/loops")
    ap.add_argument("--keep-preamble", action="store_true",
                    help="keep the obfuscator's own environment/anti-tamper probes at the top of the trace")
    ap.add_argument("--raw", help="also save the complete raw runtime output of the last run here")
    ap.add_argument("--studio", action="store_true",
                    help="optional: run inside Roblox Studio so engine objects (Path2D, UDim2, ...) are real; "
                         "serves the harness on 127.0.0.1 and waits for the loader written next to the output")
    ap.add_argument("--port", type=int, default=34889, help="local port for --studio")
    ap.add_argument("--studio-wait", type=int, default=600, help="seconds to wait for Studio per run")
    ap.add_argument("--no-devirt", action="store_true",
                    help="fast: skip lifting VM bytecode; the output is the behaviour trace only")
    ap.add_argument("--devirt", action="store_true", help=argparse.SUPPRESS)   # the default now
    ap.add_argument("--debug", action="store_true",
                    help="write every intermediate file to the output folder (trace *.deobf.luau, "
                         "*.devirt.luau, ...) instead of one result file")
    ap.add_argument("--pypy", action="store_true",
                    help="run under PyPy even for a small script (default: only above %d bytes)" % PYPY_MIN_SIZE)
    ap.add_argument("--no-pypy", action="store_true", help="never switch to PyPy")
    for p in obfuscators.PLUGINS:
        p.add_arguments(ap)
    return ap


def main():
    args = parser().parse_args()
    with open(args.input, "rb") as f:
        source = f.read().decode("latin-1")
    if args.obfuscator:
        try:
            plugin, conf = obfuscators.by_name(args.obfuscator), None
        except KeyError as e:
            sys.exit("[!] %s" % e.args[0])
    else:
        plugin, conf = obfuscators.detect(source)
    if args.detect:
        print("%s\t%s\t%s" % (plugin.name, "forced" if conf is None else "%.2f" % conf, plugin.label))
        return
    maybe_reexec_pypy(args)
    print("[*] obfuscator: %s%s" % (plugin.label, "" if conf is None else " (detected, %.2f)" % conf),
          file=sys.stderr)

    outdir = os.path.join(os.path.dirname(os.path.abspath(args.input)), "output")
    tracename = re.sub(r"(\.luau?|\.txt)?$", ".deobf.luau", os.path.basename(args.input), count=1)
    workdir = None
    if args.debug:
        # every file: <input folder>/output/<name>.deobf.luau, .devirt.luau, ...
        trace_path = args.output or os.path.join(outdir, tracename)
        final = None
    else:
        # one input -> one output file (<input folder>/output/<input file name>);
        # intermediate files live in a temporary folder
        import tempfile
        workdir = tempfile.mkdtemp(prefix="deobf_")
        trace_path = os.path.join(workdir, tracename)
        final = args.output or os.path.join(outdir, os.path.basename(args.input))
    os.makedirs(os.path.dirname(os.path.abspath(final or trace_path)), exist_ok=True)
    try:
        result = plugin.deobfuscate(Job(args.input, source, args, trace_path, args.debug, plugin.label))
        if final:
            if not result or not os.path.exists(result):
                sys.exit("[!] no result")
            import shutil
            shutil.copyfile(result, final)
            print("[+] result: " + final, file=sys.stderr)
    finally:
        if workdir:
            import shutil
            shutil.rmtree(workdir, ignore_errors=True)


if __name__ == "__main__":
    main()
