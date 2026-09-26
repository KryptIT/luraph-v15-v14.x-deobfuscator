"""
Plugin interface: one Obfuscator subclass per supported obfuscator (and
version). deob.py detects which plugin fits an input and calls it.

A plugin gets a Job (input, options, output paths), writes its files and
returns the path of the one result file (deob.py copies it to
output/<input name>), or None when it produced nothing. Everything shared
(the fake Roblox environment, trace rendering, the lifter back end) lives
in the deobf/ root modules: harness.py, traceout.py, ir.py, backend.py, ...
"""
import os
import re
import sys


class Obfuscator:
    name = ""           # CLI name (--obfuscator NAME), also the package name
    label = ""          # human-readable, e.g. "Luraph v15"
    doc = ""            # the plugin's notes file in the Decompiler folder (e.g. LURAPH.md)

    def detect(self, source):
        """Confidence 0..1 that `source` (latin-1 text) was made by this
        obfuscator. Cheap: header comments, signature strings, VM shape
        regexes. 0 = no. The generic fallback answers 0.01."""
        return 0.0

    def add_arguments(self, parser):
        """Plugin-specific command line options (an argparse group)."""

    def deobfuscate(self, job):
        """Run the pipeline; return the result file's path or None."""
        raise NotImplementedError


class Job:
    """One input file being deobfuscated.

    source     the input as latin-1 text (byte-exact unless a plugin normalized it)
    source_path a file with exactly `source` (the input, or the normalized copy)
    args       parsed command line (shared options + every plugin's options)
    trace_path where the trace goes (<work dir>/<name>.deobf.luau; with --debug
               in output/); other intermediate files use the same base name
    debug      --debug: intermediate files stay in output/ and are announced
    obfuscator the plugin's label, e.g. "Luraph v15" (credit_header)
    """

    def __init__(self, input_path, source, args, trace_path, debug, obfuscator=""):
        self.input = input_path
        self.source = source
        self.source_path = input_path   # file holding `source` (a plugin may normalize it into a copy)
        self.args = args
        self.trace_path = trace_path
        self.debug = debug
        self.obfuscator = obfuscator

    def credit_header(self):
        """First lines of a result file: the credit and the detected obfuscator."""
        return ("-- Why do i love gpt 5.6 sol high the reason is below.\n"
                "-- dsc.gg/oxyenv \n")

    @property
    def base(self):
        """trace_path without .deobf.luau: prefix for other intermediate files."""
        return re.sub(r"\.deobf\.luau$|\.luau$", "", self.trace_path)

    def path(self, suffix):
        return self.base + suffix

    def wrote(self, path):
        if self.debug:
            print("[+] wrote " + path, file=sys.stderr)

    def write(self, path, text, encoding="utf-8"):
        with open(path, "w", encoding=encoding, newline="\n" if encoding == "utf-8" else "") as f:
            f.write(text)
        self.wrote(path)
        return path

    @property
    def outdir(self):
        return os.path.dirname(os.path.abspath(self.trace_path))
