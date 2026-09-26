"""Luraph v14.9 devirtualizer engine, adapted from the v15 engine."""
import re
import sys

from obfuscators.base import Obfuscator

HEADER = re.compile(r"This file was protected using Luraph Obfuscator v(\d+)(?:\.(\d+))?")
HEADER_LINE = re.compile(r"\s*--[ \t]*This file was protected using Luraph Obfuscator v[\d.]+[ \t]*"
                         r"\[https?://lura\.ph/?\]")


class LuraphV149(Obfuscator):
    name = "luraph_v14_9"
    label = "Luraph v14.9"
    doc = "LURAPH.md"

    def detect(self, source):
        m = HEADER.search(source[:500])
        if m:
            version = m.group(1) + (("." + m.group(2)) if m.group(2) else "")
            if version == "14.9":
                return 1.0
            if m.group(1) == "14":
                return 0.15
            return 0.0
        # Headerless v14.9 samples commonly keep the init wrapper before the VM object.
        head = source.lstrip()[:4000]
        if head.startswith("local init = (function(...") and "return({" in source[:20000]:
            return 0.82
        if head.startswith("return({") and "bit32" in source[:100000]:
            return 0.42
        return 0.0

    def add_arguments(self, ap):
        g = ap.add_argument_group("Luraph v14.9")
        g.add_argument("--no-hooks", action="store_true",
                       help="do not instrument VM functions (no anti-tamper trap attribution, no lifting)")
        g.add_argument("--max-runs", type=int, default=12, help="maximum number of trace runs (trap reruns)")
        g.add_argument("--devirt-rounds", type=int, default=200,
                       help="max lift + constant-request rounds (stops early at the fixed point)")

    def deobfuscate(self, job):
        from obfuscators.luraph_v14_9 import driver
        fixed = restore_header_newline(job.source)
        if fixed != job.source:
            print("[*] header comment ran into the code (lost newline): split it", file=sys.stderr)
            job.source = fixed
            job.source_path = job.write(job.path(".src.lua"), fixed, encoding="latin-1")
        return driver.run(job)


def restore_header_newline(source):
    m = HEADER_LINE.match(source)
    if m and source[m.end():m.end() + 1] not in ("", "\n", "\r"):
        return source[:m.end()] + "\n" + source[m.end():].lstrip(" \t")
    return source
