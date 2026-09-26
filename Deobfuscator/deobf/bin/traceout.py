"""
Behaviour trace output, shared by every obfuscator plugin: the rendered
trace of a harness run (envlog.luau) -> readable Luau (tidy.py, fold.py,
spacing.py).
"""
import os
import re
import sys


def stmt_count(body):
    m = re.search(r"-- (\d+) statements recorded", body)
    return int(m.group(1)) if m else 0


def take_line(body, name):
    """(value of the first `\\0NAME value` line, body without it); value is None if absent."""
    m = re.search(r"\x00%s ([^\n]*)\n" % name, body)
    if not m:
        return None, body
    return m.group(1), body[:m.start()] + body[m.end():]


def take_strings(body):
    """(body, the strings section of `dump_strings` or None)."""
    if "\x00ENVLOG-STRINGS" in body:
        body, strings = body.split("\x00ENVLOG-STRINGS\n", 1)
        return body, strings
    return body, None


def header(input_path, notes=()):
    h = (
         "-- source: %s\n"
         "-- yeah this ran at runtime and its gonna be shit\n"
         "-- not gonna be full \n"
         % os.path.basename(input_path))
    return h + "".join("-- %s\n" % n for n in notes)


def render(text, args, preamble=True):
    """The readable trace: tidy (+ fold) + spacing, or only the fold markers
    stripped with --no-tidy. preamble: strip Luraph-style environment probes
    at the top (tidy.strip_preamble)."""
    if os.environ.get("DEOB_PRETIDY"):
        # the text tidy/fold get, markers included (for timing or diffing fold.py alone)
        with open(os.environ["DEOB_PRETIDY"], "w", encoding="utf-8", newline="\n") as f:
            f.write(text)
    if not args.no_tidy:
        import tidy
        import spacing
        t = tidy.tidy(text, preamble=preamble and not args.keep_preamble, fold_code=not args.no_fold)
        return spacing.space(t)
    import fold
    return fold.strip_markers(text)


def status_line(body):
    status = body.splitlines()[0] if body else ""
    print("[*] " + status.lstrip("- "), file=sys.stderr)
