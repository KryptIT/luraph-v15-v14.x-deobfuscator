"""
ironbrew1: a Luau VM obfuscator (header "-- this file was generated using
ironbrew1"). Notes: IRONBREW1.md. The script runs once with its closure
maker instrumented (instrument.py, capture.luau); the captured protos are
lifted back to Luau (devirt.py). The behaviour trace of that run is the
fallback. The VM probes the environment like Luraph (Path2D, datatype math),
which the shared runtime answers like Roblox.
"""
import os
import re
import sys
import time

import backend
import harness
import traceout as trace
from obfuscators.base import Obfuscator

HERE = os.path.dirname(os.path.abspath(__file__))
HEADER = re.compile(r"--\s*this file was generated using ironbrew1\b", re.I)
# header stripped: `return(function(a,b,...,bg,...) local bh=` + an integer
# table, or `local bh,bi,bj,...` (the wrapper takes 30+ library parameters)
SHAPE = re.compile(r"^return\s*\(\s*function\s*\((?:[a-z]{1,2},){20,}\.\.\.\)\s*"
                   r"local [a-z]{1,3}(?:=\{-?\d+,|(?:,[a-z]{1,3}){10,})")
# watchdog checks (2^20 dispatch steps each) without environment access that
# count as an endless loop. The VM decodes its constants with VM bytecode
# before the script starts (no environment access): a 200 KB string constant
# needs ~48 checks, so the limit grows with the input's size.
SPIN_CHECKS = 24
SPIN_PER_BYTES = 10000


class Ironbrew1(Obfuscator):
    name = "ironbrew1"
    label = "ironbrew1"
    doc = "IRONBREW1.md"

    def detect(self, source):
        if HEADER.search(source[:300]):
            return 1.0
        if SHAPE.match(source.lstrip()[:600]):
            return 0.8
        return 0.0

    def deobfuscate(self, job):
        from obfuscators.ironbrew1 import instrument
        args = job.args
        devirt_on = not args.no_devirt
        patched = None
        try:
            if devirt_on:
                patched, _ = backend.run_big_stack(instrument.instrument, job.source)
            else:
                patched = backend.run_big_stack(instrument.patch_spin, job.source)
        except Exception as e:  # noqa: BLE001 - an unexpected VM shape: run it as is
            print("[!] could not instrument the VM (%s: %s); tracing only" % (type(e).__name__, e), file=sys.stderr)
            devirt_on = False
        cache_path = harness.load_p2d_cache(job.input, args.studio)
        runner = harness.Runner(job)
        cfg = harness.base_cfg(args)
        if patched is not None and "__SPIN" in patched:
            cfg["spin"] = SPIN_CHECKS + len(job.source) // SPIN_PER_BYTES
        if devirt_on:
            with open(os.path.join(HERE, "capture.luau"), encoding="utf-8") as f:
                cfg["plugin_rt"] = f.read()
        cfg = harness.user_cfg(args, cfg)
        print("[*] tracing %s..." % job.input, file=sys.stderr)
        t0 = time.time()
        body, err = runner.run(patched or job.source, cfg)
        runner.finish()
        harness.save_raw(args.raw)
        if body is None:
            sys.exit("[!] " + err)
        dump = None
        m = re.search(r"\x00IBDUMP ([^\n]*)\n?", body)
        if m:
            dump = m.group(1)
            body = body[:m.start()] + body[m.end():]
        elif devirt_on:
            hook = re.search(r"\x00HOOKERR ([^\n]*)", body)
            print("[!] no proto capture%s" % (": " + hook.group(1)[:300] if hook else ""), file=sys.stderr)
        print("[*] run: %.1fs" % (time.time() - t0), file=sys.stderr)
        body = harness.take_p2d(body, cache_path, args.studio)
        body = harness.p2d_miss(body, cache_path)
        _, body = harness.take_chunks(body)
        body, strings = trace.take_strings(body)
        if strings is not None:
            job.write(job.path(".strings.txt"), strings)
        trace.status_line(body)

        def write_trace():
            # the VM's environment probes (Path2D, ...) open the trace: strip them
            text = job.credit_header() + trace.render(trace.header(job.input) + body, args, preamble=True)
            job.write(job.trace_path, text)
            return job.trace_path

        if job.debug or not devirt_on or dump is None:
            write_trace()
        if not devirt_on or dump is None:
            if devirt_on:
                print("[!] devirtualization impossible; writing the behaviour trace instead", file=sys.stderr)
            return job.trace_path
        dump_path = job.write(job.path(".ibdump.json"), dump)
        dpath = job.path(".devirt.luau")
        try:
            lift(job, dump_path, dpath)
        except Exception as e:  # noqa: BLE001 - never lose the run over a lifter bug
            print("[!] devirtualization failed: %s: %s" % (type(e).__name__, e), file=sys.stderr)
            if os.environ.get("DEVIRT_TB"):
                import traceback
                traceback.print_exc()
        if os.path.exists(dpath):
            return dpath
        print("[!] devirtualization produced no output; writing the behaviour trace instead", file=sys.stderr)
        if not os.path.exists(job.trace_path):
            write_trace()
        return job.trace_path


def lift(job, dump_path, dpath):
    import json
    from obfuscators.ironbrew1 import devirt
    t0 = time.time()
    with open(dump_path, encoding="utf-8") as f:
        d = json.load(f)
    print("[*] devirtualizing: %d functions captured (%d never ran)..." % (len(d["caps"]), d.get("forced", 0)),
          file=sys.stderr)
    text, prog = backend.run_big_stack(devirt.lift_program, job.source, d)
    st = prog.stats
    print("[*]   %d functions, %d unlifted blocks, %d unstructured jumps (%.1fs)"
          % (st["functions"], st["errors"], st["fallbacks"], time.time() - t0), file=sys.stderr)
    text = backend.run_big_stack(lambda: backend.finish_text(backend.polish(text)))
    header = (job.credit_header() +
              "-- Local names are inferred from use (the original names are not in the bytecode)\n")
    job.write(dpath, header + "\n" + text + "\n")
