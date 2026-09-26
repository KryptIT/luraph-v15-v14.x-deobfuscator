"""
Fallback for inputs no plugin recognizes: run the script once in the fake
environment and write the behaviour trace (only the branches that ran). No
instrumentation, no lifting. Also the simplest example of a plugin.
"""
import sys

import harness
import traceout as trace
from obfuscators.base import Obfuscator


class Generic(Obfuscator):
    name = "generic"
    label = "unknown obfuscator (behaviour trace only)"
    doc = ""

    def detect(self, source):
        return 0.01

    def deobfuscate(self, job):
        args = job.args
        cache_path = harness.load_p2d_cache(job.input, args.studio)
        runner = harness.Runner(job)
        cfg = harness.user_cfg(args, harness.base_cfg(args))
        print("[*] tracing %s..." % job.input, file=sys.stderr)
        body, err = runner.run(job.source, cfg)
        if body is None:
            harness.save_raw(args.raw)
            runner.finish()
            sys.exit("[!] " + err)
        runner.finish()
        harness.save_raw(args.raw)
        body = harness.take_p2d(body, cache_path, args.studio)
        body = harness.p2d_miss(body, cache_path)
        _, body = harness.take_chunks(body)
        body, strings = trace.take_strings(body)
        # generic scripts have no Luraph probes to strip at the top
        text = trace.render(trace.header(job.input) + body, args, preamble=False)
        job.write(job.trace_path, text)
        if strings is not None:
            job.write(job.path(".strings.txt"), strings)
        trace.status_line(body)
        return job.trace_path
