"""
Runs a script in the fake Roblox/executor environment (envlog.luau) and
returns what it did. Shared by every obfuscator plugin.

The harness is one Luau file: a few locals (the script, the config, recorded
Path2D answers, instrumented loadstring'd chunks, data tables) followed by
envlog.luau. It runs in the real Luau VM (bin/luau.exe), in a long-lived
REPL process (HarnessServer), or in Roblox Studio (StudioBridge, --studio).
Its stdout holds the rendered trace between \\0ENVLOG-BEGIN and
\\0ENVLOG-END, plus machine-readable lines (`\\0NAME ...`).
"""
import http.server
import os
import queue
import re
import subprocess
import sys
import threading
import time
import urllib.request
import zipfile

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "bin")
LUAU_URL = "https://github.com/luau-lang/luau/releases/latest/download/luau-windows.zip"


def find_luau():
    exe = "luau.exe" if os.name == "nt" else "luau"
    local = os.path.join(BIN, exe)
    if os.path.exists(local):
        return local
    for d in os.environ.get("PATH", "").split(os.pathsep):
        p = os.path.join(d, exe)
        if os.path.exists(p):
            return p
    if os.name != "nt":
        sys.exit("luau not found: build it with `python deobf/build_luau.py` (needs git, cmake, a C++ "
                 "compiler) or put one in " + BIN)
    print("[*] downloading Luau runtime...", file=sys.stderr)
    print("[!] stock Luau lacks the Vector3 members (v:Dot, v.Magnitude, ...): build the patched "
          "runtime with `python deobf/build_luau.py`", file=sys.stderr)
    os.makedirs(BIN, exist_ok=True)
    zpath = os.path.join(BIN, "luau.zip")
    urllib.request.urlretrieve(LUAU_URL, zpath)
    with zipfile.ZipFile(zpath) as z:
        for name in ("luau.exe", "luau-ast.exe"):
            z.extract(name, BIN)
    os.remove(zpath)
    return local


def luau_ast():
    """Path of luau-ast (prints a file's AST as JSON; decode it as latin-1)."""
    return os.path.join(BIN, "luau-ast.exe" if os.name == "nt" else "luau-ast")


def long_string(s):
    level = 0
    while ("]" + "=" * level + "]") in s:
        level += 1
    eq = "=" * level
    # a leading newline inside a long bracket is dropped, so add one of our own
    return "[" + eq + "[\n" + s + "]" + eq + "]"


def lua_value(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (list, tuple)):
        return "{" + ", ".join(lua_value(x) for x in v) + "}"
    if isinstance(v, str):
        return '"' + v.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\r", "\\r") + '"'
    return str(v)


def parse_cfg_value(v):
    """A `--cfg KEY=VALUE` value: true/false/int/string, `@file:PATH` reads a file."""
    if v.startswith("@file:"):
        # long values (e.g. force_req / force_buf) from a file
        with open(v[6:], encoding="utf-8") as f:
            v = f.read().strip()
    return True if v in ("", "true") else False if v == "false" else \
        int(v) if re.fullmatch(r"-?\d+", v) else v


def base_cfg(args):
    """The runtime config (envlog.luau CFG) from the shared command line options."""
    cfg = {"time_budget": args.budget, "executor": args.executor}
    if args.input_text is not None:
        cfg["input_text"] = args.input_text
    return cfg


def user_cfg(args, cfg):
    """--cfg KEY=VALUE options on top of cfg (they win over plugin defaults)."""
    for kv in args.cfg:
        k, _, v = kv.partition("=")
        cfg[k] = parse_cfg_value(v)
    return cfg


# --------------------------------------------------------------------------
# Path2D answers (engine float bits some obfuscators key stages with)

P2D_CACHE = {}


def p2d_cache_path(input_path):
    return re.sub(r"(\.luau?|\.txt)?$", ".path2d", input_path, count=1)


def load_p2d_cache(input_path, studio=False):
    """Path2D answers recorded by an earlier --studio run of this script."""
    cache_path = p2d_cache_path(input_path)
    if os.path.exists(cache_path):
        with open(cache_path, encoding="utf-8") as f:
            for line in f:
                k, _, v = line.rstrip("\n").partition("\t")
                if k:
                    P2D_CACHE[k] = v
        if not studio:
            print("[*] replaying %d recorded Path2D results from %s" % (len(P2D_CACHE), cache_path), file=sys.stderr)
    return cache_path


def take_p2d(body, cache_path, studio):
    """Strip the \\0P2D lines of a run; engine answers from Studio go to the cache file."""
    rec = re.findall(r"\x00P2D ([^\t\n]+)\t([^\n]*)\n", body)
    body = re.sub(r"\x00P2D [^\n]*\n", "", body)
    nmodel = sum(1 for k, v in rec if v.endswith("\tmodel"))
    if nmodel:
        print("[*] %d Path2D answers computed by the offline engine model" % nmodel, file=sys.stderr)
    rec = [(k, v) for k, v in rec if not v.endswith("\tmodel")]
    if rec and studio:
        for k, v in rec:
            P2D_CACHE[k] = v
        with open(cache_path, "w", encoding="utf-8", newline="\n") as f:
            f.write("".join("%s\t%s\n" % kv for kv in P2D_CACHE.items()))
    return body


def p2d_miss(body, cache_path):
    if "\x00P2DMISS" not in body:
        return body
    print("[!] this script derives keys from a Path2D call the offline model does not cover\n"
          "    (e.g. a Frame sized with Scale); run it once with --studio (writes %s)" % cache_path,
          file=sys.stderr)
    return body.replace("\x00P2DMISS\n", "")


# --------------------------------------------------------------------------
# building and running a harness

def build_harness(source, cfg, chunks=None):
    with open(os.path.join(HERE, "envlog.luau"), encoding="utf-8") as f:
        runtime = f.read()
    cfg_lua = "{" + ", ".join("%s = %s" % (k, lua_value(v)) for k, v in cfg.items()) + "}"
    # --!nocheck must stay the first line of the runtime, so strip it
    runtime = runtime.replace("--!nocheck", "", 1)
    with open(os.path.join(HERE, "unicode_data.luau"), encoding="ascii") as f:
        udata = f.read()
    with open(os.path.join(HERE, "roblox_api.luau"), encoding="ascii") as f:
        rdata = f.read()
    with open(os.path.join(HERE, "datatypes.luau"), encoding="utf-8") as f:
        dtypes = f.read().replace("--!nocheck", "", 1)
    return ("local __SOURCE = " + long_string(source) + "\n"
            "local __CONFIG = " + cfg_lua + "\n"
            "local __P2D = {" + "".join("[%s] = %s,\n" % (lua_value(k), lua_value(v))
                                        for k, v in P2D_CACHE.items()) + "}\n"
            "local __CHUNKS = {" + "".join("[%s] = %s,\n" % (lua_value(k), long_string(v))
                                           for k, v in (chunks or {}).items()) + "}\n"
            "local __UNICODE = (function()\n" + udata + "\nend)()\n"
            "local __ROBLOX = (function()\n" + rdata + "\nend)()\n"
            # offline datatype models; no new top-level local (the chunk is at Luau's limit)
            "__ROBLOX.datatypes = (function()\n" + dtypes + "\nend)()\n" + runtime)


def chunk_key(src):
    """Same key as srcKey() in envlog.luau."""
    h = 0
    for b in src.encode("latin-1"):
        h = (h * 31 + b) % 2147483648
    return "%d_%d" % (len(src), h)


def take_chunks(body):
    """[(key, source)] of the big loadstring'd chunks a run reported (\\0CHUNK),
    and the body without them. Chunks passed back in `chunks` run instead of
    the original (a plugin instruments them like the main script)."""
    found = re.findall(r"\x00CHUNK (\S+)\n([0-9a-f]*)\n", body)
    body = re.sub(r"\x00CHUNK \S+\n[0-9a-f]*\n", "", body)
    return [(k, bytes.fromhex(hx).decode("latin-1")) for k, hx in found], body


LAST_RAW = [""]     # complete runtime output of the last run (--raw)


HEARTBEAT = 2       # seconds between the runtime's heartbeats (envlog checkBudget)
STALL = 20          # no output for this long: stuck in pure script code (an endless loop)


def _communicate(cmd, timeout, stall):
    """subprocess.run(capture_output=True) that also gives up when the process
    prints nothing for `stall` seconds (the runtime's heartbeat stopped: the
    script spins without touching the environment). (stdout, stderr) bytes,
    or a TimeoutExpired."""
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    parts = {1: [], 2: []}
    last = [time.time()]

    def pump(stream, key):
        while True:
            b = stream.read1(65536) if hasattr(stream, "read1") else stream.read(65536)
            if not b:
                return
            parts[key].append(b)
            last[0] = time.time()
    threads = [threading.Thread(target=pump, args=(proc.stdout, 1), daemon=True),
               threading.Thread(target=pump, args=(proc.stderr, 2), daemon=True)]
    for t in threads:
        t.start()
    t0 = time.time()
    try:
        while proc.poll() is None:
            now = time.time()
            if now - t0 > timeout or (stall and now - last[0] > stall):
                proc.kill()
                proc.wait()
                raise subprocess.TimeoutExpired(cmd, now - t0)
            time.sleep(0.1)
    finally:
        for t in threads:
            t.join(5)
    return b"".join(parts[1]), b"".join(parts[2])


def run_once(luau, source, cfg, hpath, timeout, keep, chunks=None):
    cfg = dict(cfg, heartbeat=HEARTBEAT) if "heartbeat" not in cfg else cfg
    with open(hpath, "w", encoding="latin-1", newline="\n") as f:
        f.write(build_harness(source, cfg, chunks))
    try:
        out, errb = _communicate([luau, hpath], timeout, STALL if cfg.get("heartbeat") else None)
    except subprocess.TimeoutExpired as e:
        return None, "timed out after %ds (script is stuck in a loop the tracer cannot see)" % e.timeout
    finally:
        if not keep and os.path.exists(hpath):
            os.remove(hpath)
    stdout = re.sub(r"\x00HB\r?\n {16384}\r?\n", "", out.decode("utf-8", "replace")).replace("\r\n", "\n")
    LAST_RAW[0] = stdout + errb.decode("utf-8", "replace")
    m = re.search(r"\x00ENVLOG-BEGIN\n(.*?)\x00ENVLOG-END", stdout, re.S)
    if not m:
        return None, stdout[-3000:] + "\n" + errb.decode("utf-8", "replace")[-3000:]
    # errors raised inside the runtime name the (temporary) harness file: drop
    # "<harness path>:<line>: " (literal: a regex would crawl the PROTOS line)
    body = m.group(1)
    for hp in {hpath, hpath.replace("\\", "/")}:
        if hp + ":" in body:
            body = re.sub(re.escape(hp) + r":\d+: ", "", body)
    return body, None


def save_raw(path):
    if path:
        with open(path, "w", encoding="utf-8", newline="\n") as f:
            f.write(LAST_RAW[0])


class HarnessServer:
    """One harness process kept alive for many dumps: the script runs once,
    then each request only repeats the dump for new force_req / force_buf
    (CHAIN.serve in envlog.luau). luau.exe has no file or stdin API,
    but its REPL reads statements from stdin and require() reads files: the
    harness is require()d (it returns CHAIN.serve) and every request is a small
    module holding the long strings, called by a one-line statement.
    Its output is read in raw chunks up to the ENVLOG-END sentinel: stdout to a
    pipe is block-buffered, and the padding the harness prints after the
    sentinel only pushes the buffer out."""
    END = b"\x00ENVLOG-END"

    def __init__(self, luau, source, cfg, chunks):
        import tempfile
        self.dir = tempfile.mkdtemp(prefix="deobf_serve_")
        with open(os.path.join(self.dir, "harness.luau"), "w", encoding="latin-1", newline="\n") as f:
            f.write(build_harness(source, dict(cfg, serve=True), chunks))
        self.proc = subprocess.Popen([luau], cwd=self.dir, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT)
        self.buf = b""
        self.eof = False
        self.nreq = 0
        # replies are read synchronously (a reader thread handing chunks to
        # the waiting thread costs ~12 ms per round trip under PyPy, i.e. most
        # of the live-request time); a watchdog thread enforces the deadline
        self.deadline = None
        self.timed_out = False
        threading.Thread(target=self._watchdog, daemon=True).start()
        # the run starts from its own statement, not inside require() (C call depth)
        self._send(b'__S = require("./harness")\n__S("", "", "start")\n')

    def _watchdog(self):
        while self.proc.poll() is None:
            d = self.deadline
            if d is not None and time.time() > d:
                self.timed_out = True
                self.proc.kill()
                return
            time.sleep(0.25)

    def _send(self, line):
        try:
            self.proc.stdin.write(line)
            self.proc.stdin.flush()
        except OSError:
            pass    # the process died: the reply wait reports it

    def reply(self, timeout):
        """The next response (the text between ENVLOG-BEGIN and ENVLOG-END), or
        (None, error)."""
        self.deadline = time.time() + timeout
        try:
            start = 0
            while self.END not in self.buf[start:]:
                start = max(0, len(self.buf) - len(self.END))
                b = b"" if self.eof else self.proc.stdout.read1(1 << 20)
                if not b:
                    self.eof = True
                    out = self.buf.decode("utf-8", "replace")
                    self.close()
                    return None, ("no reply within %ds" % timeout if self.timed_out else
                                  "harness process exited") + ": " + out[-3000:]
                self.buf += b
        finally:
            self.deadline = None
        i = self.buf.index(self.END) + len(self.END)
        out, self.buf = self.buf[:i], self.buf[i:]
        out = out.decode("utf-8", "replace").replace("\r\n", "\n")
        LAST_RAW[0] = out
        m = re.search(r"\x00ENVLOG-BEGIN\n(.*?)\x00ENVLOG-END", out, re.S)
        if not m:
            return None, out[-3000:]
        return m.group(1), None

    def request(self, cfg, timeout, mode="dump"):
        req, buf = cfg.get("force_req") or "", cfg.get("force_buf") or ""
        if len(req) + len(buf) < 2000 and re.fullmatch(r"[\w,@.;=+/:*\-]*", req + buf):
            # small (live requests): inline, no request file
            self._send(('__S("%s", "%s", "%s")\n' % (req, buf, mode)).encode())
            return self.reply(timeout)
        self.nreq += 1
        name = "req_%d" % self.nreq
        with open(os.path.join(self.dir, name + ".luau"), "w", encoding="utf-8", newline="\n") as f:
            f.write("return {%s, %s, %s}\n" % (long_string(cfg.get("force_req") or ""),
                                              long_string(cfg.get("force_buf") or ""), long_string(mode)))
        self._send(b'__S(table.unpack(require("./%s")))\n' % name.encode())
        return self.reply(timeout)

    def fetch(self, paths, bufs, timeout):
        """Constants decoded right away, in the session of the last dump
        (CHAIN.fetch): JSON {"values": [[path, value]], "tables": {...}}."""
        body, err = self.request({"force_req": ";".join(paths), "force_buf": bufs}, timeout, "fetch")
        if body is None:
            raise RuntimeError("harness fetch failed: " + err[-300:])
        m = re.search(r"\x00FETCH ([^\n]*)\n", body)
        if not m or m.group(1).startswith("error:"):
            raise RuntimeError("harness fetch failed: " + (m.group(1)[:300] if m else body[-300:]))
        return m.group(1)

    def close(self):
        if self.proc.poll() is None:
            self.proc.kill()
            self.proc.wait()
        import shutil
        shutil.rmtree(self.dir, ignore_errors=True)


def trace_text(body):
    """The shape of a run's trace, to tell whether two runs behaved the same:
    no machine-readable lines, and string/number literals masked (scripts
    that use random values trace differently every run; a wrong key
    changes what runs, not just literals)."""
    body = re.sub(r"\x00CHUNK \S+\n[0-9a-f]*\n", "", body)
    body = re.sub(r"\x00(PROTOS|FORCE|P2D|TRIGGER)[^\n]*\n?", "", body)
    # error positions and tracebacks name the harness file, whose path differs
    # (run_once drops "<harness>:line: " prefixes; a served harness keeps them)
    body = re.sub(r"(?<=[ \t])(?=\S)(?:[A-Za-z]:)?[^:\n]*?\.luau:", "harness:", body)
    body = re.sub(r"harness:\d+: ", "", body)
    body = re.sub(r'"(?:[^"\\\n]|\\.)*"', '""', body)
    return re.sub(r"\d+(?:\.\d+)?(?:e[-+]?\d+)?", "0", body)


def same_trace(a, b):
    """trace_text(a) == trace_text(b), ignoring words only one of the two
    runs has: scripts that make up random names every run (diaz.txt:
    getgenv() keys, bait URLs) trace the same statements with other names
    (in another order too: pairs() over other keys). Last resort: the same
    lines in any order, local names masked."""
    if a == b:
        return True
    wa, wb = set(re.findall(r"\w+", a)), set(re.findall(r"\w+", b))
    only = (wa ^ wb)
    mask = lambda t: re.sub(r"\w+", lambda m: "_" if m.group(0) in only else m.group(0), t)  # noqa: E731
    ma, mb = mask(a), mask(b)
    if ma == mb:
        return True
    # pairs() over proxy keys (hub.lua: players) runs in address order, which
    # differs between processes: the same statements in another order, the
    # trace's local names numbered in that order
    decl = r"\blocal\s+([\w ,]+)|\bfor\s+([\w ,]+)\bin\b|\bfunction\s*\w*\s*\(([\w ,.]*)\)"
    names = set()
    for m in re.finditer(decl, a + "\n" + b):
        names.update(re.findall(r"\w+", "".join(g or "" for g in m.groups())))
    anon = lambda t: sorted(re.sub(r"\w+", lambda m: "_" if m.group(0) in names else m.group(0), t)  # noqa: E731
                            .splitlines())
    return anon(ma) == anon(mb)


# --------------------------------------------------------------------------
# Roblox Studio (--studio)

STUDIO_LOADER = r"""-- deobf Studio loader: run in the Studio command bar (Edit mode).
-- Fetches each harness from deob.py, runs it natively and posts the trace back.
-- HTTP is only on while talking to 127.0.0.1 (never while the script runs)
-- and is restored to its previous setting at the end.
local HS = game:GetService("HttpService")
local base = "http://127.0.0.1:%d"
local was = HS.HttpEnabled
HS.HttpEnabled = true
local ok0, err0 = pcall(function()
	while true do
		local src = HS:GetAsync(base .. "/harness", true)
		if src == "" then break end
		HS.HttpEnabled = false
		local f, err = loadstring(src, "=harness")
		local ok, out = false, err
		if f then ok, out = pcall(f) end
		HS.HttpEnabled = true
		out = ok and tostring(out) or ("\0ENVLOG-FAIL\n" .. tostring(out))
		-- HttpService posts are limited to 1 MB: send in parts
		local n = math.max(1, math.ceil(#out / 900000))
		for i = 1, n do
			HS:PostAsync(base .. "/result?part=" .. i .. "&of=" .. n, string.sub(out, (i - 1) * 900000 + 1, i * 900000),
				Enum.HttpContentType.TextPlain)
		end
	end
end)
HS.HttpEnabled = was
return ok0 and "deobf: done" or ("deobf loader error: " .. tostring(err0))
"""


class StudioBridge:
    """Local HTTP endpoint the Studio loader talks to. GET /harness blocks until
    the next harness is ready ("" when finished); POST /result takes the trace."""

    def __init__(self, port):
        self.jobs = queue.Queue()
        self.results = queue.Queue()
        self.parts = []
        bridge = self

        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, *a):
                pass

            def do_GET(self):
                if self.path != "/harness":
                    self.send_error(404)
                    return
                body = bridge.jobs.get()
                self.send_response(200)
                self.send_header("Content-Type", "text/plain")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def do_POST(self):
                data = self.rfile.read(int(self.headers.get("Content-Length", 0)))
                self.send_response(200)
                self.send_header("Content-Length", "0")
                self.end_headers()
                m = re.search(r"part=(\d+)&of=(\d+)", self.path)
                part, of = (int(m.group(1)), int(m.group(2))) if m else (1, 1)
                bridge.parts.append(data)
                if part == of:
                    bridge.results.put(b"".join(bridge.parts))
                    bridge.parts = []

        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", port), Handler)
        threading.Thread(target=self.server.serve_forever, daemon=True).start()

    def run(self, harness, timeout):
        self.jobs.put(harness.encode("latin-1"))
        try:
            return self.results.get(timeout=timeout).decode("utf-8", "replace")
        except queue.Empty:
            return None

    def finish(self):
        self.jobs.put(b"")
        time.sleep(1)  # let the loader pick up the stop signal


def run_once_studio(bridge, source, cfg, timeout, chunks=None):
    out = bridge.run(build_harness(source, dict(cfg, native=True), chunks), timeout)
    if out is None:
        return None, "no result from Studio within %ds (is the loader running?)" % timeout
    out = out.replace("\r\n", "\n")
    LAST_RAW[0] = out
    if out.startswith("\x00ENVLOG-FAIL"):
        return None, "harness failed in Studio: " + out[len("\x00ENVLOG-FAIL\n"):]
    m = re.search(r"\x00ENVLOG-BEGIN\n(.*?)\x00ENVLOG-END", out, re.S)
    if not m:
        return None, out[-3000:]
    return m.group(1), None


class Runner:
    """Runs harnesses for one job: offline with luau.exe, or in Studio with
    --studio (writes the loader next to the output and waits for it)."""

    def __init__(self, job):
        self.job = job
        args = job.args
        self.bridge = None
        self.luau = None
        self.hpath = job.trace_path + ".harness.luau"
        if args.studio:
            self.bridge = StudioBridge(args.port)
            lpath = re.sub(r"\.luau$", "", job.trace_path) + ".studio_loader.luau"
            with open(lpath, "w", encoding="utf-8", newline="\n") as f:
                f.write(STUDIO_LOADER % args.port)
            print("[*] Studio mode: run %s in the Studio command bar (Edit mode)" % lpath, file=sys.stderr)
        else:
            self.luau = find_luau()

    def run(self, source, cfg, chunks=None):
        """(body, None) or (None, error)."""
        a = self.job.args
        if self.bridge:
            return run_once_studio(self.bridge, source, cfg, a.studio_wait, chunks)
        return run_once(self.luau, source, cfg, self.hpath, a.timeout, a.keep_harness, chunks)

    def finish(self):
        if self.bridge:
            self.bridge.finish()
            self.bridge = None
