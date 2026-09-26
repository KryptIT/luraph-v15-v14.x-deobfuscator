"""Fold the trace back into helper functions and loops (runs inside tidy).

    python fold.py file.deobf.luau      (only useful on output that still has markers)

The runtime prefixes every rendered statement with a marker line

    --@<n> <pid>:<inv>,<pid>:<inv>,...

<n> is the number of output lines the statement takes (nested markers
included). The chain lists the script functions (Luraph protos) that were on
the Lua stack when the statement was recorded, outermost first, each with the
number of its invocation. So consecutive statements that share an entry
beyond the enclosing function's own frame were produced by one call of a
helper.

1. Helpers. When a proto was called several times and every call produced the
   same statement shape (literals and outside names may differ), the calls
   are folded, innermost helpers first:

       local function createPreview(parent, image, text)  -- body of the first call
           ...                                            -- differing tokens -> parameters
           return button                                  -- locals used after the call
       end
       local LittleCrosshair = createPreview(Grid2, "rbxthumb://...", "Little Crosshair")

   A helper is defined at top level, right before the top-level statement
   holding its first call. A local the body reads that is not visible there
   becomes a parameter as well.

2. Loops. Consecutive groups of statements with the same shape (a loop body
   the trace unrolled, or a run of helper calls) become

       for _, v in ipairs({ { name = "A", order = 1 }, ... }) do <body using v.name> end

   when none of the locals a group makes is used after it.
"""
import argparse
import bisect
import re
import sys
from collections import Counter

KEYWORDS = {"and", "break", "do", "else", "elseif", "end", "for", "function", "if", "in",
            "local", "not", "or", "repeat", "return", "then", "until", "while", "continue"}
LITERAL_KW = {"true", "false", "nil"}
MARK = re.compile(r"^(\t*)--@(\d+) ?(.*)$")
TOK = re.compile(r"""
 (?P<ws>[ \t\r\n]+)
|(?P<comment>--\[(?P<eq>=*)\[.*?\](?P=eq)\]|--[^\n]*)
|(?P<str>"(?:[^"\\\n]|\\.)*"|'(?:[^'\\\n]|\\.)*'|\[(?P<eq2>=*)\[.*?\](?P=eq2)\])
|(?P<num>0[xX][0-9a-fA-F_]+|0[bB][01_]+|(?:\d[\d_]*\.?[\d_]*|\.\d[\d_]*)(?:[eE][+-]?\d+)?)
|(?P<name>[A-Za-z_]\w*)
|(?P<op>\.\.\.|\.\.=|==|~=|<=|>=|//=|//|\.\.|::|->|\+=|-=|\*=|/=|%=|\^=|[-+*/%^\#<>=(){}\[\];:,.&|?~])
""", re.S | re.X)
# names never used for a new helper, parameter or loop variable
RESERVED = KEYWORDS | LITERAL_KW | {
    "game", "workspace", "script", "Instance", "Enum", "Vector2", "Vector3", "CFrame", "Color3", "UDim",
    "UDim2", "Font", "TweenInfo", "task", "math", "string", "table", "coroutine", "os", "debug", "utf8",
    "bit32", "buffer", "print", "warn", "error", "type", "typeof", "pairs", "ipairs", "next", "select",
    "pcall", "xpcall", "tostring", "tonumber", "require", "wait", "spawn", "delay", "tick", "time",
    "shared", "_G", "self", "unpack", "setmetatable", "getmetatable", "loadstring", "_",
}
MAX_PARAMS = 16
MAX_PERIOD = 400  # statements in one loop body


# ---------------------------------------------------------------------------
# tokens
# ---------------------------------------------------------------------------
class Tok:
    __slots__ = ("kind", "text", "start", "end", "role")

    def __init__(self, kind, text, start, end):
        self.kind, self.text, self.start, self.end = kind, text, start, end
        self.role = None  # names: "var", "field" (x.Name) or "key" ({ Name = 1 })

    @property
    def hole(self):
        """Can differ between two occurrences of the same shape."""
        return self.kind == "lit" or self.role == "var"


def tokenize(src):
    out = []
    pos = 0
    while pos < len(src):
        m = TOK.match(src, pos)
        if not m:
            out.append(Tok("op", src[pos], pos, pos + 1))
            pos += 1
            continue
        kind = m.lastgroup
        if kind in ("eq", "eq2"):
            kind = "comment" if m.group("comment") else "str"
        if kind != "ws":
            text = m.group(0)
            if kind == "name" and text in KEYWORDS:
                kind = "kw"
            elif (kind == "name" and text in LITERAL_KW) or kind in ("str", "num"):
                kind = "lit"
            out.append(Tok(kind, text, m.start(), m.end()))
        pos = m.end()
    brackets = []
    for i, t in enumerate(out):
        if t.kind == "op" and t.text in "({[":
            brackets.append(t.text)
        elif t.kind == "op" and t.text in ")}]":
            if brackets:
                brackets.pop()
        elif t.kind == "name":
            prev = out[i - 1] if i else None
            nxt = out[i + 1] if i + 1 < len(out) else None
            if prev and prev.kind == "op" and prev.text in (".", ":"):
                t.role = "field"
            elif nxt and nxt.kind == "op" and nxt.text == "=" and brackets and brackets[-1] == "{":
                t.role = "key"
            else:
                t.role = "var"
    return out


def skeleton(toks):
    return "\1".join("\0" + t.kind if t.hole else t.text for t in toks)


def declared(toks):
    """Names declared anywhere in the token list (locals, function params, loop vars)."""
    out = set()
    n = len(toks)
    for i, t in enumerate(toks):
        if t.kind != "kw":
            continue
        if t.text == "local":
            j = i + 1
            if j < n and toks[j].text == "function":
                if j + 1 < n and toks[j + 1].kind == "name":
                    out.add(toks[j + 1].text)
                continue
            while j < n and toks[j].kind == "name":
                out.add(toks[j].text)
                if j + 1 < n and toks[j + 1].text == ",":
                    j += 2
                else:
                    break
        elif t.text == "function":
            j = i + 1
            while j < n and (toks[j].kind == "name" or toks[j].text in (".", ":")):
                j += 1
            if j < n and toks[j].text == "(":
                j += 1
                while j < n and toks[j].text != ")":
                    if toks[j].kind == "name":
                        out.add(toks[j].text)
                    j += 1
        elif t.text == "for":
            j = i + 1
            while j < n and toks[j].text not in ("in", "="):
                if toks[j].kind == "name":
                    out.add(toks[j].text)
                j += 1
    return out


def var_counts(toks):
    return Counter(t.text for t in toks if t.kind == "name" and t.role == "var")


def decl_line(line):
    """Locals a statement line declares at its own level."""
    m = re.match(r"\t*local (?:function (\w+)|([\w, ]+?)\s*(?:=|$))", line)
    if not m:
        return []
    if m.group(1):
        return [m.group(1)]
    return [x.strip() for x in m.group(2).split(",") if x.strip()]


# ---------------------------------------------------------------------------
# statement tree
# ---------------------------------------------------------------------------
class Raw:
    __slots__ = ("line",)

    def __init__(self, line):
        self.line = line


class Stmt:
    __slots__ = ("chain", "items")

    def __init__(self, chain, items):
        self.chain, self.items = chain, items


class Inv:
    """Consecutive statements recorded during one invocation of one proto.
    Once folded, `call` holds the lines that replace them."""
    __slots__ = ("key", "items", "call", "root", "height", "rec")

    def __init__(self, key, items):
        self.key, self.items = key, items
        self.call = None
        self.root = None  # the top-level item that contains it
        self.height = 1
        self.rec = None  # folded: (helper name, args, returned names)


def parse_chain(s):
    out = []
    for part in s.split(","):
        pid, _, inv = part.partition(":")
        if pid:
            out.append((pid, inv))
    return tuple(out)


def parse(lines, i, j):
    items = []
    while i < j:
        m = MARK.match(lines[i])
        if m:
            n = int(m.group(2))
            items.append(Stmt(parse_chain(m.group(3)), parse(lines, i + 1, min(j, i + 1 + n))))
            i += 1 + n
        else:
            items.append(Raw(lines[i]))
            i += 1
    return items


def render(items, out=None):
    out = [] if out is None else out
    for it in items:
        if isinstance(it, Raw):
            out.append(it.line)
        elif isinstance(it, Stmt):
            render(it.items, out)
        elif it.call is not None:
            out.extend(it.call)
        else:
            render(it.items, out)
    return out


def common_prefix(chains):
    chains = [c for c in chains if c]
    if not chains:
        return ()
    p = chains[0]
    for c in chains[1:]:
        k = 0
        while k < len(p) and k < len(c) and p[k] == c[k]:
            k += 1
        p = p[:k]
    return p


def group(items, base):
    """Turn runs of statements that share chain[len(base)] into Inv nodes
    (recursively), and do the same inside every statement's nested lines."""
    for it in items:
        if isinstance(it, Stmt):
            inner = [s.chain for s in it.items if isinstance(s, Stmt) and s.chain]
            if not inner:
                continue
            if it.chain and all(c[:len(it.chain)] == it.chain for c in inner):
                sub = it.chain  # same thread: a `for` body
            else:
                sub = common_prefix(inner)[:1]  # a function body, run in a thread of its own
            it.items = group(it.items, sub)
    return group_run(items, base)


def group_run(items, base):
    d = len(base)
    out = []
    i = 0
    while i < len(items):
        it = items[i]
        if isinstance(it, Stmt) and len(it.chain) > d and it.chain[:d] == base:
            key = it.chain[d]
            j = i
            while j < len(items) and isinstance(items[j], Stmt) and items[j].chain[:d + 1] == base + (key,) \
                    and len(items[j].chain) > d:
                j += 1
            out.append(Inv(key, group_run(items[i:j], base + (key,))))
            i = j
        else:
            out.append(it)
            i += 1
    return out


def walk_invs(items, root, out):
    """Collect Inv nodes in document order; returns the tallest height."""
    h = 0
    for it in items:
        if isinstance(it, Stmt):
            h = max(h, walk_invs(it.items, root, out))
        elif isinstance(it, Inv):
            it.root = root
            out.append(it)
            it.height = 1 + walk_invs(it.items, root, out)
            h = max(h, it.height)
    return h


def walk_top(items, top, out):
    """Like walk_invs for the top level: `top` receives the top-level
    statements (Inv nodes are transparent there), and each Inv's root is the
    index of the top-level statement it starts in."""
    h = 0
    for it in items:
        if isinstance(it, Inv) and it.call is None:
            it.root = len(top)
            out.append(it)
            it.height = 1 + walk_top(it.items, top, out)
            h = max(h, it.height)
        else:
            h = max(h, walk_invs([it], len(top), out))
            top.append(it)
    return h


def units(items):
    """The statements of a list at its own level: unfolded Inv nodes are
    transparent (their statements sit at the same level)."""
    out = []
    for it in items:
        if isinstance(it, Inv) and it.call is None:
            out += units(it.items)
        else:
            out.append(it)
    return out


def unit_decls(u):
    if isinstance(u, Raw):  # an unmarked line (e.g. a service local kept by the preamble strip)
        return decl_line(u.line)
    lines = render([u])
    return decl_line(lines[0]) if lines else []


# argument names of common calls, by position
ARG_NAMES = {
    "fromRGB": ("r", "g", "b"), "Color3.new": ("r", "g", "b"), "fromHSV": ("h", "s", "v"),
    "Vector3.new": ("x", "y", "z"), "Vector2.new": ("x", "y"), "fromOffset": ("x", "y"),
    "fromScale": ("x", "y"), "UDim2.new": ("xScale", "xOffset", "yScale", "yOffset"),
    "UDim.new": ("scale", "offset"), "TweenInfo.new": ("duration",), "Instance.new": ("className",),
    "FindFirstChild": ("childName",), "WaitForChild": ("childName",), "FindFirstChildOfClass": ("className",),
    "FindFirstChildWhichIsA": ("className",), "GetService": ("serviceName",), "wait": ("delay",),
    "delay": ("delay",), "GetPropertyChangedSignal": ("property",), "HttpGet": ("url",),
    "HttpGetAsync": ("url",), "Notify": ("options",), "print": ("message",), "warn": ("message",),
}


HELPER_PARAMS = {}  # helper made by this run -> its parameter names


def call_arg_name(toks, i):
    """Name for token i when it is a whole argument of a known call."""
    if i + 1 >= len(toks) or toks[i + 1].text not in (",", ")"):
        return None
    depth, pos, j = 0, 0, i - 1
    while j >= 0:
        x = toks[j].text
        if x in (")", "}", "]"):
            depth += 1
        elif x in ("(", "{", "["):
            if depth == 0:
                break
            depth -= 1
        elif x == "," and depth == 0:
            pos += 1
        elif depth == 0 and x in ("=", "local", "then", "do", "return"):
            return None
        j -= 1
    if j <= 0 or toks[j].text != "(" or toks[j - 1].kind != "name":
        return None
    fn = toks[j - 1].text
    qual = toks[j - 3].text + "." + fn if j >= 3 and toks[j - 2].text == "." else fn
    if fn == "SetAttribute" and pos == 1 and toks[j + 1].text.startswith('"'):
        nm = re.sub(r"\W", "", toks[j + 1].text.strip('"'))
        return lower_first(nm) if nm and not nm[0].isdigit() else None
    names = HELPER_PARAMS.get(fn) or ARG_NAMES.get(qual) or ARG_NAMES.get(fn)
    if names and pos < len(names):
        return names[pos]
    # the only argument of a conversion: `Accent = Color3.fromHex(<hole>)` -> accent
    k = j - 1
    while k >= 2 and toks[k - 1].text in (".", ":") and toks[k - 2].kind == "name":
        k -= 2
    if pos == 0 and toks[i + 1].text == ")" and k >= 2 and toks[k - 1].text == "=" \
            and toks[k - 2].role in ("key", "field"):
        return lower_first(toks[k - 2].text)
    return None


def lower_first(s):
    """TextButton -> textButton, UIStroke -> uiStroke, HTTPGet -> httpGet"""
    m = re.match(r"[A-Z][A-Z0-9]*(?=[A-Z][a-z])|[A-Z][A-Z0-9]*$|[A-Z]", s)
    return s[:m.end()].lower() + s[m.end():] if m else s


def dedent(lines):
    pad = re.match(r"\t*", lines[0]).group(0) if lines else ""
    return pad, "\n".join(l[len(pad):] if l.startswith(pad) else l.lstrip("\t") for l in lines)


# ---------------------------------------------------------------------------
# folding
# ---------------------------------------------------------------------------
class Group:
    """One occurrence of a repeated shape: its text, tokens and statements."""

    def __init__(self, lines, stmts):
        self.pad, self.text = dedent(lines)
        self.toks = tokenize(self.text)
        self.skel = skeleton(self.toks)
        self.stmts = stmts  # statement-level units (for its own declarations)

    @classmethod
    def from_units(cls, parts, stmts, exact):
        """The same group from per-statement (pad, text, toks, skel) already
        tokenized by fold_loops (re-tokenizing every candidate run was most of
        the time on big traces). Token offsets are only right when `exact`
        (the group whose text gets substituted); the others share the cached
        tokens. None when the statements are not at one indentation."""
        pad = parts[0][0]
        if any(p[0] != pad for p in parts):
            return None
        g = cls.__new__(cls)
        g.pad, g.text, g.stmts = pad, "\n".join(p[1] for p in parts), stmts
        g.skel = "\1".join(p[3] for p in parts)
        if exact:
            toks, off = [], 0
            for p in parts:
                for t in p[2]:
                    c = Tok(t.kind, t.text, t.start + off, t.end + off)
                    c.role = t.role
                    toks.append(c)
                off += len(p[1]) + 1
            g.toks = toks
        else:
            g.toks = [t for p in parts for t in p[2]]
        return g


class Folder:
    def __init__(self, root_items):
        self.root = root_items
        toks = tokenize("\n".join(render(root_items)))
        self.counts = var_counts(toks)
        self.all_declared = declared(toks)
        self.taken = {t.text for t in toks if t.kind == "name"} | RESERVED
        # local -> class of the instance it holds (`local X = Instance.new("Frame")`)
        self.cls = dict(re.findall(r'^\t*local (\w+) = Instance\.new\("(\w+)"', "\n".join(render(root_items)),
                                   re.M))
        self.top, self.invs = [], []  # top-level statements; all Inv nodes
        walk_top(root_items, self.top, self.invs)
        self.top_index = {}  # local declared at top level -> index of its top-level statement
        for i, u in enumerate(self.top):
            for nm in unit_decls(u):
                self.top_index.setdefault(nm, i)
        # id(top-level statement) -> helper definitions [(creation number, lines)]
        self.defs = {}
        self.n_helpers = 0
        self.n_calls = 0
        self.n_loops = 0
        self.renames = {}  # local -> new name (applied to the whole output)

    def fresh(self, base):
        base = re.sub(r"\W", "", base) or "helper"
        if base[0].isdigit():
            base = "v" + base
        n, name = 1, base
        while name in self.taken:
            n += 1
            name = "%s%d" % (base, n)
        self.taken.add(name)
        return name

    def visible(self, name, root_index):
        """Can a helper defined before top-level item root_index read `name`?"""
        if name not in self.all_declared:
            return True  # a global
        i = self.top_index.get(name)
        return i is not None and i < root_index

    # -- matching ------------------------------------------------------------
    def match(self, groups, visible):
        """Compare occurrences of one shape. Returns (holes, params, fwd):
        holes: token index -> values tuple (one value per occurrence),
        params: distinct values tuples in order of first appearance,
        fwd[j]: occurrence j's own local names -> the first occurrence's.
        None when the occurrences cannot share one body."""
        rep = groups[0]
        k = len(groups)
        decls = [declared(g.toks) for g in groups]
        fwd = [dict() for _ in groups]
        holes = {}
        for i, t0 in enumerate(rep.toks):
            if not t0.hole:
                continue
            vals = tuple(g.toks[i].text for g in groups)
            if t0.kind == "name":
                internal = [vals[j] in decls[j] for j in range(k)]
                if all(internal):
                    for j in range(k):
                        if fwd[j].setdefault(vals[j], vals[0]) != vals[0]:
                            return None
                    continue
                if any(internal):
                    return None
                if all(v == vals[0] for v in vals) and visible(vals[0]):
                    continue
                holes[i] = vals
            elif any(v != vals[0] for v in vals):
                holes[i] = vals
        for j in range(k):
            if len(set(fwd[j].values())) != len(fwd[j]):
                return None
        params, seen = [], set()
        for i in sorted(holes):
            if holes[i] not in seen:
                seen.add(holes[i])
                params.append(holes[i])
        if len(params) > MAX_PARAMS:
            return None
        return holes, params, fwd

    def escaping(self, g):
        """Locals the group declares at its own level that are used outside it."""
        own = var_counts(g.toks)
        return [nm for u in g.stmts for nm in unit_decls(u) if self.counts[nm] - own[nm] > 0]

    def param_names(self, rep, holes, params, extra_used=()):
        used = {t.text for t in rep.toks if t.kind == "name"} | RESERVED | set(extra_used)
        names = []
        for vals in params:
            i = min(ix for ix, v in holes.items() if v == vals)
            base = self.param_base(rep.toks, i)
            t = rep.toks
            # different instances in different calls: name it after their class
            classes = {self.cls.get(v) for v in vals}
            if t[i].kind == "name" and len(set(vals)) > 1 and len(classes) == 1 and None not in classes \
                    and base == self.param_base_of_name(t[i].text):
                base = lower_first(classes.pop())
            if base in used and i >= 4 and t[i - 1].text == "=" and t[i - 3].text == "." \
                    and t[i - 4].kind == "name" and i - 4 not in holes:
                obj = lower_first(re.sub(r"\d+$", "", t[i - 4].text))
                base = obj + base[:1].upper() + base[1:]
            nm, n = base, 1
            while nm in used:
                n += 1
                nm = "%s%d" % (base, n)
            used.add(nm)
            names.append(nm)
        return names

    @staticmethod
    def param_base_of_name(name):
        return lower_first(re.sub(r"\d+$", "", name)) or "value"

    @staticmethod
    def param_base(toks, i):
        t = toks[i]
        prev = toks[max(0, i - 3):i]
        if len(prev) == 3 and prev[2].text == "=" and prev[1].role == "field" and prev[0].text == ".":
            base = lower_first(prev[1].text)  # X.Prop = <hole>
        elif len(prev) >= 2 and prev[-1].text == "=" and prev[-2].role == "key":
            base = lower_first(prev[-2].text)  # { Key = <hole> }
        elif call_arg_name(toks, i):
            base = call_arg_name(toks, i)
        elif t.kind == "name":
            base = lower_first(re.sub(r"\d+$", "", t.text)) or "value"
        elif t.text.startswith('"'):
            base = "text"
        else:
            base = "value"
        base = re.sub(r"\W", "", base) or "value"
        if base in RESERVED or base[0].isdigit():
            base = "value"
        return base

    @staticmethod
    def substitute(rep, holes, params, names):
        index = {vals: n for vals, n in zip(params, names)}
        text = rep.text
        for i in sorted(holes, reverse=True):
            t = rep.toks[i]
            text = text[:t.start] + index[holes[i]] + text[t.end:]
        return text

    def account(self, removed, added):
        # in place: `-=`/`+=` rebuild the whole Counter (slow on big traces);
        # counts never go below zero here, and only `> 0` is ever asked
        for toks in removed:
            self.counts.subtract(var_counts(toks))
        for text in added:
            self.counts.update(var_counts(tokenize(text)))

    # -- helpers -------------------------------------------------------------
    def fold_helpers(self):
        invs = self.invs
        for h in sorted({n.height for n in invs}):
            by_pid = {}
            for n in invs:
                if n.height == h:
                    by_pid.setdefault(n.key[0], []).append(n)
            for nodes in by_pid.values():
                # the same invocation split into several runs: leave it alone
                keys = Counter(n.key for n in nodes)
                nodes = [n for n in nodes if keys[n.key] == 1 and n.call is None]
                shapes = {}
                for n in nodes:
                    lines = render(n.items)
                    if len(lines) < 2:
                        continue  # one-line bodies read better inline
                    g = Group(lines, units(n.items))
                    g.node = n
                    shapes.setdefault(g.skel, []).append(g)
                for groups in shapes.values():
                    if len(groups) >= 2:
                        self.fold_helper(groups)

    def fold_helper(self, groups):
        first_root = min(g.node.root for g in groups)
        m = self.match(groups, lambda nm: self.visible(nm, first_root))
        if not m:
            return
        holes, params, fwd = m
        rep = groups[0]
        rep_top = [nm for u in rep.stmts for nm in unit_decls(u)]
        rets = []
        for j, g in enumerate(groups):
            for nm in self.escaping(g):
                r = fwd[j].get(nm)
                if r is None or r not in rep_top:
                    return
                if r not in rets:
                    rets.append(r)
        names = self.param_names(rep, holes, params)
        lead = names[params.index(holes[0])] if 0 in holes else None
        name = self.fresh(self.helper_base(rep.toks, holes, rets, lead,
                                           lambda i: names[params.index(holes[i])] if i in holes else None))
        body = ["\t" + l if l else l for l in self.substitute(rep, holes, params, names).split("\n")]
        if rets:
            body.append("\treturn " + ", ".join(rets))
        lines = ["local function %s(%s)" % (name, ", ".join(names))] + body + ["end"]
        HELPER_PARAMS[name] = names
        self.defs.setdefault(id(self.top[first_root]), []).append((self.n_helpers, lines))
        calls = []
        for j, g in enumerate(groups):
            args = [vals[j] for vals in params]
            back = {v: kk for kk, v in fwd[j].items()}
            call = "%s(%s)" % (name, ", ".join(args))
            if rets:
                call = "local %s = %s" % (", ".join(back[r] for r in rets), call)
            g.node.call = [g.pad + call]
            g.node.rec = (name, args, rets)
            calls.append(call)
        self.account([g.toks for g in groups], calls + ["\n".join(body)])
        self.n_helpers += 1
        self.n_calls += len(groups)

    @staticmethod
    def helper_base(toks, holes, rets=(), lead=None, lead_of=None):
        """A name from what the body does: setupX (it styles a parameter
        first), createX (the first instance's fixed Name, or the class it
        makes most), getX (what it returns), onX (it connects to X)."""
        def cap(x):
            x = re.sub(r"\d+$", "", x)
            return x[:1].upper() + x[1:]
        if lead and len(toks) > 3 and toks[1].text in (".", ":"):
            return "setup" + cap(lead)
        classes = []
        for i in range(len(toks) - 4):
            if toks[i].text == "Instance" and toks[i + 1].text == "." and toks[i + 2].text == "new" \
                    and toks[i + 4].text.startswith('"'):
                classes.append(toks[i + 4].text.strip('"'))
        if classes:
            for i in range(len(toks) - 4):
                if toks[i + 1].text == "." and toks[i + 2].text == "Name" and toks[i + 3].text == "=":
                    if i + 4 not in holes and toks[i + 4].text.startswith('"'):
                        nm = re.sub(r"\W", "", toks[i + 4].text.strip('"'))
                        if nm and not nm[0].isdigit():
                            return "create" + nm[0].upper() + nm[1:]
                    break
            best, n = Counter(classes).most_common(1)[0]
            return "create" + (best if n > 1 else classes[0])
        for i in range(1, len(toks) - 2):
            if toks[i + 1].text == ":" and toks[i + 2].text == "Create" and i + 4 < len(toks) \
                    and toks[i + 3].text == "(" and toks[i + 4].kind == "name":
                target = lead_of(i + 4) if lead_of else None
                return "tween" + cap(target or toks[i + 4].text)
            if toks[i].text == ":" and toks[i + 1].text in ("Connect", "Once") and toks[i - 1].kind == "name":
                return "on" + cap(toks[i - 1].text)
        if rets:
            return "get" + cap(rets[-1])
        for i in range(len(toks) - 3):
            if toks[i].kind == "name" and toks[i + 1].text == ":" and toks[i + 2].text == "Destroy":
                return "destroy" + cap(toks[i].text)
        if len(toks) > 4 and toks[0].kind == "name" and toks[1].text == "." and toks[3].text == "=" \
                and 0 not in holes:
            return "set" + cap(toks[0].text) + toks[2].text
        return "helper"

    # -- loops ---------------------------------------------------------------
    def fold_loops(self, items):
        """Fold repeated consecutive statement groups in this list (and in all
        nested ones). Returns the new list; unfolded Inv nodes are flattened."""
        for it in items:
            if isinstance(it, Stmt):
                it.items = self.fold_loops(it.items)
            elif isinstance(it, Inv) and it.call is None:
                it.items = self.fold_loops(it.items)
        flat = units(items)
        # shape ids (statements that cannot be part of a loop get unique negative ids)
        ids, size, shapes = [], [], {}
        parts = []  # per statement: (pad, dedented text, tokens, skeleton)
        for x, u in enumerate(flat):
            lines = [] if isinstance(u, Raw) else render([u])
            size.append(len(lines))
            if not lines:
                ids.append(-1 - x)
                parts.append(None)
                continue
            pad, text = dedent(lines)
            toks = tokenize(text)
            sk = skeleton(toks)
            parts.append((pad, text, toks, sk))
            ids.append(shapes.setdefault(sk, len(shapes)))
        n = len(flat)
        where = {}  # shape id -> positions, ascending
        for x, s in enumerate(ids):
            where.setdefault(s, []).append(x)
        banned = {}  # period -> first position where it may be tried again
        out = []
        i = 0
        while i < n:
            best = None
            if ids[i] >= 0:
                pos = where[ids[i]]
                for j in pos[bisect.bisect_right(pos, i):]:
                    L = j - i
                    if L > MAX_PERIOD or i + 2 * L > n:
                        break
                    if banned.get(L, 0) > i or ids[i:i + L] != ids[j:j + L] or min(ids[i:i + L]) < 0:
                        continue
                    r = 2
                    while i + (r + 1) * L <= n and ids[i + r * L:i + (r + 1) * L] == ids[i:i + L]:
                        r += 1
                    if r < 3 and sum(size[i:i + L]) < 8:
                        continue
                    score = (L * r, -L)
                    if best is None or score > best[2]:
                        best = (L, r, score)
            if best:
                L, r, _ = best
                loop = self.make_loop([flat[i + k * L:i + (k + 1) * L] for k in range(r)],
                                      [parts[i + k * L:i + (k + 1) * L] for k in range(r)])
                if loop is not None and len(loop.call) + 2 >= sum(size[i:i + L * r]):
                    loop = None  # not clearly shorter
                if loop is not None:
                    self.account([tokenize("\n".join(render(flat[i:i + L * r])))], ["\n".join(loop.call)])
                    self.n_loops += 1
                    out.append(loop)
                    i += L * r
                    continue
                banned[L] = i + L * r
            out.append(flat[i])
            i += 1
        return out

    def make_loop(self, reps, parts=None):
        groups = None
        if parts is not None:
            groups = [Group.from_units(p, stmts, k == 0) for k, (p, stmts) in enumerate(zip(parts, reps))]
            if any(g is None for g in groups):
                groups = None
        if groups is None:
            groups = [Group(render(stmts), stmts) for stmts in reps]
        if len({g.skel for g in groups}) != 1:
            return None
        m = self.match(groups, lambda nm: True)
        if not m:
            return None
        holes, params, fwd = m
        if not params:
            return None  # the very same statements again: not a data-driven loop
        k = len(groups)
        decls0 = declared(groups[0].toks)
        # a value carried over from the previous iteration: group j reads a
        # local that group j-1 made (the trace's view of some "last/selected"
        # state variable in the original)
        carried = {}  # values tuple -> the first group's local it stands for
        for vals in params:
            if all(groups[0].toks[i].kind == "name" for i, v in holes.items() if v == vals):
                r = fwd[0].get(vals[1]) if k > 1 else None
                if r and vals[0] not in decls0 and all(fwd[j - 1].get(vals[j]) == r for j in range(1, k)):
                    carried[vals] = r
        carried_names = [{kk for kk, v in fwd[j].items() if v in carried.values()} for j in range(k)]
        tail = []  # the last group's carried locals that are read after the loop
        for j, g in enumerate(groups):
            nxt = var_counts(groups[j + 1].toks) if j + 1 < k else Counter()
            own = var_counts(g.toks)
            for nm in self.escaping(g):
                if nm not in carried_names[j]:
                    return None
                if j + 1 < k and self.counts[nm] - own[nm] - nxt[nm] > 0:
                    return None
                if j + 1 == k:
                    tail.append(nm)
        rep = groups[0]
        pad = rep.pad
        taken = {t.text for g in groups for t in g.toks if t.kind == "name"}
        fields = [vals for vals in params if vals not in carried]
        names = self.param_names(rep, holes, fields, taken | self.taken)
        state = {}  # rep local -> (outer "last" variable, per-iteration "previous" copy)
        for r in carried.values():
            if r not in state:
                base = re.sub(r"\d+$", "", r) or "value"
                base = base[0].upper() + base[1:]
                state[r] = (self.fresh("last" + base), self.fresh("previous" + base))
        subst = {vals: state[carried[vals]][1] for vals in carried}
        if len(fields) == 0:
            var = None
            head = pad + "for _ = 1, %d do" % k
        elif len(fields) == 1:
            var = names[0]
            subst[fields[0]] = var
        else:
            var = next(v for v in ("v", "item", "entry", "row") + tuple("v%d" % x for x in range(2, 99))
                       if v not in taken and v not in RESERVED and v not in self.taken)
            for vals, nm in zip(fields, names):
                subst[vals] = "%s.%s" % (var, nm)
        body = self.substitute(rep, holes, list(subst), list(subst.values()))
        if len(fields) == 1:
            rows, cur = [], ""
            for j in range(k):
                v = fields[0][j] + ","
                if cur and len(pad) * 4 + 4 + len(cur) + 1 + len(v) > 100:
                    rows.append(cur)
                    cur = ""
                cur = cur + " " + v if cur else v
            rows.append(cur)
        else:
            rows = ["{ " + ", ".join("%s = %s" % (nm, vals[j]) for nm, vals in zip(names, fields)) + " }"
                    for j in range(k)]
        lines = []
        for vals, r in carried.items():
            if all(state[r][0] + " =" not in l for l in lines):
                lines.append(pad + "local %s = %s" % (state[r][0], vals[0]))
        if var is None:
            lines.append(head)
        else:
            lines += [pad + "for _, %s in ipairs({" % var]
            lines += [pad + "\t" + (row if len(fields) == 1 else row + ",") for row in rows]
            lines += [pad + "}) do"]
        lines += [pad + "\tlocal %s = %s" % (prev, last) for last, prev in state.values()]
        lines += [pad + "\t" + l if l else l for l in body.split("\n")]
        lines += [pad + "\t%s = %s" % (state[r][0], r) for r in state]
        lines += [pad + "end"]
        # the last group's carried locals keep being read after the loop
        for nm in tail:
            self.renames[nm] = state[fwd[k - 1][nm]][0]
        loop = Inv(("loop", ""), [])
        loop.call = lines
        # helper definitions anchored inside the folded statements move to the loop
        moved = []
        for stmts in reps:
            for u in stmts:
                moved += self.take_defs(u)
        if moved:
            self.defs[id(loop)] = moved
        return loop

    def take_defs(self, it):
        """Helper definitions anchored on `it` or on a statement folded into it."""
        out = self.defs.pop(id(it), [])
        if isinstance(it, Inv):
            for sub in it.items:
                out += self.take_defs(sub)
        return out

    # ------------------------------------------------------------------------
    def output(self):
        out = []
        for it in units(self.root):
            # in creation order: a helper that calls another one comes after it
            for _, d in sorted(self.take_defs(it), key=lambda x: x[0]):
                out.extend(d)
            render([it], out)
        if self.defs:  # should not happen: keep the code usable and say so
            lost = sorted((d for ds in self.defs.values() for d in ds), key=lambda x: x[0])
            print("[!] fold.py: %d helper definition(s) lost their place; put at the top" % len(lost),
                  file=sys.stderr)
            out = [l for _, d in lost for l in d] + out
        if self.renames:
            pat = re.compile(r"(?<![\w.:])(%s)\b" % "|".join(map(re.escape, self.renames)))
            out = [pat.sub(lambda m: self.renames[m.group(1)], l) for l in out]
        return out


def fold(body, stats=None):
    """Fold helper invocations and loops in a marked trace body; returns it
    without markers."""
    lines = body.split("\n")
    if not any(MARK.match(l) for l in lines):
        return body
    items = parse(lines, 0, len(lines))
    items = group(items, common_prefix([s.chain for s in items if isinstance(s, Stmt)]))
    HELPER_PARAMS.clear()
    f = Folder(items)
    f.fold_helpers()
    f.root = f.fold_loops(f.root)
    if stats is not None:
        stats.update(helpers=f.n_helpers, calls=f.n_calls, loops=f.n_loops)
    return "\n".join(f.output())


def strip_markers(text):
    return "\n".join(l for l in text.split("\n") if not MARK.match(l))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input")
    ap.add_argument("-o", "--output")
    a = ap.parse_args()
    with open(a.input, encoding="utf-8") as fh:
        text = fh.read()
    header, sep, body = text.partition("\n\n")
    stats = {}
    out = header + sep + fold(body, stats)
    with open(a.output or a.input, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(out)
    print("folded: %(helpers)d helpers (%(calls)d calls), %(loops)d loops" % stats)


if __name__ == "__main__":
    main()
