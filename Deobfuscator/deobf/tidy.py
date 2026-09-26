"""Readability pass over the rendered trace (runs after tracing, never affects it).

    python tidy.py file.deobf.luau [-o out.luau]

Steps (each one is conservative: when unsure it leaves the text alone):
  * strip_preamble   - drop Luraph's own environment/anti-tamper probes at the top
                       (Path2D maths, ChildRemoved/DescendantRemoving hooks, Folder
                       WaitForChild checks); they are not part of the original script
  * name_instances   - `local Frame3 = Instance.new("Frame")` + `Frame3.Name = "Panel"`
                       -> `local Panel = ...`; loadstring'd libraries get the repo name
  * fold (fold.py)   - repeated calls of one script function -> `local function` helpers,
                       unrolled repetitions -> `for _, v in ipairs({...})` loops; needs the
                       runtime's statement markers (removed here either way)
  * hoist_repeats    - repeated pure sub-expressions (the symbolic value of an unknown
                       argument pushed through the same clamp several times) become locals
  * trim_params      - `function(arg, arg2)` params the body never reads are dropped
  * unwrap_parens    - `f((a * b))` -> `f(a * b)`
"""
import argparse
import bisect
import re
import sys

import fold

KEYWORDS = {"and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in",
            "local", "nil", "not", "or", "repeat", "return", "then", "true", "until", "while", "continue"}
# globals a new local must never shadow
RESERVED = KEYWORDS | {
    "game", "workspace", "script", "Instance", "Enum", "Vector2", "Vector3", "CFrame", "Color3", "UDim",
    "UDim2", "Font", "TweenInfo", "Ray", "Region3", "Rect", "BrickColor", "NumberRange", "NumberSequence",
    "ColorSequence", "NumberSequenceKeypoint", "ColorSequenceKeypoint", "PhysicalProperties", "Random",
    "Axes", "Faces", "RaycastParams", "OverlapParams", "DateTime", "task", "math", "string", "table",
    "coroutine", "os", "debug", "utf8", "bit32", "buffer", "print", "warn", "error", "type", "typeof",
    "pairs", "ipairs", "next", "select", "pcall", "xpcall", "tostring", "tonumber", "require", "wait",
    "spawn", "delay", "tick", "time", "settings", "shared", "_G", "getgenv", "gethui", "loadstring",
    "setmetatable", "getmetatable", "rawget", "rawset", "rawequal", "unpack", "assert", "self",
}

# strings, comments, identifiers (in that priority)
TOKEN = re.compile(r'"(?:[^"\\\n]|\\.)*"|--\[(=*)\[.*?\]\1\]|--[^\n]*|[A-Za-z_]\w*', re.S)


def indent(line):
    return len(line) - len(line.lstrip("\t"))


def identifiers(text):
    """All identifier tokens that are not field names (`.x`, `:x`)."""
    out = set()
    for m in TOKEN.finditer(text):
        t = m.group(0)
        if t[0] in '"-':
            continue
        i = m.start() - 1
        while i >= 0 and text[i] in " \t":
            i -= 1
        if i >= 0 and text[i] in ".:" and not (text[i] == "." and i > 0 and text[i - 1] == "."):
            continue
        out.add(t)
    return out


def rename(text, mapping):
    """Rename variables (identifier tokens that are not field names) outside strings/comments."""
    if not mapping:
        return text

    def sub(m):
        t = m.group(0)
        if t[0] in '"-' or t not in mapping:
            return t
        i = m.start() - 1
        while i >= 0 and text[i] in " \t":
            i -= 1
        if i >= 0 and text[i] in ".:" and not (text[i] == "." and i > 0 and text[i - 1] == "."):
            return t
        # table constructor key `{ Frame3 = 1 }` is not a variable
        j = m.end()
        while j < len(text) and text[j] in " \t":
            j += 1
        # (a multi-line constructor has the key at a line start: look back over newlines too)
        k = i
        while k >= 0 and text[k] in " \t\r\n":
            k -= 1
        if text.startswith("=", j) and not text.startswith("==", j) and k >= 0 and text[k] in "{,":
            # ... but not the last name of `local a, b = ...`
            ls = text.rfind("\n", 0, m.start()) + 1
            if not re.fullmatch(r"\t*local [\w, ]*", text[ls:m.start()]):
                return t
        return mapping[t]

    return TOKEN.sub(sub, text)


class Namer:
    def __init__(self, text):
        self.taken = identifiers(text) | RESERVED
        self.made = set()
        self.next = {}  # base -> first suffix worth trying (thousands of equal bases were quadratic)

    def fresh(self, base):
        base = re.sub(r"\W", "", base)
        if not base or base[0].isdigit():
            return None
        n = self.next.get(base, 1)
        name = base if n == 1 else "%s%d" % (base, n)
        while name in self.taken:
            n += 1
            name = "%s%d" % (base, n)
        self.next[base] = n
        self.taken.add(name)
        self.made.add(name)
        return name


# ---------------------------------------------------------------------------
# Luraph preamble
# ---------------------------------------------------------------------------
PRE_SINGLE = [
    r'local ScreenGui = Instance\.new\("ScreenGui"\)',
    r'local Frame = Instance\.new\("Frame"\)',
    r'Frame\.(Position|Size) = UDim2\.new\([^)]*\)',
    r'Frame\.Parent = ScreenGui',
    r'local Path2D = Instance\.new\("Path2D"\)',
    r'Path2D[.:].*',
    r'ScreenGui:Destroy\(\)',
    r'connection\d*:Disconnect\(\)',
    r'local Folder\d* = Instance\.new\("Folder"(, Folder\d*)?\)',
    r'Folder\d*:(GetChildren|Destroy)\(\)',
    r'Folder\d*\.Name = "\d+"',
    r'Folder\d*:WaitForChild\("\d+"\)',
]
PRE_SINGLE = [re.compile(p + "$") for p in PRE_SINGLE]
PRE_CONNECT = re.compile(r"local connection\d* = [\w.]+\.(ChildRemoved|DescendantRemoving|ChildAdded|"
                         r"DescendantAdded|AncestryChanged|Changed|Destroying):Connect\(function\(\w*\)$")
PRE_SPAWN = re.compile(r"task\.(spawn|defer)\(function\(\.\.\.\)$|task\.delay\([\d.]+, function\(\.\.\.\)$")
GETSERVICE = re.compile(r'local (\w+) = game:GetService\("\w+"\)$')


def statements(lines, start=0):
    """Split top-level lines into (first, last) statement ranges."""
    i = start
    while i < len(lines):
        j = i + 1
        while j < len(lines) and (indent(lines[j]) > 0 or re.match(r"(end|\}|\))", lines[j])):
            j += 1
        yield i, j
        i = j


def strip_preamble(text):
    """Works on output with or without fold.py's statement markers."""
    lines = text.split("\n")
    marked = [bool(fold.MARK.match(l)) for l in lines]
    idx = [i for i, m in enumerate(marked) if not m]
    plan = preamble_plan([lines[i] for i in idx])
    if plan is None:
        return text
    head, end, middle = plan

    def orig(ci):  # first original line of the statement at clean line ci (its marker)
        if ci >= len(idx):
            return len(lines)
        o = idx[ci]
        while o > 0 and marked[o - 1]:
            o -= 1
        return o
    return "\n".join(lines[:orig(head)] + middle + lines[orig(end):])


def preamble_plan(lines):
    """(first line, end line, replacement lines) for the preamble, or None."""
    head = 0
    while head < len(lines) and (lines[head].startswith("--") or not lines[head].strip()):
        head += 1
    if not any('Instance.new("Path2D")' in l for l in lines[head:head + 60]):
        return None
    drop, keep_services = [], []
    end = head
    for a, b in statements(lines, head):
        first = lines[a]
        body = [l.strip() for l in lines[a + 1:b]]
        inner = [l for l in body[:-1] if not l.startswith("-- [envlog]")]
        if b - a == 1 and (any(p.match(first) for p in PRE_SINGLE) or first.startswith("--")):
            ok = True
        elif b - a == 1 and GETSERVICE.match(first):
            keep_services.append(a)
            ok = True
        elif (PRE_CONNECT.match(first) or PRE_SPAWN.match(first)) and not inner and body and body[-1] == "end)":
            ok = True
        else:
            ok = False
        if not ok:
            break
        drop.append((a, b))
        end = b
    if end == head or not any("Path2D" in lines[i] for a, b in drop for i in range(a, b)):
        return None
    rest = "\n".join(lines[end:])
    kept = []
    for a in keep_services:
        m = GETSERVICE.match(lines[a])
        if re.search(r"\b%s\b" % m.group(1), rest):
            kept.append(lines[a])
    removed = sum(b - a for a, b in drop) - len(kept)
    note = ["removed at so its gonna be shit osrry!"]
    comments = [lines[i] for a, b in drop for i in range(a, b) if lines[i].startswith("-- ")
                and not lines[i].startswith("-- [envlog]")]
    return head, end, comments + note + kept


# ---------------------------------------------------------------------------
# naming
# ---------------------------------------------------------------------------
NAME_SET = re.compile(r'^\t*(\w+)\.Name = "([^"\n]{1,40})"$', re.M)
NEW_INST = re.compile(r'^\t*local (\w+) = Instance\.new\("(\w+)"(?:, [^)]*)?\)$', re.M)
UI_OBJ = re.compile(r'^\t*local (\w+) = [\w.]+:(\w+)\(\{(?:\n\t*| )Title = "([^"\n]+)"', re.M)
LOADLIB = re.compile(r'^\t*local (result\d*) = loadstring\((\w+)\)\(\)$', re.M)
SKIP_URL_PARTS = {"raw", "refs", "heads", "main", "master", "releases", "latest", "download", "blob",
                  "source", "src", "dist", "lua", "luau", "txt", "init", "loader", "script", "api"}


def lib_name(url):
    parts = [p for p in re.split(r"[/?#]", url.split("://", 1)[-1]) if p]
    host, path = (parts[0], parts[1:]) if parts else ("", [])
    cands = []
    if "github" in host and len(path) >= 2:
        cands.append(path[1])  # repo
    cands += [re.sub(r"\.(lua|luau|txt)$", "", p) for p in reversed(path)]
    for c in cands:
        c = re.sub(r"\W", "", c)
        if c and not c[0].isdigit() and c.lower() not in SKIP_URL_PARTS:
            return c
    return None


def name_instances(text):
    namer = Namer(text)
    mapping = {}
    # every `x.Name = "..."` once (searching the rest of the text per instance was quadratic)
    names = {}
    for nm in NAME_SET.finditer(text):
        names.setdefault(nm.group(1), []).append((nm.start(), nm.group(2)))
    for m in NEW_INST.finditer(text):
        var, cls = m.group(1), m.group(2)
        if not re.fullmatch(re.escape(cls) + r"\d*", var):
            continue  # already named from context
        sets = names.get(var, [])
        k = bisect.bisect_left(sets, (m.end(), ""))
        if k == len(sets):
            continue
        base = re.sub(r"\W", "", sets[k][1])
        if not base or base[0].isdigit() or base in RESERVED:
            continue
        new = namer.fresh(base)
        if new:
            mapping[var] = new
    # UI library objects: `local Tab3 = Window:Tab({ Title = "Auto Farm" ...` -> AutoFarmTab
    for m in UI_OBJ.finditer(text):
        var, kind, title = m.group(1), m.group(2), m.group(3)
        if not re.fullmatch(re.escape(kind) + r"\d*", var):
            continue
        words = re.findall(r"[A-Za-z0-9]+", title)[:4]
        base = "".join(w[0].upper() + w[1:] for w in words)
        if base and not base.endswith(kind):
            base += kind
        if base and not base[0].isdigit():
            new = namer.fresh(base)
            if new:
                mapping[var] = new
    for m in LOADLIB.finditer(text):
        url = re.search(r'^\t*local %s = game:HttpGet(?:Async)?\("([^"]+)"' % re.escape(m.group(2)), text, re.M)
        base = url and lib_name(url.group(1))
        if base:
            new = namer.fresh(base)
            if new:
                mapping[m.group(1)] = new
    return rename(text, mapping)


# ---------------------------------------------------------------------------
# repeated pure expressions
# ---------------------------------------------------------------------------
PURE_NAMES = {"math", "clamp", "floor", "ceil", "max", "min", "abs", "round", "sqrt", "sign", "huge",
              "tonumber", "tostring", "string", "format", "sub", "len", "lower", "upper", "rep",
              "and", "or", "not"}
CALL_START = re.compile(r"(?<![\w.:])(math\.\w+|tonumber|tostring|string\.\w+)\(")


def balanced(s, i):
    """s[i] == '(' -> index after the matching ')' (strings skipped), or -1."""
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == '"':
            m = re.compile(r'"(?:[^"\\\n]|\\.)*"').match(s, j)
            if not m:
                return -1
            j = m.end()
            continue
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return j + 1
        elif c == "\n":
            return -1
        j += 1
    return -1


def pure(expr):
    if '"' in expr:
        return False
    names = set(re.findall(r"[A-Za-z_]\w*", expr))
    free = {n for n in names if n not in PURE_NAMES}
    # must depend on something unknown (else it is a constant the trace would have folded)
    return bool(free) and all(re.fullmatch(r"(arg|value)\d*|[a-z]\w*", n) for n in free) \
        and not re.search(r"[:\[{]", expr)


STMT_START = re.compile(r"\t*(local \w+ = |[\w.\[\]\"]+ = |[\w.]+[:.]\w+\()")


def hoist_repeats(text, min_len=36, min_count=3):
    namer = Namer(text)
    for _ in range(2000):
        cands = {}
        for m in CALL_START.finditer(text):
            e = balanced(text, m.end() - 1)
            if e > 0:
                expr = text[m.start():e]
                if len(expr) >= min_len and pure(expr):
                    cands.setdefault(expr, 0)
                    cands[expr] += 1
        done = False
        for expr in sorted((c for c, n in cands.items() if n >= min_count), key=len, reverse=True):
            lines = text.split("\n")
            first = next(i for i, l in enumerate(lines) if expr in l)
            base = indent(lines[first])
            if not STMT_START.match(lines[first]) or lines[first].rstrip().endswith((",", "{")):
                continue
            # the local is only visible until the enclosing block closes
            last = first
            for j in range(first + 1, len(lines)):
                l = lines[j]
                if l.strip() and indent(l) < base:
                    break
                if expr in l:
                    last = j
            outside = sum(l.count(expr) for l in lines[:first] + lines[last + 1:])
            inside = sum(l.count(expr) for l in lines[first:last + 1])
            if inside < min_count or outside:
                continue
            name = namer.fresh("value")
            for j in range(first, last + 1):
                lines[j] = lines[j].replace(expr, name)
            lines.insert(first, "\t" * base + "local %s = %s" % (name, expr))
            text = "\n".join(lines)
            done = True
            break
        if not done:
            break
    # a hoisted value that ended up used only once goes back inline
    # (hoisted expressions are single calls, so no parentheses are needed)
    for _ in range(len(namer.made) + 1):
        changed = False
        for name in list(namer.made):
            m = re.search(r"^\t*local %s = (.*)\n" % name, text, re.M)
            if not m:
                continue
            rest = text[:m.start()] + text[m.end():]
            uses = [u for u in re.finditer(r"(?<![\w.:])%s\b" % name, rest)]
            if len(uses) == 1:
                u = uses[0]
                text = rest[:u.start()] + m.group(1) + rest[u.end():]
                namer.made.discard(name)
                changed = True
        if not changed:
            break
    # number the new locals in order of appearance
    order = [v for v in re.findall(r"\blocal (value\d*) = ", text) if v in namer.made]
    text = rename(text, {v: "__hoisted_%d__" % n for n, v in enumerate(order)})
    fresh = Namer(text)
    final = {"__hoisted_%d__" % n: fresh.fresh("value") for n in range(len(order))}
    return rename(text, final)


# ---------------------------------------------------------------------------
# parameters and parentheses
# ---------------------------------------------------------------------------
FUNC_HDR = re.compile(r"function\(([^()]*)\)$")


def trim_params(text):
    lines = text.split("\n")
    for i, line in enumerate(lines):
        m = FUNC_HDR.search(line)
        if not m or not m.group(1):
            continue
        base = indent(line)
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or indent(lines[j]) > base):
            j += 1
        body = "\n".join(lines[i + 1:j])
        used = identifiers(body)
        params = [p.strip() for p in m.group(1).split(",")]
        generic = lambda p: p == "..." or re.fullmatch(r"(arg|state)\d*", p)
        is_used = lambda p: ("..." in re.sub(r'"(?:[^"\\\n]|\\.)*"', "", body)) if p == "..." else p in used
        while params and generic(params[-1]) and not is_used(params[-1]):
            params.pop()
        params = ["_" if generic(p) and p != "..." and not is_used(p) else p for p in params]
        lines[i] = line[:m.start(1)] + ", ".join(params) + line[m.end(1):]
    return "\n".join(lines)


def unwrap_parens(text):
    out, i = [], 0
    for m in re.finditer(r"(?<=[\w\]\)])\(\(", text):
        if m.start() < i:
            continue
        outer_end = balanced(text, m.start())
        inner_end = balanced(text, m.start() + 1)
        if outer_end > 0 and inner_end == outer_end - 1:
            out.append(text[i:m.start()] + "(" + text[m.start() + 2:inner_end - 1] + ")")
            i = outer_end
    out.append(text[i:])
    return "".join(out)


def tidy(text, preamble=True, fold_code=True):
    header, sep, body = text.partition("\n\n")
    if not sep:
        header, body = "", text
    if preamble:
        body = strip_preamble(body)
    # before folding, so helper names and parameters see the final instance names
    body = name_instances(body)
    stats = {}
    body = fold.fold(body, stats) if fold_code else fold.strip_markers(body)
    if stats.get("helpers") or stats.get("loops"):
        body = ("-- yeah this is gonna be shit ig")
    body = unwrap_parens(body)
    body = hoist_repeats(body)
    body = trim_params(body)
    return header + sep + body


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("input")
    ap.add_argument("-o", "--output")
    ap.add_argument("--keep-preamble", action="store_true")
    ap.add_argument("--no-fold", action="store_true")
    a = ap.parse_args()
    with open(a.input, encoding="utf-8") as f:
        text = f.read()
    out = tidy(text, not a.keep_preamble, not a.no_fold)
    with open(a.output or a.input, "w", encoding="utf-8", newline="\n") as f:
        f.write(out)


if __name__ == "__main__":
    main()
