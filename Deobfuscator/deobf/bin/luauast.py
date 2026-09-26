"""
Luau source <-> luau-ast JSON: `parse(text)` runs bin/luau-ast and returns
the AST as dicts; `render(node)` prints a statement block / expression back
as indented Luau (one statement per line, elseif chains flattened, explicit
parentheses kept as the AST's AstExprGroup). For reading obfuscated one-line
VMs (StyLua overflows its stack on their nesting) and for static analysis.

Deep nesting: call through backend.run_big_stack (or `main`, which does).
String constants: luau-ast prints raw bytes, so the JSON is decoded as
latin-1 and every str here is a byte string in disguise (chr(0..255)).

    python deobf/luauast.py file.lua > pretty.lua
"""
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

BINOPS = {
    "Add": "+", "Sub": "-", "Mul": "*", "Div": "/", "FloorDiv": "//", "Mod": "%", "Pow": "^",
    "Concat": "..", "CompareNe": "~=", "CompareEq": "==", "CompareLt": "<", "CompareLe": "<=",
    "CompareGt": ">", "CompareGe": ">=", "And": "and", "Or": "or",
}
UNOPS = {"Not": "not ", "Minus": "-", "Len": "#"}


def parse(text):
    """AST dict of Luau source `text` (latin-1 str)."""
    fd, path = tempfile.mkstemp(suffix=".lua")
    try:
        with os.fdopen(fd, "wb") as f:
            f.write(text.encode("latin-1"))
        out = subprocess.run([os.path.join(HERE, "bin", "luau-ast.exe" if os.name == "nt" else "luau-ast"), path],
                             capture_output=True, check=True).stdout
    finally:
        os.remove(path)
    return json.loads(out.decode("latin-1"))["root"]


def quote(s):
    out = ['"']
    for ch in s:
        o = ord(ch)
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif 32 <= o < 127:
            out.append(ch)
        else:
            out.append("\\%03d" % o)
    out.append('"')
    return "".join(out)


def num(v):
    if isinstance(v, float) and v.is_integer() and abs(v) < 2 ** 53:
        return str(int(v))
    if v == float("inf"):
        return "math.huge"
    if v == float("-inf"):
        return "-math.huge"
    if v != v:
        return "(0/0)"
    return repr(v)


class Printer:
    def __init__(self, indent="  "):
        self.ind = indent
        self.lines = []

    # expressions ---------------------------------------------------------
    def expr(self, e, depth=0):
        t = e["type"]
        if t == "AstExprConstantNumber":
            return num(e["value"])
        if t == "AstExprConstantString":
            return quote(e["value"])
        if t == "AstExprConstantBool":
            return "true" if e["value"] else "false"
        if t == "AstExprConstantNil":
            return "nil"
        if t == "AstExprLocal":
            return e["local"]["name"]
        if t == "AstExprGlobal":
            return e["global"]
        if t == "AstExprVarargs":
            return "..."
        if t == "AstExprGroup":
            return "(" + self.expr(e["expr"], depth) + ")"
        if t == "AstExprIndexName":
            return self.prefix(e["expr"], depth) + e["op"] + e["index"]
        if t == "AstExprIndexExpr":
            return self.prefix(e["expr"], depth) + "[" + self.expr(e["index"], depth) + "]"
        if t == "AstExprCall":
            f = e["func"]
            args = ", ".join(self.expr(a, depth) for a in e["args"])
            return self.prefix(f, depth) + "(" + args + ")"
        if t == "AstExprUnary":
            return UNOPS[e["op"]] + self.operand(e["expr"], depth)
        if t == "AstExprBinary":
            return self.operand(e["left"], depth) + " " + BINOPS[e["op"]] + " " + self.operand(e["right"], depth)
        if t == "AstExprIfElse":
            return ("if " + self.expr(e["condition"], depth) + " then " + self.expr(e["trueExpr"], depth)
                    + " else " + self.expr(e["falseExpr"], depth))
        if t == "AstExprTable":
            items = []
            for it in e["items"]:
                k = it["kind"]
                if k == "item":
                    items.append(self.expr(it["value"], depth))
                elif k == "record":
                    items.append(it["key"]["value"] + " = " + self.expr(it["value"], depth))
                else:
                    items.append("[" + self.expr(it["key"], depth) + "] = " + self.expr(it["value"], depth))
            return "{" + ", ".join(items) + "}"
        if t == "AstExprFunction":
            return self.function(e, "function", depth)
        if t == "AstExprInterpString":
            parts = []
            for i, s in enumerate(e["strings"]):
                parts.append(s.replace("{", "\\{").replace("`", "\\`"))
                if i < len(e["expressions"]):
                    parts.append("{" + self.expr(e["expressions"][i], depth) + "}")
            return "`" + "".join(parts) + "`"
        if t == "AstExprTypeAssertion":
            return self.expr(e["expr"], depth)
        raise ValueError("unknown expression " + t)

    def prefix(self, e, depth):
        s = self.expr(e, depth)
        if e["type"] in ("AstExprLocal", "AstExprGlobal", "AstExprGroup", "AstExprIndexName",
                         "AstExprIndexExpr", "AstExprCall"):
            return s
        return "(" + s + ")"

    def operand(self, e, depth):
        # the AST keeps source parentheses as AstExprGroup; nested operators
        # without a group bind as written, parenthesize them to be safe
        s = self.expr(e, depth)
        if e["type"] in ("AstExprBinary", "AstExprIfElse", "AstExprFunction"):
            return "(" + s + ")"
        return s

    def function(self, e, head, depth):
        params = [a["name"] for a in e["args"]]
        if e.get("vararg"):
            params.append("...")
        sub = type(self)(self.ind)
        sub.block(e["body"], depth + 1)
        body = "\n".join(sub.lines)
        return head + "(" + ", ".join(params) + ")\n" + body + ("\n" if body else "") + self.ind * depth + "end"

    # statements ----------------------------------------------------------
    def emit(self, depth, text):
        self.lines.append(self.ind * depth + text)

    def block(self, b, depth):
        for s in b["body"]:
            self.stat(s, depth)

    def stat(self, s, depth):
        t = s["type"]
        if t == "AstStatBlock":
            self.emit(depth, "do")
            self.block(s, depth + 1)
            self.emit(depth, "end")
        elif t == "AstStatLocal":
            names = ", ".join(v["name"] for v in s["vars"])
            if s["values"]:
                self.emit(depth, "local " + names + " = " + ", ".join(self.expr(v, depth) for v in s["values"]))
            else:
                self.emit(depth, "local " + names)
        elif t == "AstStatAssign":
            self.emit(depth, ", ".join(self.expr(v, depth) for v in s["vars"]) + " = "
                      + ", ".join(self.expr(v, depth) for v in s["values"]))
        elif t == "AstStatCompoundAssign":
            self.emit(depth, self.expr(s["var"], depth) + " " + BINOPS[s["op"]] + "= " + self.expr(s["value"], depth))
        elif t == "AstStatExpr":
            self.emit(depth, self.expr(s["expr"], depth))
        elif t == "AstStatReturn":
            self.emit(depth, ("return " + ", ".join(self.expr(v, depth) for v in s["list"])).rstrip())
        elif t == "AstStatBreak":
            self.emit(depth, "break")
        elif t == "AstStatContinue":
            self.emit(depth, "continue")
        elif t == "AstStatIf":
            self.emit(depth, "if " + self.expr(s["condition"], depth) + " then")
            self.block(s["thenbody"], depth + 1)
            e = s.get("elsebody")
            while e is not None:
                if e["type"] == "AstStatIf":
                    self.emit(depth, "elseif " + self.expr(e["condition"], depth) + " then")
                    self.block(e["thenbody"], depth + 1)
                    e = e.get("elsebody")
                else:
                    self.emit(depth, "else")
                    self.block(e, depth + 1)
                    e = None
            self.emit(depth, "end")
        elif t == "AstStatWhile":
            self.emit(depth, "while " + self.expr(s["condition"], depth) + " do")
            self.block(s["body"], depth + 1)
            self.emit(depth, "end")
        elif t == "AstStatRepeat":
            self.emit(depth, "repeat")
            self.block(s["body"], depth + 1)
            self.emit(depth, "until " + self.expr(s["condition"], depth))
        elif t == "AstStatFor":
            head = "for %s = %s, %s" % (s["var"]["name"], self.expr(s["from"], depth), self.expr(s["to"], depth))
            if s.get("step"):
                head += ", " + self.expr(s["step"], depth)
            self.emit(depth, head + " do")
            self.block(s["body"], depth + 1)
            self.emit(depth, "end")
        elif t == "AstStatForIn":
            self.emit(depth, "for %s in %s do" % (", ".join(v["name"] for v in s["vars"]),
                                                  ", ".join(self.expr(v, depth) for v in s["values"])))
            self.block(s["body"], depth + 1)
            self.emit(depth, "end")
        elif t == "AstStatLocalFunction":
            self.emit(depth, self.function(s["func"], "local function " + s["name"]["name"], depth))
        elif t == "AstStatFunction":
            self.emit(depth, self.function(s["func"], "function " + self.expr(s["name"], depth), depth))
        elif t in ("AstStatTypeAlias", "AstStatDeclareGlobal", "AstStatDeclareFunction", "AstStatDeclareClass"):
            pass
        else:
            raise ValueError("unknown statement " + t)


def render(node, indent="  "):
    p = Printer(indent)
    if node["type"] == "AstStatBlock":
        p.block(node, 0)
    elif node["type"].startswith("AstStat"):
        p.stat(node, 0)
    else:
        return p.expr(node)
    return "\n".join(p.lines)


def main():
    import backend
    src = open(sys.argv[1], encoding="latin-1").read()
    text = backend.run_big_stack(lambda: render(parse(src)))
    sys.stdout.buffer.write((text + "\n").encode("latin-1"))


if __name__ == "__main__":
    sys.path.insert(0, HERE)
    main()
