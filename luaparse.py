"""Minimal but complete Lua 5.1 lexer + parser producing a simple AST."""

import re


KEYWORDS = {
    "and", "break", "do", "else", "elseif", "end", "false", "for",
    "function", "if", "in", "local", "nil", "not", "or", "repeat",
    "return", "then", "true", "until", "while", "goto", "continue",
}


class Node:
    __slots__ = ("k", "a", "b", "c", "d", "e")

    def __init__(self, k, a=None, b=None, c=None, d=None, e=None):
        self.k, self.a, self.b, self.c, self.d, self.e = k, a, b, c, d, e

    def __repr__(self):
        return "Node(%s)" % self.k


class LuaSyntaxError(Exception):
    pass


_num_re = re.compile(
    r"0[xX][0-9a-fA-F]*(?:\.[0-9a-fA-F]*)?(?:[pP][+-]?\d+)?"
    r"|(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?"
)
_name_re = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")

# Longest operators first.
_ops = [
    # Longest operators first.
    "<<=", ">>=", "//=", "..=", "+=", "-=", "*=", "/=", "%=", "^=", "&=", "|=", "~=",
    "...", "==", "<=", ">=", "::", "<<", ">>", "//", "..",
    "+", "-", "*", "/", "%", "^", "#", "<", ">", "=", "(", ")",
    "{", "}", "[", "]", ";", ":", ",", ".", "&", "|", "~",
]


def _long_bracket(src, i):
    m = re.match(r"\[(=*)\[", src[i:])
    if not m:
        return None

    level = m.group(1)
    close = "]" + level + "]"
    start = i + m.end()
    j = src.find(close, start)
    if j < 0:
        raise LuaSyntaxError("unfinished long bracket")

    body = src[start:j]
    if body.startswith("\r\n"):
        body = body[2:]
    elif body.startswith("\n"):
        body = body[1:]

    return body, j + len(close)


def lex(src):
    """src is a str where each char is one byte (latin-1 decoded)."""
    toks = []
    i, n = 0, len(src)

    while i < n:
        c = src[i]

        if c in " \t\r\n\f\v":
            i += 1
            continue

        if src.startswith("--", i):
            lb = _long_bracket(src, i + 2) if src.startswith("[", i + 2) else None
            if lb:
                i = lb[1]
            else:
                j = src.find("\n", i)
                i = n if j < 0 else j + 1
            continue

        if c.isalpha() or c == "_":
            m = _name_re.match(src, i)
            w = m.group(0)
            toks.append(("kw" if w in KEYWORDS else "name", w))
            i = m.end()
            continue

        if c.isdigit() or (c == "." and i + 1 < n and src[i + 1].isdigit()):
            m = _num_re.match(src, i)
            if not m:
                raise LuaSyntaxError("invalid number at %d" % i)

            s = m.group(0)
            if s[:2].lower() == "0x":
                v = (
                    float(int(s, 16))
                    if re.fullmatch(r"0[xX][0-9a-fA-F]+", s)
                    else float.fromhex(s)
                )
            else:
                v = float(s)

            toks.append(("num", v))
            i = m.end()
            continue

        if c in "\"'":
            q = c
            i += 1
            out = []

            while True:
                if i >= n:
                    raise LuaSyntaxError("unfinished string")

                ch = src[i]

                if ch == q:
                    i += 1
                    break

                if ch == "\\":
                    i += 1
                    if i >= n:
                        raise LuaSyntaxError("unfinished string escape")

                    e = src[i]
                    simple = {
                        "n": "\n",
                        "t": "\t",
                        "r": "\r",
                        "a": "\a",
                        "b": "\b",
                        "f": "\f",
                        "v": "\v",
                        "\\": "\\",
                        '"': '"',
                        "'": "'",
                        "\n": "\n",
                    }

                    if e in simple:
                        out.append(simple[e])
                        i += 1
                    elif e == "x":
                        if i + 2 >= n:
                            raise LuaSyntaxError("unfinished hex escape")
                        try:
                            out.append(chr(int(src[i + 1:i + 3], 16)))
                        except ValueError:
                            raise LuaSyntaxError("invalid hex escape")
                        i += 3
                    elif e == "z":
                        i += 1
                        while i < n and src[i] in " \t\r\n\f\v":
                            i += 1
                    elif e.isdigit():
                        m = re.match(r"\d{1,3}", src[i:])
                        out.append(chr(int(m.group(0)) & 255))
                        i += m.end()
                    else:
                        out.append(e)
                        i += 1
                else:
                    out.append(ch)
                    i += 1

            toks.append(("str", "".join(out).encode("latin-1")))
            continue

        if c == "[":
            lb = _long_bracket(src, i)
            if lb:
                toks.append(("str", lb[0].encode("latin-1")))
                i = lb[1]
                continue

        for op in _ops:
            if src.startswith(op, i):
                toks.append(("op", op))
                i += len(op)
                break
        else:
            raise LuaSyntaxError("unexpected char %r at %d" % (c, i))

    toks.append(("eof", None))
    return toks


BINPRI = {
    "or": (1, 1),
    "and": (2, 2),
    "<": (3, 3),
    ">": (3, 3),
    "<=": (3, 3),
    ">=": (3, 3),
    "~=": (3, 3),
    "==": (3, 3),
    "|": (4, 4),
    "~": (5, 5),
    "&": (6, 6),
    "<<": (7, 7),
    ">>": (7, 7),
    "..": (9, 8),
    "+": (10, 10),
    "-": (10, 10),
    "*": (11, 11),
    "/": (11, 11),
    "//": (11, 11),
    "%": (11, 11),
    "^": (14, 13),
}
UNPRI = 12

COMPOUND_ASSIGN = {
    "+=": "+",
    "-=": "-",
    "*=": "*",
    "/=": "/",
    "//=": "//",
    "%=": "%",
    "^=": "^",
    "..=": "..",
    "&=": "&",
    "|=": "|",
    "~=": "~",
    "<<=": "<<",
    ">>=": ">>",
}


class Parser:
    def __init__(self, src):
        self.t = lex(src)
        self.p = 0

    def peek(self, off=0):
        return self.t[self.p + off]

    def nxt(self):
        tok = self.t[self.p]
        self.p += 1
        return tok

    def check(self, kind, val=None):
        t = self.t[self.p]
        return t[0] == kind and (val is None or t[1] == val)

    def accept(self, kind, val=None):
        if self.check(kind, val):
            return self.nxt()
        return None

    def _context(self, radius=4):
        lo = max(0, self.p - radius)
        hi = min(len(self.t), self.p + radius + 1)
        return self.t[lo:hi]

    def expect(self, kind, val=None):
        if not self.check(kind, val):
            raise LuaSyntaxError(
                "expected %s %s got %r near %r"
                % (kind, val, self.t[self.p], self._context())
            )
        return self.nxt()

    def isop(self, v):
        return self.check("op", v)

    def iskw(self, v):
        return self.check("kw", v)

    # ---- blocks

    def chunk(self):
        b = self.block()
        self.expect("eof")
        return b

    def block_end(self):
        t = self.peek()
        return t[0] == "eof" or (
            t[0] == "kw" and t[1] in ("end", "else", "elseif", "until")
        )

    def block(self):
        out = []

        while not self.block_end():
            # Lua permits empty statements / repeated semicolon separators.
            if self.accept("op", ";"):
                continue

            # `return` terminates the current block and therefore is handled
            # here rather than as a normal statement.
            if self.accept("kw", "return"):
                exprs = []
                if not self.block_end() and not self.isop(";"):
                    exprs = self.exprlist()

                out.append(Node("Return", exprs))

                while self.accept("op", ";"):
                    pass
                break

            s = self.statement()
            if s is not None:
                out.append(s)

            while self.accept("op", ";"):
                pass

        return out

    def statement(self):
        # Accept an empty statement even if statement() is called directly.
        if self.accept("op", ";"):
            return None

        t = self.peek()

        # Defensive Luau support: tolerate `continue` even if a caller uses a
        # lexer table that still classifies it as a normal identifier.
        if t == ("name", "continue"):
            self.nxt()
            return Node("Continue")

        if t[0] == "kw":
            w = t[1]

            if w == "if":
                self.nxt()
                conds, blocks = [], []

                conds.append(self.expr())
                self.expect("kw", "then")
                blocks.append(self.block())

                els = None
                while True:
                    if self.accept("kw", "elseif"):
                        conds.append(self.expr())
                        self.expect("kw", "then")
                        blocks.append(self.block())
                    elif self.accept("kw", "else"):
                        els = self.block()
                        self.expect("kw", "end")
                        break
                    else:
                        self.expect("kw", "end")
                        break

                return Node("If", conds, blocks, els)

            if w == "while":
                self.nxt()
                c = self.expr()
                self.expect("kw", "do")
                b = self.block()
                self.expect("kw", "end")
                return Node("While", c, b)

            if w == "do":
                self.nxt()
                b = self.block()
                self.expect("kw", "end")
                return Node("Do", b)

            if w == "for":
                self.nxt()
                n1 = self.expect("name")[1]

                if self.accept("op", "="):
                    a = self.expr()
                    self.expect("op", ",")
                    b = self.expr()
                    c = self.expr() if self.accept("op", ",") else None
                    self.expect("kw", "do")
                    body = self.block()
                    self.expect("kw", "end")
                    return Node("NumFor", n1, a, b, c, body)

                names = [n1]
                while self.accept("op", ","):
                    names.append(self.expect("name")[1])

                self.expect("kw", "in")
                exprs = self.exprlist()
                self.expect("kw", "do")
                body = self.block()
                self.expect("kw", "end")
                return Node("GenFor", names, exprs, body)

            if w == "repeat":
                self.nxt()
                b = self.block()
                self.expect("kw", "until")
                c = self.expr()
                return Node("Repeat", b, c)

            if w == "function":
                self.nxt()
                name = Node("Name", self.expect("name")[1])
                is_method = False

                while True:
                    if self.accept("op", "."):
                        name = Node(
                            "Index",
                            name,
                            Node("Str", self.expect("name")[1].encode()),
                        )
                    elif self.accept("op", ":"):
                        name = Node(
                            "Index",
                            name,
                            Node("Str", self.expect("name")[1].encode()),
                        )
                        is_method = True
                        break
                    else:
                        break

                f = self.funcbody(is_method)
                return Node("Assign", [name], [f])

            if w == "local":
                self.nxt()

                if self.accept("kw", "function"):
                    nm = self.expect("name")[1]
                    f = self.funcbody(False)
                    return Node("LocalFunction", nm, f)

                names = [self.expect("name")[1]]
                while self.accept("op", ","):
                    names.append(self.expect("name")[1])

                exprs = self.exprlist() if self.accept("op", "=") else []
                return Node("Local", names, exprs)

            if w == "break":
                self.nxt()
                return Node("Break")

            # Luau extension. LuaObfuscator output may contain `continue;`.
            # Without treating it as a keyword, it is parsed as a bare name and
            # fails at the following semicolon.
            if w == "continue":
                self.nxt()
                return Node("Continue")

            if w == "goto":
                self.nxt()
                return Node("Goto", self.expect("name")[1])

        if self.accept("op", "::"):
            nm = self.expect("name")[1]
            self.expect("op", "::")
            return Node("Label", nm)

        e = self.suffixedexp()

        # Luau compound assignment: x += y, x -= y, x *= y, etc.
        # Desugar it to the AST shape the rest of this deobfuscator already
        # understands: x = x <op> y.
        tok = self.peek()
        if tok[0] == "op" and tok[1] in COMPOUND_ASSIGN:
            if e.k not in ("Name", "Index"):
                raise LuaSyntaxError("invalid compound-assignment target %r" % (e.k,))
            compound = self.nxt()[1]
            rhs = self.expr()
            return Node(
                "Assign",
                [e],
                [Node("Bin", COMPOUND_ASSIGN[compound], e, rhs)],
            )

        if self.isop("=") or self.isop(","):
            targets = [e]
            while self.accept("op", ","):
                targets.append(self.suffixedexp())

            self.expect("op", "=")
            return Node("Assign", targets, self.exprlist())

        if e.k not in ("Call", "Method"):
            raise LuaSyntaxError("syntax error near %r; context=%r" % (self.peek(), self._context()))

        return Node("CallStat", e)

    def funcbody(self, is_method):
        self.expect("op", "(")
        params = ["self"] if is_method else []
        vararg = False

        if not self.isop(")"):
            while True:
                if self.accept("op", "..."):
                    vararg = True
                    break

                params.append(self.expect("name")[1])
                if not self.accept("op", ","):
                    break

        self.expect("op", ")")
        body = self.block()
        self.expect("kw", "end")
        return Node("Func", params, vararg, body)

    def exprlist(self):
        l = [self.expr()]
        while self.accept("op", ","):
            l.append(self.expr())
        return l

    def primaryexp(self):
        if self.check("name"):
            return Node("Name", self.nxt()[1])

        if self.accept("op", "("):
            e = self.expr()
            self.expect("op", ")")
            return Node("Paren", e)

        raise LuaSyntaxError("unexpected symbol %r; context=%r" % (self.peek(), self._context()))

    def suffixedexp(self):
        e = self.primaryexp()

        while True:
            if self.accept("op", "."):
                e = Node(
                    "Index",
                    e,
                    Node("Str", self.expect("name")[1].encode()),
                )
            elif self.accept("op", "["):
                k = self.expr()
                self.expect("op", "]")
                e = Node("Index", e, k)
            elif self.accept("op", ":"):
                nm = self.expect("name")[1].encode()
                e = Node("Method", e, nm, self.callargs())
            elif self.isop("(") or self.isop("{") or self.check("str"):
                e = Node("Call", e, self.callargs())
            else:
                return e

    def callargs(self):
        if self.check("str"):
            return [Node("Str", self.nxt()[1])]

        if self.isop("{"):
            return [self.table()]

        self.expect("op", "(")
        if self.accept("op", ")"):
            return []

        l = self.exprlist()
        self.expect("op", ")")
        return l

    def table(self):
        self.expect("op", "{")
        items = []

        while not self.isop("}"):
            if self.accept("op", "["):
                k = self.expr()
                self.expect("op", "]")
                self.expect("op", "=")
                items.append(("key", k, self.expr()))
            elif self.check("name") and self.peek(1) == ("op", "="):
                k = Node("Str", self.nxt()[1].encode())
                self.nxt()
                items.append(("key", k, self.expr()))
            else:
                items.append(("pos", None, self.expr()))

            if not (self.accept("op", ",") or self.accept("op", ";")):
                break

        self.expect("op", "}")
        return Node("Table", items)

    def ifexpr(self):
        """Parse Luau's expression form: if c then a elseif d then b else e.

        The rest of this deobfuscator only knows the original small AST, so
        lower the expression to an immediately-called anonymous function whose
        branches return the corresponding values. That avoids introducing a new
        AST node kind that lifter/interp/emit would also need to understand.
        """
        self.expect("kw", "if")

        conds = []
        blocks = []

        conds.append(self.expr())
        self.expect("kw", "then")
        blocks.append([Node("Return", [self.expr()])])

        while self.accept("kw", "elseif"):
            conds.append(self.expr())
            self.expect("kw", "then")
            blocks.append([Node("Return", [self.expr()])])

        self.expect("kw", "else")
        els = [Node("Return", [self.expr()])]

        body = [Node("If", conds, blocks, els)]
        return Node("Call", Node("Func", [], False, body), [])

    def simpleexp(self):
        t = self.peek()

        # Luau if-expression, e.g.:
        #   local x = if ok then 1 else 2
        # This must be handled before suffixedexp(), otherwise `if` reaches
        # primaryexp() and is rejected as an unexpected keyword.
        if t == ("kw", "if"):
            return self.ifexpr()

        if t[0] == "num":
            self.nxt()
            return Node("Num", t[1])

        if t[0] == "str":
            self.nxt()
            return Node("Str", t[1])

        if t[0] == "kw":
            if t[1] == "nil":
                self.nxt()
                return Node("Nil")

            if t[1] == "true":
                self.nxt()
                return Node("True")

            if t[1] == "false":
                self.nxt()
                return Node("False")

            if t[1] == "function":
                self.nxt()
                return self.funcbody(False)

        if self.isop("..."):
            self.nxt()
            return Node("Vararg")

        if self.isop("{"):
            return self.table()

        return self.suffixedexp()

    def expr(self, limit=0):
        t = self.peek()

        if (t[0] == "kw" and t[1] == "not") or (
            t[0] == "op" and t[1] in ("-", "#", "~")
        ):
            self.nxt()
            e = Node("Un", t[1], self.expr(UNPRI))
        else:
            e = self.simpleexp()

        while True:
            t = self.peek()
            op = t[1] if t[0] in ("op", "kw") else None

            if op not in BINPRI or BINPRI[op][0] <= limit:
                return e

            self.nxt()
            rhs = self.expr(BINPRI[op][1])
            e = Node("Bin", op, e, rhs)


def parse(src_bytes):
    if isinstance(src_bytes, bytes):
        src_bytes = src_bytes.decode("latin-1")

    return Parser(src_bytes).chunk()
