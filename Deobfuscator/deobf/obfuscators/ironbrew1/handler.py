"""
Print the handler source of an opcode (research aid):

    python -m obfuscators.ironbrew1.handler <src> OP [OP ...]     (from deobf/)

Follows the interpreter's if-tree on the opcode local (comparisons with
number constants, folded arithmetic) and prints the statements it reaches.
"""
import sys

import backend
import luauast
from obfuscators.ironbrew1 import instrument
from obfuscators.ironbrew1.deflatten import fold


def num(e):
    e = fold(e)
    return e["value"] if e["type"] == "AstExprConstantNumber" else None


def test(c, op, opkey):
    """value of condition c for opcode op, or None if it is not about the opcode"""
    t = c["type"]
    if t == "AstExprGroup":
        return test(c["expr"], op, opkey)
    if t == "AstExprUnary" and c["op"] == "Not":
        v = test(c["expr"], op, opkey)
        return None if v is None else not v
    if t != "AstExprBinary":
        return None
    l, r = c["left"], c["right"]
    while l["type"] == "AstExprGroup":
        l = l["expr"]
    while r["type"] == "AstExprGroup":
        r = r["expr"]
    ops = {"CompareLt": lambda a, b: a < b, "CompareLe": lambda a, b: a <= b, "CompareGt": lambda a, b: a > b,
           "CompareGe": lambda a, b: a >= b, "CompareEq": lambda a, b: a == b, "CompareNe": lambda a, b: a != b}
    if c["op"] not in ops:
        return None
    if l["type"] == "AstExprLocal" and l["local"]["location"] == opkey and num(r) is not None:
        return ops[c["op"]](op, num(r))
    if r["type"] == "AstExprLocal" and r["local"]["location"] == opkey and num(l) is not None:
        return ops[c["op"]](num(l), op)
    return None


def _target(st):
    if st["type"] == "AstStatAssign" and st["vars"][0]["type"] == "AstExprLocal":
        return st["vars"][0]["local"]["location"]
    if st["type"] == "AstStatLocal":
        return st["vars"][0]["location"]
    return None


def opcode_local(body):
    """(declaration of the opcode local, index of the first handler statement):
    `ins = code[pc]; op = ins[k]` or directly `op = ops[pc]`"""
    if len(body) > 1 and _target(body[1]) is not None and body[1].get("values") and \
            body[1]["values"][0]["type"] in ("AstExprIndexExpr", "AstExprIndexName"):
        return _target(body[1]), 2
    return _target(body[0]), 1


def reach(stmts, op, opkey, out):
    for s in stmts:
        if s["type"] == "AstStatIf":
            v = test(s["condition"], op, opkey)
            if v is not None:
                if v:
                    reach(s["thenbody"]["body"], op, opkey, out)
                else:
                    e = s.get("elsebody")
                    if e is not None:
                        reach([e] if e["type"] == "AstStatIf" else e["body"], op, opkey, out)
                continue
        out.append(s)


def main():
    src = open(sys.argv[1], encoding="latin-1").read()

    def go():
        root = luauast.parse(src)
        for mk, interp in instrument.find_vms(root):
            loop = instrument.dispatch_loop(interp)
            body = loop["body"]["body"]
            opkey, first = opcode_local(body)
            for a in sys.argv[2:]:
                out = []
                reach(body[first:], int(a), opkey, out)
                print("-- op %s" % a)
                print(luauast.render({"type": "AstStatBlock", "body": out}))
    backend.run_big_stack(go)


if __name__ == "__main__":
    main()
