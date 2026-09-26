"""
Instruction listing of a captured proto (research aid):

    python -m obfuscators.ironbrew1.listing <src> <dump.json> CAP [FROM TO]   (from deobf/)

Prints each instruction's fields (the tables the dispatch loop fetches) and
its handler source (handler.py), one line per statement.
"""
import json
import sys

import backend
import luauast
from obfuscators.ironbrew1 import devirt as D
from obfuscators.ironbrew1.handler import reach, opcode_local


def main():
    src = open(sys.argv[1], encoding="latin-1").read()
    d = json.load(open(sys.argv[2]))
    ci = int(sys.argv[3])
    lo = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    hi = int(sys.argv[5]) if len(sys.argv) > 5 else 10 ** 9

    def go():
        prog = D.Program(src, d)
        lf = D.ProtoLifter(prog, ci, D.UpList())
        lf.initial_state()
        vm = lf.vm
        it = D.LiftInterp(lf)
        body = vm.loop_body
        code = it.eval(body[0]["values"][0]["expr"], lf.cscope)
        opkey, first = opcode_local(body)
        pc_decl = vm.pc_decl
        cache = {}
        n = max(k for k in code.h if isinstance(k, int))
        for pc in range(lo, min(hi, n) + 1):
            sc = D.Scope(lf.iscope)
            sc.vars[pc_decl] = pc
            try:
                for st in body[:first]:
                    it.exec_stmt(st, sc)
                op = sc.lookup(opkey).vars[opkey]
            except Exception as ex:  # noqa: BLE001
                print("%5d  ?? %s" % (pc, ex))
                continue
            ins = code.get(pc)
            fields = " ".join("%s=%s" % (k, D.fmt_any(v)) for k, v in sorted(ins.h.items(), key=lambda kv: repr(kv[0]))
                              if not isinstance(v, D.LTable)) if isinstance(ins, D.LTable) else D.fmt_any(ins)
            if op not in cache:
                out = []
                reach(body[first:], op, opkey, out)
                txt = luauast.render({"type": "AstStatBlock", "body": out}).split("\n")
                cache[op] = [t.strip() for t in txt if t.strip() and not t.strip().startswith("is = is + 1")]
            h = cache[op]
            print("%5d  op %-4s %-40s | %s" % (pc, op, fields[:40], " ; ".join(h)[:160]))
    backend.run_big_stack(go)


if __name__ == "__main__":
    main()
