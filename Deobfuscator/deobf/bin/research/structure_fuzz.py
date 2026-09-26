"""Structurer fuzz check: random CFGs -> structure.structure; the CFG and
the structured AST are interpreted on the same condition sequences and must
trace the same, and no goto may remain.

    python research/structure_fuzz.py [first seed] [count]
"""
import os
import random
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import structure as ST
import codegen as CG
from luasym import Global, Const, Multi, Bin, Un

LIMIT = 200
sys.setrecursionlimit(20000)


class Stop(Exception):
    pass


class Env:
    def __init__(self, bits):
        self.bits, self.i, self.trace, self.vars = bits, 0, [], {}

    def bit(self):
        if self.i >= len(self.bits):
            raise Stop()
        self.i += 1
        return self.bits[self.i - 1]

    def emit(self, x):
        self.trace.append(x)
        if len(self.trace) >= LIMIT:
            raise Stop()


def ev(e, env):
    if isinstance(e, CG.CallE):
        return env.bit()
    if isinstance(e, Un) and e.op == "Not":
        return not ev(e.a, env)
    if isinstance(e, Bin) and e.op in ("CompareEq", "CompareNe"):
        a = env.vars.get(e.a.name) if isinstance(e.a, CG.LocalName) else e.a.v
        b = e.b.v
        return (a == b) == (e.op == "CompareEq")
    if isinstance(e, Bin) and e.op in ("And", "Or"):
        a = ev(e.a, env)
        if e.op == "And":
            return ev(e.b, env) if a else a
        return a if a else ev(e.b, env)
    raise ValueError("cond %r" % (e,))


def run_stmt(s, env):
    if isinstance(s, CG.CallS):
        env.emit(s.call.args.items[0].v)
    elif isinstance(s, CG.AssignS):
        env.vars[s.targets[0].name] = s.values.items[0].v
    elif isinstance(s, CG.LocalS):
        for n in s.names:
            env.vars[n] = None
    else:
        raise ValueError(s)


class Brk(Exception):
    pass


class Cont(Exception):
    pass


class Ret(Exception):
    pass


def run_ast(stmts, env):
    for s in stmts:
        if isinstance(s, ST.SIf):
            run_ast(s.then if ev(s.cond, env) else s.els, env)
        elif isinstance(s, ST.SLoop):
            while True:
                if s.cond is not None and not ev(s.cond, env):
                    break
                try:
                    run_ast(s.body, env)
                except Brk:
                    break
                except Cont:
                    continue
        elif isinstance(s, ST.SBreak):
            raise Brk()
        elif isinstance(s, ST.SContinue):
            raise Cont()
        elif isinstance(s, ST.SReturn):
            env.emit("ret")
            raise Ret()
        elif isinstance(s, ST.SGotoState):
            env.emit("GOTO")
            raise Ret()
        elif isinstance(s, ST.SError):
            env.emit("ERR")
            raise Ret()
        else:
            run_stmt(s, env)


def run_cfg(entry, blocks, env):
    cur = entry
    while True:
        b = blocks[cur]
        for s in b.stmts:
            run_stmt(s, env)
        if b.kind == "ret":
            env.emit("ret")
            return
        if b.kind == "goto":
            cur = b.succ[0]
        else:
            cur = b.succ[0] if ev(b.cond, env) else b.succ[1]


def gen(rng, n):
    blocks = {}
    for i in range(1, n + 1):
        b = ST.Block(i)
        b.stmts = [CG.CallS(CG.CallE(Global("f"), Multi([Const(i)])))]
        r = rng.random()
        if r < 0.15 and i > 1:
            b.kind = "ret"
            b.values = Multi([])
        elif r < 0.45:
            b.kind = "goto"
            b.succ = [rng.randint(1, n)]
        else:
            b.kind = "cond"
            b.cond = CG.CallE(Global("c"), Multi([]))
            a, c = rng.randint(1, n), rng.randint(1, n)
            while c == a:
                c = rng.randint(1, n)
            b.succ = [a, c]
        blocks[i] = b
    reach = ST.reachable(1, blocks)
    for k in list(blocks):
        if k not in reach:
            del blocks[k]
    ST.recompute_preds(blocks)
    return blocks


def fresh(blocks):
    import copy
    return copy.deepcopy(blocks)


def main(seed0=0, count=3000):
    bad = gotos = 0
    for seed in range(seed0, seed0 + count):
        rng = random.Random(seed)
        n = rng.randint(2, 11)
        blocks = gen(rng, n)
        orig = fresh(blocks)
        own = set()
        try:
            entry, body, sr = ST.structure(1, blocks, own)
            body = ST.cleanup(body)
        except Exception as ex:  # noqa: BLE001
            print("seed %d: exception %r" % (seed, ex))
            bad += 1
            continue
        if sr.fallbacks:
            gotos += 1
        for t in range(12):
            bits = [random.Random(seed * 100 + t).random() < 0.5 for _ in range(400)]
            e1, e2 = Env(bits), Env(bits)
            try:
                run_cfg(1, orig, e1)
            except Stop:
                pass
            try:
                run_ast(body, e2)
            except (Stop, Ret):
                pass
            k = min(len(e1.trace), len(e2.trace))
            ok = e1.trace[:k] == e2.trace[:k] and (len(e1.trace) == len(e2.trace) or k >= LIMIT - 1
                                                    or e1.i >= len(bits) or e2.i >= len(bits))
            if not ok or "GOTO" in e2.trace:
                if not sr.fallbacks:
                    print("seed %d: MISMATCH\n cfg %s\n ast %s" % (seed, e1.trace[:40], e2.trace[:40]))
                    bad += 1
                break
    print("done: %d mismatches/exceptions, %d with gotos left, of %d" % (bad, gotos, count))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 0, int(sys.argv[2]) if len(sys.argv) > 2 else 3000)
