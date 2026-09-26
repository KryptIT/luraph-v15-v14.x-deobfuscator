#!/usr/bin/env python3
"""Generic automatic deobfuscator for LuaObfuscator.com (Ferib) VM-protected scripts.

    python3 deobfuscate.py input.lua -o output.lua [--verify] [--raw]

Nothing here is specific to one obfuscated file: the obfuscator's own loader is executed to recover
the bytecode, every VM handler is symbolically executed to learn its meaning, and the result is
structured, cleaned and printed as Lua with locals named v1, v2, ...
"""
import argparse
import sys
import time

import emit
import interp
import lifter
import lualib
import luaparse
import passes
import recon
import structure
from ir import *


def simplify(fn, limit=2000):
    for _ in range(limit):
        ch = passes.peephole(fn)
        ch |= recon.const_fold(fn)
        ch |= passes.inline_once(fn)
        ch |= passes.dce_once(fn)
        if not ch:
            return


def reconstruct(src, log=print, raw=False):
    t0 = time.time()
    L = lifter.Lifter(src)
    protos = L.lift_all()
    log('lifted %d function(s) in %.2fs' % (len(protos), time.time() - t0))
    funcs = {}
    warnings = []
    for P in protos:
        for w in P.warnings:
            warnings.append('function %d: %s' % (P.pid, w))
        body = structure.Structurer(P, lambda m, pid=P.pid: warnings.append('function %d: %s' % (pid, m))).run()
        funcs[P.pid] = Function(P.pid, P.nparams, body, P.uses_vararg)
    root = protos[0].pid

    if not raw:
        order = [f for f, _, _ in recon.child_order(funcs, root)]
        for fn in order:
            simplify(fn)
            if passes.Deflattener(fn).run():
                log('function %d: removed control-flow flattening' % fn.pid)
            simplify(fn)
        # decrypt strings / fold helper calls by running the recovered helpers
        for _ in range(10):
            if not recon.fold_calls(funcs, root):
                break
            for fn in order:
                simplify(fn)
        recon.prune_caps(funcs, root)
        for fn in order:
            simplify(fn)
            while passes.fold_const_tables(fn):
                simplify(fn)
        # remove functions that are no longer referenced
        live = {f.pid for f, _, _ in recon.child_order(funcs, root)}
        for pid in list(funcs):
            if pid not in live:
                del funcs[pid]
        recon.Namer().run(funcs, root)

    pr = emit.Printer(funcs)
    pr.block(funcs[root].body, 0)
    text = '\n'.join(pr.lines)
    text = recon.renumber(text)
    head = ['-- Reconstructed automatically by deobfuscate.py (LuaObfuscator.com VM)',
            '-- Original local names are not recoverable; locals are named v1, v2, ...']
    for w in warnings:
        head.append('-- WARNING: ' + w)
    return '\n'.join(head) + '\n\n' + text + '\n', warnings


def run_lua(src, max_steps=50_000_000):
    """Execute Lua source in the sandbox interpreter, returning captured print output."""
    out = []
    I = interp.Interp()
    I.max_steps = max_steps
    lualib.make_env(I, output=out)
    sc = interp.Scope()
    sc.vars['...'] = []
    I.exec_block(luaparse.parse(src), sc)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('input')
    ap.add_argument('-o', '--output')
    ap.add_argument('--verify', action='store_true',
                    help='run original and reconstruction in the sandbox and compare printed output')
    ap.add_argument('--raw', action='store_true', help='skip cleanup passes (debug)')
    a = ap.parse_args()
    src = open(a.input, 'rb').read()
    log = lambda m: print('[*] ' + m, file=sys.stderr)
    text, warns = reconstruct(src, log, a.raw)
    if a.output:
        open(a.output, 'w', encoding='latin-1').write(text)
        log('wrote ' + a.output)
    else:
        sys.stdout.write(text)
    if warns:
        log('%d warning(s) - see header of output' % len(warns))
    if a.verify:
        luaparse.parse(text.encode('latin-1'))
        log('reconstruction parses OK')
        o1 = run_lua(src)
        o2 = run_lua(text.encode('latin-1'))
        if o1 == o2:
            log('verify OK: identical output (%d lines)' % len(o1))
        else:
            log('verify MISMATCH: original %d lines, reconstruction %d lines' % (len(o1), len(o2)))
            sys.exit(2)


if __name__ == '__main__':
    main()
