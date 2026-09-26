# developer helper: call-free instrumentation of every interpreter loop (h.luau)
# records into __R: numbers = packed (proto, loop, op, pc); tables = {value}
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
import harness as deob
from obfuscators.luraph_v15 import vmmap
from obfuscators.luraph_v15.driver import patch_entries
deob.patch_entries = patch_entries

path = sys.argv[1]
src = open(path, encoding='latin-1', newline='').read()
skip = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else []
src = deob.patch_entries(src, path)
open('_patched.luau', 'w', encoding='latin-1', newline='').write(src)
root = vmmap.load_ast('_patched.luau')
src2 = vmmap.instrument_everything(
    src, root,
    lambda op, dst, pc: '__R[#__R+1]={%s};' % dst,
    lambda k, opv, pcv: ('local _x=x or __P;local _p=__P[_x];'
                         'if not _p then _p=__P.n+1;__P.n=_p;__P[_x]=_p;end;'
                         '__R[#__R+1]=((_p*16+%d)*256+%s)*65536+%s;') % (k, opv, pcv))

# extra probes: (loop, opcode, lua code inserted before the handler)
EXTRA = [(4, 84, '__R[#__R+1]={"envkey:"..tostring(Y[W])};'),
         (2, 18, '__R[#__R+1]={"S18"};__R[#__R+1]={Z[S[W]]};__R[#__R+1]={Z[F[W]]};'),
         (2, 46, '__R[#__R+1]={"S46"};__R[#__R+1]={F[W]};__R[#__R+1]={Z[S[W]]};'),
         (2, 2, '__R[#__R+1]={"S2"};__R[#__R+1]={Y[W]};__R[#__R+1]={Z[f[W]]};'),
         (1, 29, '__R[#__R+1]={"VA"};local __va={...};for __i=1,6 do __R[#__R+1]={__va[__i]} end;')]
lines = src.split('\n')
lines2 = src2.split('\n')
disps = vmmap.find_dispatchers(root)
for loop, op, code in EXTRA:
    d = disps[loop - 1]
    blk = vmmap.resolve(d['tree'], d['op'], op)
    l1 = vmmap.loc(blk)[0]
    ht = vmmap.text_of(lines, blk).strip()
    pos = lines2[l1].find(ht)
    assert pos >= 0, 'handler text not found'
    lines2[l1] = lines2[l1][:pos] + code + lines2[l1][pos:]
src2 = '\n'.join(lines2)

open('h.luau', 'w', encoding='latin-1', newline='\n').write(
    deob.build_harness(src2, {'inline_probe': True, 'time_budget': 60, 'skip_protos': skip, 'dump_err': 5000000}))
