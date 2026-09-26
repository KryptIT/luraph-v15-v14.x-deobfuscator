# developer helper: instruments every interpreter loop (h.luau)
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
import harness as deob
from obfuscators.luraph_v15 import vmmap
from obfuscators.luraph_v15.driver import patch_entries
deob.patch_entries = patch_entries
path = sys.argv[1]
src = open(path, encoding='latin-1', newline='').read()
root = vmmap.load_ast(path)
src2 = vmmap.instrument_everything(
    src, root,
    lambda op, dst, pc: '__OPV(%s,%s);' % (dst, pc),
    lambda k, opv, pcv: '__OPL(%d,%s,%s,x);' % (k, opv, pcv))
open('h.luau', 'w', encoding='latin-1', newline='\n').write(
    deob.build_harness(src2, {'oplog': 4000000, 'time_budget': 60}))
