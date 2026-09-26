# developer helper: builds an instrumented harness (h.luau) for dispatch loop N
import re, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
import harness as deob
from obfuscators.luraph_v15 import vmmap
from obfuscators.luraph_v15.driver import patch_entries
deob.patch_entries = patch_entries
path = sys.argv[1]; disp = int(sys.argv[2]) if len(sys.argv) > 2 else 3
src = open(path, encoding='latin-1', newline='').read()
root = vmmap.load_ast(path)
probes = {
 61: '__OPLOG("LE r"..tostring(f[W]),__NAME(Z[f[W]]).." <= "..__NAME(R[W]),W);',
 37: '__OPLOG("LEr",__NAME(Z[R[W]]).." <= "..__NAME(S[W]),W);',
 71: '__OPLOG("TEST r"..tostring(S[W]),__NAME(Z[S[W]]),W);',
 50: '__OPLOG("UPV",__NAME(V[S[W]]),W);',
 58: '__OPLOG("CALL",__NAME(Z[f[W]]).."("..__NAME(Z[f[W]+1])..","..__NAME(Z[f[W]+2])..","..__NAME(Z[f[W]+3])..")",W);',
 40: '__OPLOG("CALL2",__NAME(Z[S[W]]).."("..__NAME(Z[S[W]+1])..","..__NAME(Z[S[W]+2])..")",W);',
 6: 'if Z[R[W]]==25 and type(Z[f[W]])=="table" then __OPLOG("HASHED",tostring(Z[f[W]]),W) end;',
 51: 'if type(Z[f[W]])=="table" and #Z[f[W]]==50 then __DUMP("len50",Z[f[W]]) end;',
 14: '__OPLOG("op14 r"..tostring(f[W]).."="..__NAME(Z[S[W]]).."; r"..tostring(R[W+1]),__NAME(S[W+1]),W);',
 44: '__OPLOG("op44 r"..tostring(R[W]).."="..__NAME(S[W]).."; r"..tostring(R[W+1]),__NAME(S[W+1]),W);',
 93: '__OPLOG("op93 r"..tostring(f[W]).."="..__NAME(Z[S[W]]).."; r"..tostring(f[W+1]),__NAME(Z[S[W+1]]),W);',
 62: '__OPLOG("RET1",__NAME(Z[S[W]]),W);',
 86: '__OPLOG("RET2",__NAME(Z[R[W]])..","..__NAME(Z[f[W]]),W);',
 98: '__OPLOG("RET0","",W);',
 36: '__OPLOG("CALL36",__NAME(Z[S[W]]).."()",W);',
 52: '__OPLOG("CALL52",__NAME(Z[S[W]]).."()",W);',
 66: '__OPLOG("CALL66",__NAME(Z[R[W]]).."("..__NAME(Z[f[W]])..")",W);',
 72: '__OPLOG("CALL72",__NAME(Z[R[W]]).."("..__NAME(m[W])..")",W);',
 84: '__OPLOG("CALL84",__NAME(Z[f[W]]).."(...)",W);',
 92: '__OPLOG("CALL92",__NAME(Z[S[W]]).."("..__NAME(Z[S[W]+1])..","..__NAME(Z[S[W]+2])..")",W);',
 97: '__OPLOG("CALL97",__NAME(Z[f[W]]).."()",W);',
}
src2 = vmmap.instrument(src, disp, probes, root=root)
if len(sys.argv) > 3 and sys.argv[3] == 'post':
    open('_tmp_src.luau', 'w', encoding='latin-1', newline='').write(src2)
    root2 = vmmap.load_ast('_tmp_src.luau')
    src2 = vmmap.instrument_post(src2, disp, root2, lambda op, dst: '__OPLOG("op%d r"..tostring(%s),__NAME(%s),W);' % (op, dst[2:-1], dst))
import re as _re
_k = [0]
def _rep(m):
    _k[0] += 1
    extra = ''
    return m.group(0) + extra + 'if not __SEEN[x] then __SEEN[x]=1;__OPLOG("PROTO%d",tostring(x),W) end;' % _k[0]
src2 = _re.sub(r'while true do local ([A-Za-z_]+)=([A-Za-z_]+)\[([A-Za-z_]+)\];', _rep, src2)
open('h.luau', 'w', encoding='latin-1', newline='\n').write(deob.build_harness(src2, {'oplog': 3000000, 'time_budget': 20}))
