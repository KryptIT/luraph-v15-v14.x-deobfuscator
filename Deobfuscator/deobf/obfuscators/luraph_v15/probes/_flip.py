# developer helper: invert one boolean result in the main proto and report the run status
import sys, os, subprocess, re
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..'))
import harness as deob
from obfuscators.luraph_v15 import vmmap
from obfuscators.luraph_v15.driver import patch_entries
deob.patch_entries = patch_entries
path = sys.argv[1]
targets = [(int(a.split(':')[0]), int(a.split(':')[1]), int(a.split(':')[2])) for a in sys.argv[2:]]  # loop:op:pc
src = open(path, encoding='latin-1', newline='').read()
root = vmmap.load_ast(path)
lines = src.split('\n')
disps = vmmap.find_dispatchers(root)
for loop, op, pc in targets:
    d = disps[loop - 1]
    reg, pcv = vmmap.loop_names(d)
    blk = vmmap.resolve(d['tree'], d['op'], op)
    text = vmmap.text_of(lines, blk)
    m = re.match(r"\s*(" + reg + r"\[[A-Za-z_]+\[" + pcv + r"\]\])=", text)
    dst = m.group(1)
    code = ' if %s==%d and __P[x]==1 then %s=not %s end ' % (pcv, pc, dst, dst)
    variant = list(lines)
    l1, c1, l2, c2 = vmmap.loc(blk)
    variant[l2] = variant[l2][:c2] + code + variant[l2][c2:]
    s2 = '\n'.join(variant)
    s2 = re.sub(r"while true do local ([A-Za-z_]+)=([A-Za-z_]+)\[([A-Za-z_]+)\];",
                lambda m: m.group(0) + 'if not __P[x] then __P.n=__P.n+1;__P[x]=__P.n;end;', s2)
    open('hf.luau', 'w', encoding='latin-1', newline='\n').write(deob.build_harness(s2, {'flip_probe': True, 'time_budget': 30}))
    try:
        out = subprocess.run([deob.find_luau(), 'hf.luau'], capture_output=True, timeout=60).stdout.decode('utf-8', 'replace')
    except subprocess.TimeoutExpired:
        out = 'TIMEOUT'
    st = re.search(r'-- run status: ([^\r\n]*)', out)
    n = re.search(r'-- (\d+) statements', out)
    print('flip L%d op%d pc%d ->' % (loop, op, pc), st.group(1) if st else out[-200:], '| stmts', n.group(1) if n else '?')
