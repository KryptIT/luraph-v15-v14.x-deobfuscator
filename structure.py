"""Rebuild structured control flow (while / numeric for / generic for / if-else) from lifted nodes."""
from ir import *


def negate(c):
    if isinstance(c, EUn) and c.op == 'not':
        return c.a
    if isinstance(c, EBin):
        inv = {'==': '~=', '~=': '=='}
        if c.op in inv:
            return EBin(inv[c.op], c.a, c.b)
    return EUn('not', c)


class Structurer:
    def __init__(self, proto, warn):
        self.P = proto
        self.nodes = proto.nodes
        self.warn = warn
        self.end_pos = proto.ninstr + 1

    # ---- jump helpers
    def is_jump(self, p):
        n = self.nodes.get(p)
        return n is not None and n.kind == 'stmts' and not n.stmts and n.next != p + n.size

    def chain(self, x):
        seen = []
        while x not in seen and len(seen) < 1000:
            seen.append(x)
            if self.is_jump(x):
                x = self.nodes[x].next
            else:
                break
        return seen

    def resolve(self, x):
        return self.chain(x)[-1]

    def jump_kind(self, target, ft, loops):
        rt = self.resolve(target)
        if ft is not None and rt == self.resolve(ft):
            return 'fall'
        if loops:
            lp = loops[-1]
            if rt == self.resolve(lp['exit']):
                return 'break'
            if rt == self.resolve(lp['cont']):
                return 'continue'
        return 'goto'

    def jump_stmt(self, target, ft, loops):
        k = self.jump_kind(target, ft, loops)
        if k == 'fall':
            return None
        if k == 'break':
            return SBreak()
        if k == 'continue':
            return SContinue()
        self.warn('unstructured jump to instruction %d' % target)
        return SGoto(target)

    def node_ending_at(self, start, end):
        """The node whose extent ends exactly at `end` (searching within [start, end))."""
        for q in range(end - 1, start - 1, -1):
            n = self.nodes.get(q)
            if n is not None:
                return n if q + n.size == end else None
        return None

    # ---- main
    def run(self):
        return self.struct(1, self.end_pos, None, [])

    def struct(self, start, end, ft, loops, skip_head=None):
        if ft is None:
            ft = end
        out = []
        pc = start
        while pc < end:
            node = self.nodes.get(pc)
            if node is None:
                pc += 1
                continue
            # ---------------- while loops (back-edge to pc)
            if pc != skip_head:
                j = None
                for q in range(end - 1, pc - 1, -1):
                    if self.is_jump(q) and pc in self.chain(self.nodes[q].next):
                        j = q
                        break
                if j is not None:
                    lp = {'head': pc, 'exit': j + 1, 'cont': pc}
                    cond = None
                    if node.kind == 'cond' and not node.pre and not node.tstmts and not node.fstmts:
                        c, T = self.norm_cond(node)
                        if c is not None and self.resolve(T) == self.resolve(j + 1):
                            cond = c
                    if cond is not None:
                        body = self.struct(pc + 2, j, j, loops + [lp])
                        out.append(SWhile(cond, body))
                    else:
                        body = self.struct(pc, j, j, loops + [lp], skip_head=pc)
                        out.append(SWhile(EConst(True), body))
                    pc = j + 1
                    continue
            k = node.kind
            if k == 'stmts':
                out.extend(node.stmts)
                nxt = pc + node.size
                if node.next != nxt:
                    t = self.nodes.get(node.next)
                    if not node.stmts and t is not None and t.kind == 'tforloop' and t.back == nxt:
                        a = t.a
                        lp = {'head': node.next, 'exit': t.exit, 'cont': node.next}
                        body = self.struct(nxt, node.next, node.next, loops + [lp])
                        out.append(SGenFor([EReg(a + 3 + i) for i in range(t.nvars)],
                                           [EReg(a), EReg(a + 1), EReg(a + 2)], body))
                        pc = t.exit
                        continue
                    js = self.jump_stmt(node.next, ft, loops)
                    if js is not None:
                        out.append(js)
                        break           # rest of range is unreachable
                pc = nxt
                continue
            if k == 'ret':
                out.extend(node.stmts)
                break
            if k == 'forprep':
                out.extend(node.pre)
                X = node.exit
                a = node.a
                lp = {'head': X - 1, 'exit': X, 'cont': X - 1}
                body = self.struct(pc + 1, X - 1, X - 1, loops + [lp])
                out.append(SNumFor(EReg(a + 3), EReg(a), EReg(a + 1), EReg(a + 2), body))
                pc = X
                continue
            if k == 'cond':
                out.extend(node.pre)
                c, T = self.norm_cond(node)
                if c is None:
                    self.warn('conditional at %d has no fall-through arm' % pc)
                    out.append(SIf(node.cond, node.tstmts + [SGoto(node.t)], node.fstmts + [SGoto(node.f)]))
                    pc += 2
                    continue
                tst, fst = (node.tstmts, node.fstmts) if c is node.cond else (node.fstmts, node.tstmts)
                body_start = pc + 2
                if body_start <= T <= end:
                    last = self.node_ending_at(body_start, T) if T > body_start else None
                    E = None
                    if last is not None and last.kind == 'stmts' and last.next != last.pos + last.size:
                        E = last.next
                        if not (T < E <= end or (E != T and self.resolve(E) == self.resolve(ft))):
                            E = None
                        elif self.jump_kind(E, ft, loops) in ('break', 'continue') and not (T < E <= end):
                            E = None
                    if E is not None:
                        else_end = E if T < E <= end else end
                        then = self.struct(body_start, T, E, loops)
                        els = self.struct(T, else_end, ft if else_end == end else else_end, loops)
                        out.append(SIf(c, tst + then, fst + els))
                        pc = else_end
                    else:
                        then = self.struct(body_start, T, T if T < end else ft, loops)
                        out.append(SIf(c, tst + then, list(fst)))
                        pc = T
                    continue
                jk = self.jump_kind(T, ft, loops)
                if jk == 'fall':
                    then = self.struct(body_start, end, ft, loops)
                    out.append(SIf(c, tst + then, list(fst)))
                    pc = end
                    continue
                js = SBreak() if jk == 'break' else SContinue() if jk == 'continue' else SGoto(T)
                if jk == 'goto':
                    self.warn('unstructured conditional jump to %d' % T)
                out.append(SIf(negate(c), fst + [js], []))
                out.extend(tst)
                pc = body_start
                continue
            if k == 'bad':
                out.append(SComment('could not decode instruction %d: %s' % (pc, node.msg)))
                pc += node.size
                continue
            # stray loop-closing nodes (should have been consumed)
            self.warn('unexpected %s at %d' % (k, pc))
            out.append(SComment('unexpected %s at %d' % (k, pc)))
            pc += node.size
        return out

    def norm_cond(self, node):
        pc = node.pos
        if node.t == pc + 2:
            return node.cond, node.f
        if node.f == pc + 2:
            return negate(node.cond), node.t
        return None, None
