"""sms_stab.py n p s1,..,sp dmin out.enc [flags]: the Turan-stability model of scripts/stab2.py for SAT modulo
symmetries (smsg --directed --thickness2 F --initial-partition s1 .. sp). Arc variables come first in SMS's
order; a pair is in layer 1 iff both arcs are present, in layer 2 iff only the lower arc (higher -> lower vertex)
is; planarity of both layers is left to the thickness-two propagator, symmetry breaking to SMS's minimality
check (permutations inside parts). Flags: e = Euler bounds per layer on parts, pairs of parts, part + vertex; s = Schnyder orders for both layers."""
import sys, itertools
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
n, p = int(sys.argv[1]), int(sys.argv[2]); sizes = list(map(int, sys.argv[3].split(','))); dmin = int(sys.argv[4]); out = sys.argv[5]
FL = set(sys.argv[6]) if len(sys.argv) > 6 else set('e')
part = []
for i, s in enumerate(sizes): part += [i] * s
P = [[v for v in range(n) if part[v] == i] for i in range(p)]
arc = {}; k = 0
for u, v in itertools.permutations(range(n), 2): k += 1; arc[u, v] = k
pool = IDPool(start_from=k + 1); cls = []
pairs = list(itertools.combinations(range(n), 2))
def E(a, b): a, b = min(a, b), max(a, b); return arc[b, a]          # lower arc = edge of the union
def L1(a, b): a, b = min(a, b), max(a, b); return arc[a, b]         # upper arc (implies lower) = layer 1
L2v = {}
for a, b in pairs:
    cls.append([-arc[a, b], arc[b, a]])
    y = pool.id(('L2', a, b)); L2v[a, b] = y                        # y <-> lower and not upper
    cls += [[-y, arc[b, a]], [-y, -arc[a, b]], [y, -arc[b, a], arc[a, b]]]
def L2(a, b): return L2v[min(a, b), max(a, b)]
def card(lits, k, kind):
    f = {'le': CardEnc.atmost, 'ge': CardEnc.atleast}[kind](lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter)
    cls.extend(f.clauses)
for S in itertools.combinations(range(n), p + 1): cls.append([E(a, b) for a, b in itertools.combinations(S, 2)])
for Q in P:
    if len(Q) >= 9:
        for S in itertools.combinations(Q, 9): cls.append([-E(a, b) for a, b in itertools.combinations(S, 2)])
qs, r = divmod(n, p); T = (n * n - sum(s * s for s in [qs + 1] * r + [qs] * (p - r))) // 2
lits = []
for a, b in pairs:
    if part[a] == part[b]:
        for _ in range(2):
            c = pool.id(('copy', len(lits))); cls.append([E(a, b), c]); lits.append(c)
    else: lits.append(-E(a, b))
card(lits, T, 'le')
for v in range(n):
    for j in range(p):
        if j != part[v]: card([-E(v, u) for u in P[part[v]] if u != v] + [E(v, u) for u in P[j]], sizes[j], 'le')
    if dmin: card([E(v, u) for u in range(n) if u != v], dmin, 'ge')
for L in (L1, L2):
    card([L(a, b) for a, b in pairs], 3 * n - 6, 'le')
    if 'e' in FL:
        sets = [Q for Q in P if len(Q) >= 3] + [sorted(Q + R) for Q, R in itertools.combinations(P, 2)]
        sets += [sorted(Q + [v]) for Q in P if len(Q) >= 2 for v in range(n) if v not in Q]
        for S in sets: card([L(a, b) for a, b in itertools.combinations(S, 2)], 3 * len(S) - 6, 'le')
        for Q, R in itertools.combinations(P, 2):
            if len(Q) + len(R) >= 3: card([L(a, b) for a in Q for b in R], 2 * (len(Q) + len(R)) - 4, 'le')
if 't' in FL:  # layer 1 = a whole triangulation T1 (WLOG: U = T1 u T2, layer 2 = T2 minus T1): 3n-6 edges, every
    # layer-1 edge in two layer-1 triangles, layer-1 degree >= 3; every layer-2 edge has two common U-neighbours
    card([L1(a, b) for a, b in pairs], 3 * n - 6, 'ge')
    for v in range(n): card([L1(min(v, u), max(v, u)) for u in range(n) if u != v], 3, 'ge')
    for a, b in pairs:
        for L, tag in ((L1, 'T1'), (E, 'T2')):
            ts = []
            for x in range(n):
                if x in (a, b): continue
                t = pool.id((tag, a, b, x)); ts.append(t); cls.append([-t, L(a, x)]); cls.append([-t, L(b, x)])
            trig = L1(a, b) if tag == 'T1' else L2(a, b)
            f = CardEnc.atleast(lits=ts, bound=2, vpool=pool, encoding=EncType.seqcounter)
            sel = pool.id(('sel', tag, a, b))
            cls.append([-trig, sel])
            for c in f.clauses: cls.append([-sel] + c)
if 'T' in FL:  # both layers as full triangulations: T1 = double arcs (3n-6 edges); T2 = lower-only arcs plus the
    # double-arc pairs flagged B (T1 and T2 may share edges). Relaxation-sound: planarity of T2 is only checked on the
    # lower-only part by the propagator, but every rule below holds for genuine T1, T2.
    Bv, T2v = {}, {}
    for a, b in pairs:
        Bv[a, b] = pool.id(('B', a, b)); cls.append([-Bv[a, b], L1(a, b)])
        t = pool.id(('T2', a, b)); T2v[a, b] = t
        cls += [[-t, L2(a, b), Bv[a, b]], [t, -L2(a, b)], [t, -Bv[a, b]]]
    def T2(a, b): return T2v[min(a, b), max(a, b)]
    for L, tag in ((L1, 'R1'), (T2, 'R2')):
        card([L(a, b) for a, b in pairs], 3 * n - 6, 'ge'); card([L(a, b) for a, b in pairs], 3 * n - 6, 'le')
        for v in range(n): card([L(min(v, u), max(v, u)) for u in range(n) if u != v], 3, 'ge')
        sets = [Q for Q in P if len(Q) >= 3] + [sorted(Q + R) for Q, R in itertools.combinations(P, 2)]
        sets += [sorted(Q + [v]) for Q in P if len(Q) >= 2 for v in range(n) if v not in Q]
        for S in sets: card([L(a, b) for a, b in itertools.combinations(S, 2)], 3 * len(S) - 6, 'le')
        for a, b in pairs:
            ts = []
            for x in range(n):
                if x in (a, b): continue
                t = pool.id((tag, a, b, x)); ts.append(t); cls.append([-t, L(a, x)]); cls.append([-t, L(b, x)])
            f = CardEnc.atleast(lits=ts, bound=2, vpool=pool, encoding=EncType.seqcounter)
            sel = pool.id(('sel', tag, a, b)); cls.append([-L(a, b), sel])
            for c in f.clauses: cls.append([-sel] + c)
if 's' in FL:  # Schnyder: three linear orders per layer, every layer edge ab is below every other vertex x in some order
    for l, L in enumerate((L1, L2)):
        O = {}
        for i in range(3):
            for a, b in pairs: O[i, a, b] = pool.id(('O', l, i, a, b))
        def o(i, a, b): return O[i, a, b] if a < b else -O[i, b, a]
        for i in range(3):
            for a, b, c in itertools.permutations(range(n), 3): cls.append([-o(i, a, b), -o(i, b, c), o(i, a, c)])
        for a, b in pairs:
            for x in range(n):
                if x in (a, b): continue
                zs = []
                for i in range(3):
                    z = pool.id(('Z', l, a, b, x, i)); zs.append(z)
                    cls.append([-z, o(i, a, x)]); cls.append([-z, o(i, b, x)])
                cls.append([-L(a, b)] + zs)
with open(out, 'w') as f:
    f.write(f'p cnf {pool.top} {len(cls)}\n')
    for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
print('vars', pool.top, 'clauses', len(cls), file=sys.stderr)
