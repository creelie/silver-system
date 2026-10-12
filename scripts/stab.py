"""stab.py n p s1,s2,..,sp out.cnf [dmin] [cube-file]

CNF for: a graph U on n vertices that is the union of two plane triangulations (Schnyder orders, 3n-6
edges per layer), has independence number <= p, and whose complement H (K_{p+1}-free) has a vertex
partition into parts of the given sizes that is optimal for H in Furedi's stability theorem:
  * 2|M| + (cross pairs that are non-edges of U) <= t(n,p), where M = internal non-edges of U
    (Furedi: e(H) >= t(n,p) - t implies a p-partition with at most t internal edges of H; here
    t = t(n,p) - e(H) and e(H) = C(n,2) - e(U));
  * no vertex has fewer H-neighbours in another part than in its own (local optimality);
  * every vertex has U-degree >= dmin;
  * no 9 vertices of one part form a clique of U.
Symmetry breaking: lexicographic rows inside each part (Codish et al.), and edge 01 in layer 0.
"""
import sys, itertools
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

n = int(sys.argv[1]); p = int(sys.argv[2]); sizes = list(map(int, sys.argv[3].split(',')))
out = sys.argv[4]; dmin = int(sys.argv[5]) if len(sys.argv) > 5 else 0
assert sum(sizes) == n and len(sizes) == p
part = []
for i, s in enumerate(sizes): part += [i] * s
P = [[v for v in range(n) if part[v] == i] for i in range(p)]
pool = IDPool(); cls = []
def E(a, b):
    if a > b: a, b = b, a
    return pool.id(('E', a, b))
def L(l, a, b):
    if a > b: a, b = b, a
    return pool.id(('L', l, a, b))
def O(l, i, a, b):  # a before b in order i of layer l
    return pool.id(('O', l, i, a, b)) if a < b else -pool.id(('O', l, i, b, a))
pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
for a, b in pairs: E(a, b)
for l in range(2):
    for a, b in pairs: L(l, a, b)
for l in range(2):
    for i in range(3):
        for a, b in pairs: O(l, i, a, b)
# linear orders
for l in range(2):
    for i in range(3):
        for a, b, c in itertools.permutations(range(n), 3):
            cls.append([-O(l, i, a, b), -O(l, i, b, c), O(l, i, a, c)])
# layers and union
for a, b in pairs:
    cls.append([-E(a, b), L(0, a, b), L(1, a, b)])
    for l in range(2): cls.append([-L(l, a, b), E(a, b)])
# Schnyder condition
for l in range(2):
    for a, b in pairs:
        for x in range(n):
            if x in (a, b): continue
            zs = []
            for i in range(3):
                z = pool.id(('Z', l, a, b, x, i)); zs.append(z)
                cls.append([-z, O(l, i, a, x)]); cls.append([-z, O(l, i, b, x)])
            cls.append([-L(l, a, b)] + zs)
def card(lits, k, kind):
    f = {'le': CardEnc.atmost, 'ge': CardEnc.atleast, 'eq': CardEnc.equals}[kind](
        lits=lits, bound=k, vpool=pool, encoding=EncType.seqcounter if kind != 'eq' else EncType.totalizer)
    cls.extend(f.clauses)
# triangulations
for l in range(2): card([L(l, a, b) for a, b in pairs], 3 * n - 6, 'eq')
# Euler inside one layer: at most 3s-6 edges inside a part, 2s-4 between two parts (bipartite)
for l in range(2):
    for Q in P:
        if len(Q) >= 3: card([L(l, a, b) for a, b in itertools.combinations(Q, 2)], 3 * len(Q) - 6, 'le')
    for Q, R in itertools.combinations(P, 2):
        if len(Q) + len(R) >= 3: card([L(l, a, b) for a in Q for b in R], 2 * (len(Q) + len(R)) - 4, 'le')
# independence number <= p
for S in itertools.combinations(range(n), p + 1):
    cls.append([E(a, b) for a, b in itertools.combinations(S, 2)])
# no 9-clique inside a part
for Q in P:
    if len(Q) >= 9:
        for S in itertools.combinations(Q, 9):
            cls.append([-E(a, b) for a, b in itertools.combinations(S, 2)])
# Furedi stability with t = t(n,p) - e(H)
def turan(n, p):
    q, r = divmod(n, p); sz = [q + 1] * r + [q] * (p - r)
    return (n * n - sum(s * s for s in sz)) // 2
T = turan(n, p)
lits = []
for a, b in pairs:
    if part[a] == part[b]: lits += [-E(a, b), -E(a, b)]
    else: lits.append(-E(a, b))
# duplicates are fine for the sequential counter only with distinct variables: use copies
dl = []
for x in lits:
    c = pool.id(('copy', len(dl))); dl.append(c); cls.append([-x, c])  # x -> c (c may be over-set; upper bound stays sound)
card(dl, T, 'le')
# local optimality
for v in range(n):
    i = part[v]
    for j in range(p):
        if j == i: continue
        card([-E(v, u) for u in P[i] if u != v] + [E(v, u) for u in P[j]], sizes[j], 'le')
# minimum degree
if dmin > 0:
    for v in range(n): card([E(v, u) for u in range(n) if u != v], dmin, 'ge')
# symmetry breaking: row i lex <= row j (columns other than i, j) for i < j in the same part
for Q in P:
    for i, j in itertools.combinations(Q, 2):
        cols = [k for k in range(n) if k not in (i, j)]
        prev = None  # prev: rows equal on the columns so far
        for k in cols:
            a, b = E(i, k), E(j, k)
            # if equal so far then a <= b
            cls.append(([-prev] if prev else []) + [-a, b])
            eq = pool.id(('eq', i, j, k))
            # eq <-> prev and (a == b); only the -> direction of "eq is implied" is needed
            cls.append(([-prev] if prev else []) + [a, b, eq])
            cls.append(([-prev] if prev else []) + [-a, -b, eq])
            prev = eq
if (0, 1) in pairs and part[0] == part[1]:
    cls.append([-E(0, 1), L(0, 0, 1)])
cube = sys.argv[6] if len(sys.argv) > 6 else None
nv = pool.top
with open(out, 'w') as f:
    f.write(f'p cnf {nv} {len(cls)}\n')
    for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
# variable map for decoding
with open(out + '.map', 'w') as f:
    for a, b in pairs: f.write(f'{a} {b} {E(a, b)} {L(0, a, b)} {L(1, a, b)}\n')
print('vars', nv, 'clauses', len(cls), 'T', T, file=sys.stderr)
