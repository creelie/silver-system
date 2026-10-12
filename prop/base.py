"""base.py SPEC OUT [sb] [nok] : base CNF for 'is G biplanar?' with edge variables.
SPEC is a C5 weight vector like 3,3,4,3,4 or a file with lines 'a b' (first line: n).
Variable i (1..m) is true iff edge i lies in layer 0. Clauses: no K5 or K3,3 of G inside a
layer (unless nok), at most 3n-6 edges per layer, edge 1 in layer 1, and with sb lex-leader
clauses for the transpositions of twins (vertices with the same closed or open neighbourhood).
Writes OUT.cnf and OUT.map (lines 'var a b')."""
import sys, itertools, os
from pysat.card import CardEnc, EncType
spec, out = sys.argv[1], sys.argv[2]; opts = set(sys.argv[3:])
if os.path.exists(spec):
    L = open(spec).read().split('\n'); n = int(L[0])
    E = sorted({(min(a, b), max(a, b)) for a, b in (map(int, l.split()) for l in L[1:] if l.strip())})
else:
    w = [int(t) for t in spec.split(',')]; K = len(w)
    bag = [i for i, k in enumerate(w) for _ in range(k)]; n = len(bag)
    E = [(a, b) for a, b in itertools.combinations(range(n), 2) if (bag[a] - bag[b]) % K in (0, 1, K - 1)]
m = len(E); eid = {e: i + 1 for i, e in enumerate(E)}; Es = set(E)
adj = lambda a, b: (min(a, b), max(a, b)) in Es
X = lambda a, b: eid[(min(a, b), max(a, b))]
N = [set(v for v in range(n) if adj(u, v)) for u in range(n)]
cls = []
if 'nok' not in opts:
    for S in itertools.combinations(range(n), 5):
        if all(adj(a, b) for a, b in itertools.combinations(S, 2)):
            ps = [X(a, b) for a, b in itertools.combinations(S, 2)]; cls += [[-x for x in ps], ps]
    for A in itertools.combinations(range(n), 3):
        rest = [v for v in range(n) if v not in A and v > A[0] and all(adj(v, a) for a in A)]
        for B in itertools.combinations(rest, 3):
            ps = [X(a, b) for a in A for b in B]; cls += [[-x for x in ps], ps]
top = m
for lits in (list(range(1, m + 1)), [-i for i in range(1, m + 1)]):
    if m > 3 * n - 6:
        enc = CardEnc.atmost(lits=lits, bound=3 * n - 6, top_id=top, encoding=EncType.seqcounter)
        cls += enc.clauses; top = max(top, enc.nv)
cls.append([-1])
if 'sb' in opts:
    twins = [(u, v) for u, v in itertools.combinations(range(n), 2) if N[u] - {v} == N[v] - {u}]
    for u, v in twins:
        sig = list(range(n)); sig[u], sig[v] = v, u
        ys = [X(sig[a], sig[b]) for a, b in E]; xs = list(range(1, m + 1)); eq = None
        for x, y in zip(xs, ys):
            if x == y: continue
            cls.append([-x, y] if eq is None else [-eq, -x, y])
            top += 1; ne = top
            cls += [[-x, -y, ne], [x, y, ne]] if eq is None else [[-eq, -x, -y, ne], [-eq, x, y, ne]]
            eq = ne
with open(out + '.cnf', 'w') as f:
    f.write('p cnf %d %d\n' % (top, len(cls)))
    for c in cls: f.write(' '.join(map(str, c)) + ' 0\n')
with open(out + '.map', 'w') as f:
    f.write('%d %d\n' % (n, m))
    for (a, b), i in eid.items(): f.write('%d %d %d\n' % (i, a, b))
print(out, 'n', n, 'm', m, 'vars', top, 'clauses', len(cls))
