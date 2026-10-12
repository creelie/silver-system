"""symlay.py W SIGMA OUT.cnf [k5k33] : look for a biplanar drawing of C5[W] whose second layer is sigma(first layer).

SIGMA is an automorphism given as a comma list of images of 0..n-1.  One planar layer L0 is encoded
with three Schnyder orders; every edge e needs e in L0 or sigma^-1(e) in L0.  A solution gives the
biplanar decomposition L0, sigma(L0).  Writes OUT.cnf and OUT.cnf.map (edge -> variable).
"""
import sys
from itertools import combinations

w = [int(x) for x in sys.argv[1].split(',')]
sig = [int(x) for x in sys.argv[2].split(',')]
out = sys.argv[3]
opts = set(sys.argv[4:])
bag = [i for i, k in enumerate(w) for _ in range(k)]
n = len(bag)
assert sorted(sig) == list(range(n))
K = len(w)


def adj(a, b):
    return a != b and (bag[a] - bag[b]) % K in (0, 1, K - 1)


E = [(a, b) for a, b in combinations(range(n), 2) if adj(a, b)]
for a, b in E:
    assert adj(sig[a], sig[b]), "sigma is not an automorphism"
inv = [0] * n
for i, s in enumerate(sig):
    inv[s] = i
nv = 0


def new():
    global nv
    nv += 1
    return nv


x = {e: new() for e in E}
o = {}
for i in range(3):
    for a, b in combinations(range(n), 2):
        o[i, a, b] = new()


def lt(i, a, b):
    return o[i, a, b] if a < b else -o[i, b, a]


C = []
for i in range(3):
    for a in range(n):
        for b in range(n):
            for c in range(n):
                if len({a, b, c}) == 3:
                    C.append([-lt(i, a, b), -lt(i, b, c), lt(i, a, c)])
for (a, b) in E:
    for v in range(n):
        if v in (a, b):
            continue
        zs = []
        for i in range(3):
            z = new()
            C.append([-z, lt(i, a, v)])
            C.append([-z, lt(i, b, v)])
            zs.append(z)
        C.append([-x[a, b]] + zs)
for (a, b) in E:
    p, q = inv[a], inv[b]
    e2 = (min(p, q), max(p, q))
    C.append([x[a, b], x[e2]])
# planarity of the layer: no K5 and no K3,3 among the edges of C5[W] in L0 (implied, may help)
if 'k5k33' in opts:
    for S in combinations(range(n), 5):
        if all(adj(a, b) for a, b in combinations(S, 2)):
            C.append([-x[p] for p in combinations(S, 2)])
    for A in combinations(range(n), 3):
        rest = [v for v in range(n) if v not in A and v > A[0] and all(adj(v, a) for a in A)]
        for B in combinations(rest, 3):
            C.append([-x[min(a, b), max(a, b)] for a in A for b in B])
with open(out, 'w') as f:
    f.write('p cnf %d %d\n' % (nv, len(C)))
    for c in C:
        f.write(' '.join(map(str, c)) + ' 0\n')
with open(out + '.map', 'w') as f:
    for e in E:
        f.write('%d %d %d\n' % (e[0], e[1], x[e]))
