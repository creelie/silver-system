"""mklits.py W OUT [edge] : literal map for bipprop. Default: the Schnyder encoding of DumpF/Encode
(lay l a b = 6n^2 + (l n + a) n + b + 1). With 'edge': base.py's edge variables (OUT.map)."""
import sys, itertools
w = [int(t) for t in sys.argv[1].split(',')]; out = sys.argv[2]; K = len(w)
bag = [i for i, k in enumerate(w) for _ in range(k)]; n = len(bag)
E = [(a, b) for a, b in itertools.combinations(range(n), 2) if (bag[a] - bag[b]) % K in (0, 1, K - 1)]
L = []
if 'edge' in sys.argv[3:]:
    for line in open(out + '.map').read().split('\n')[1:]:
        if line.strip():
            v, a, b = map(int, line.split()); L += [(v, 0, a, b), (-v, 1, a, b)]
else:
    for a, b in E:
        for l in (0, 1): L.append((6 * n * n + (l * n + a) * n + b + 1, l, a, b))
with open(out + '.lits', 'w') as f:
    f.write('%d %d\n' % (n, len(L)))
    for t in L: f.write('%d %d %d %d\n' % t)
