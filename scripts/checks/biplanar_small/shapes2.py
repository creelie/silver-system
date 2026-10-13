"""shapes2.py n spec...: is K_n - C biplanar? Enumerate labeled copies of C in K_n once, then for each triangulation T
test whether comp(T) minus the copy is planar."""
import pickle, networkx as nx, itertools, sys, time
n = int(sys.argv[1]); T = pickle.load(open(f'tri{n}.pkl', 'rb')); comps = [nx.complement(t) for t in T]
def copies(C):
    vs = sorted(set(v for e in C for v in e)); out = set()
    for img in itertools.permutations(range(n), len(vs)):
        f = dict(zip(vs, img)); out.add(frozenset(tuple(sorted((f[a], f[b]))) for a, b in C))
    return list(out)
for spec in sys.argv[2:]:
    C = [tuple(map(int, e.split('-'))) for e in spec.split(',')]; t0 = time.time()
    cps = copies(C); res = None
    for ti, c in enumerate(comps):
        cache = set()
        for cp in cps:
            D = frozenset(e for e in cp if c.has_edge(*e))
            if D in cache: continue
            cache.add(D); h = c.copy(); h.remove_edges_from(D)
            if nx.check_planarity(h)[0]: res = (ti, sorted(D)); break
        if res: break
    print(n, spec, 'copies', len(cps), 'BIPLANAR' if res else 'NOT biplanar', res, round(time.time() - t0), 's', flush=True)
