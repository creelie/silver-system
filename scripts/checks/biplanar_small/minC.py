"""Enumerate edge-minimal complement shapes C on <= n vertices (up to iso, <= maxe edges) such that
nu(C - v) >= 2 for every vertex v (i.e. K_n - C has no K9 and no K10-K3 subgraph)."""
import networkx as nx, itertools, sys, pickle
from networkx.algorithms.matching import max_weight_matching
n = int(sys.argv[1]); maxe = int(sys.argv[2])
def nu(g): return len(nx.max_weight_matching(g, maxcardinality=True))
def good(C):
    for v in range(n):
        h = C.copy(); h.remove_node(v)
        if nu(h) < 2: return False
    return True
def canon_add(lst, g):
    for h in lst:
        if nx.faster_could_be_isomorphic(g, h) and nx.is_isomorphic(g, h): return False
    lst.append(g); return True
level = [nx.empty_graph(n)]; minimal = []
for e in range(1, maxe + 1):
    nxt = []
    for g in level:
        for a, b in itertools.combinations(range(n), 2):
            if g.has_edge(a, b): continue
            h = g.copy(); h.add_edge(a, b)
            if any(nx.is_isomorphic(nx.Graph(h.edges()), nx.Graph(m.edges())) or False for m in []): pass
            canon_add(nxt, h)
    # split
    keep = []
    for h in nxt:
        # skip supersets of known minimal shapes
        sup = False
        for m in minimal:
            GM = nx.algorithms.isomorphism.GraphMatcher(h, m)
            if any(True for _ in GM.subgraph_monomorphisms_iter()): sup = True; break
        if sup: continue
        if good(h): minimal.append(h)
        else: keep.append(h)
    level = keep
    print('edges', e, 'minimal so far', len(minimal), 'frontier', len(level), flush=True)
pickle.dump([sorted(m.edges()) for m in minimal], open(f'minC{n}_{maxe}.pkl', 'wb'))
for m in minimal: print(sorted(m.edges()))
