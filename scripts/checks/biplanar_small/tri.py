"""Enumerate unlabeled triangulations on n vertices by random edge flips (collect WL-hash + iso classes)."""
import sys, random, networkx as nx, pickle
n = int(sys.argv[1]); target = int(sys.argv[2])
# start: a triangulation built by stacking
faces = {(0, 1, 2), (0, 2, 1)}
G = nx.Graph(); G.add_edges_from([(0, 1), (1, 2), (0, 2)])
F = [(0, 1, 2), (0, 2, 1)]
for v in range(3, n):
    a, b, c = F.pop(random.randrange(len(F))); F += [(a, b, v), (b, c, v), (c, a, v)]; G.add_edges_from([(a, v), (b, v), (c, v)])
classes = []
def add(G):
    for H in classes:
        if nx.faster_could_be_isomorphic(G, H) and nx.is_isomorphic(G, H): return False
    classes.append(G.copy()); return True
add(G); steps = 0
while len(classes) < target and steps < 2000000:
    steps += 1
    a, b = random.choice(list(G.edges()))
    common = [x for x in nx.common_neighbors(G, a, b)]
    # in a triangulation the two faces on ab are triangles abx, aby with x,y common neighbours; flip only if exactly the face pair is determined: use planar embedding
    emb = nx.check_planarity(G)[1]
    x = emb[a][b]['cw']; y = emb[a][b]['ccw']
    if x == y or G.has_edge(x, y): continue
    if min(G.degree(a), G.degree(b)) <= 3: continue
    G.remove_edge(a, b); G.add_edge(x, y)
    if not nx.check_planarity(G)[0]: G.remove_edge(x, y); G.add_edge(a, b); continue
    add(G)
print(n, len(classes), 'steps', steps)
pickle.dump(classes, open(f'tri{n}.pkl', 'wb'))
