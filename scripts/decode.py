"""decode.py LINE SOLUTION : read a Kissat model of the CNF for the line "w|edges" and check it.

Prints the two layers, checks that each is planar and that together they cover F[w], and reports
the order, the edge count and the independence number of F[w] with its graph6 string.
"""
import sys
from itertools import combinations
import networkx as nx

line, sol = sys.argv[1], sys.argv[2]
ws, fes = line.split('|')
w = [int(x) for x in ws.split(',')]
fe = [] if fes == '-' else [tuple(int(y) for y in e.split('-')) for e in fes.split(',')]
bag = [i for i, k in enumerate(w) for _ in range(k)]
n = len(bag)
fadj = {(a, b) for a, b in fe} | {(b, a) for a, b in fe}
G = nx.Graph()
G.add_nodes_from(range(n))
for a, b in combinations(range(n), 2):
    if bag[a] == bag[b] or (bag[a], bag[b]) in fadj:
        G.add_edge(a, b)
true = set()
for t in open(sol).read().split():
    if t.lstrip('-').isdigit() and int(t) > 0:
        true.add(int(t))
layers = []
for l in range(2):
    L = nx.Graph()
    L.add_nodes_from(range(n))
    for a, b in G.edges():
        a, b = min(a, b), max(a, b)
        if 6 * n * n + (l * n + a) * n + b + 1 in true:
            L.add_edge(a, b)
    layers.append(L)
ok = all(nx.check_planarity(L)[0] for L in layers)
cover = all(layers[0].has_edge(a, b) or layers[1].has_edge(a, b) for a, b in G.edges())
alpha = max(len(c) for c in nx.find_cliques(nx.complement(G)))
print('n', n, 'edges', G.number_of_edges(), 'alpha', alpha, 'planar layers', ok, 'cover', cover)
for l, L in enumerate(layers):
    print('layer', l, sorted(L.edges()))
print('graph6', nx.to_graph6_bytes(G, header=False).decode().strip())
