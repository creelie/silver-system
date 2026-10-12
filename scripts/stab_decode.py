import sys, networkx as nx, itertools
sol=set(); 
for line in open(sys.argv[1]):
    if line.startswith('v'): sol.update(int(x) for x in line.split()[1:] if int(x)>0)
G=nx.Graph(); L=[nx.Graph(),nx.Graph()]
mp=[list(map(int,l.split())) for l in open(sys.argv[2])]
n=max(max(a,b) for a,b,*_ in mp)+1
for g in [G]+L: g.add_nodes_from(range(n))
for a,b,e,l0,l1 in mp:
    if e in sol: G.add_edge(a,b)
    if l0 in sol: L[0].add_edge(a,b)
    if l1 in sol: L[1].add_edge(a,b)
al=max(len(c) for c in nx.find_cliques(nx.complement(G))); om=max(len(c) for c in nx.find_cliques(G))
print('n',n,'e',G.number_of_edges(),'alpha',al,'omega',om,'layers',[l.number_of_edges() for l in L],'planar',[nx.check_planarity(l)[0] for l in L],
      'union ok', set(map(frozenset,G.edges()))==set(map(frozenset,L[0].edges()))|set(map(frozenset,L[1].edges())))
print(nx.to_graph6_bytes(G,header=False).decode().strip())
