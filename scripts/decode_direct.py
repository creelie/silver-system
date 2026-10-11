"""decode_direct.py CNF SOLUTION [G6] : decode a model of encode/direct.py, check both layers are planar,
and print the edge counts, the independence number and the clique number of the union."""
import sys, networkx as nx, itertools
cnf, sol = sys.argv[1], sys.argv[2]
val=set()
for line in open(sol):
    if line.startswith('v'):
        for t in line.split()[1:]:
            t=int(t)
            if t>0: val.add(t)
L=[nx.Graph(),nx.Graph()]
n=0
for line in open(cnf+'.map'):
    l,a,b,v=map(int,line.split()); n=max(n,b+1)
    if v in val: L[l].add_edge(a,b)
for g in L: g.add_nodes_from(range(n))
U=nx.compose(L[0],L[1])
pl=[nx.check_planarity(g)[0] for g in L]
indep3=max(len(c) for c in nx.find_cliques(nx.complement(U)))
w=max(len(c) for c in nx.find_cliques(U))
print('n',n,'layers planar',pl,'edges',L[0].number_of_edges(),L[1].number_of_edges(),'U',U.number_of_edges(),'alpha',indep3,'omega',w)
if len(sys.argv)>3:
    open(sys.argv[3],'w').write(nx.to_graph6_bytes(U,header=False).decode())
    for i,g in enumerate(L): open(sys.argv[3]+f'.L{i}','w').write(' '.join(f'{a}-{b}' for a,b in g.edges())+'\n')
