"""direct.py N OUT.cnf [aA] [disjoint] [sym=CYCLES] [lsym=CYCLES] [lswap=CYCLES] [k9] [k5l] [k33l]

CNF for a biplanar graph U on N labelled vertices with independence number at most A (default 2):
two layers, each planar by Schnyder's theorem (three linear orders), and every (A+1)-set spans an
edge of U. Options: disjoint (no edge in both layers); sym= (U invariant under the permutation given
by its cycles, e.g. 0,1,2;3,4,5); lsym= (each layer invariant); lswap= (the permutation maps layer 0
to layer 1 and back); k9 (no 9-clique, implied but added); k5l, k33l (no K5, no K3,3 inside one
layer, implied by planarity). OUT.cnf.map lists "layer a b variable".
"""
import sys, itertools
n=int(sys.argv[1]); out=sys.argv[2]
opts=set(sys.argv[3:])
V=range(n)
nv=0
def new():
    global nv; nv+=1; return nv
cl=[]
pairs=list(itertools.combinations(V,2))
x={}
for L in (0,1):
    for p in pairs: x[L,p]=new()
u={}
for p in pairs:
    u[p]=new()
    cl.append([-u[p],x[0,p],x[1,p]]); cl.append([u[p],-x[0,p]]); cl.append([u[p],-x[1,p]])
def P(a,b): return (a,b) if a<b else (b,a)
# alpha(U)<=A
A=2
for t in opts:
    if t.startswith('a') and t[1:].isdigit(): A=int(t[1:])
for S in itertools.combinations(V,A+1):
    cl.append([u[p] for p in itertools.combinations(S,2)])
# orders
o={}
for L in (0,1):
    for i in range(3):
        for a,b in pairs: o[L,i,a,b]=new()
def lt(L,i,a,b):  # literal: a before b in order i of layer L
    return o[L,i,a,b] if a<b else -o[L,i,b,a]
for L in (0,1):
    for i in range(3):
        for a,b,c in itertools.permutations(V,3):
            if a<b and a<c:  # each 3-cycle once per orientation class
                pass
            cl.append([-lt(L,i,a,b),-lt(L,i,b,c),lt(L,i,a,c)])
# Schnyder condition
for L in (0,1):
    for a,b in pairs:
        for w in V:
            if w in (a,b): continue
            ys=[]
            for i in range(3):
                y=new(); ys.append(y)
                cl.append([-y,lt(L,i,a,w)]); cl.append([-y,lt(L,i,b,w)])
            cl.append([-x[L,(a,b)]]+ys)
# symmetry: an edge in both layers is pointless (keep layers disjoint)
if 'disjoint' in opts:
    for p in pairs: cl.append([-x[0,p],-x[1,p]])
# symmetry: U invariant under the permutation given as sym=c1;c2;... (cycles, comma-separated)
for t in opts:
    if t.startswith('sym='):
        perm=list(V)
        for cyc in t[4:].split(';'):
            c=list(map(int,cyc.split(',')))
            for i in range(len(c)): perm[c[i]]=c[(i+1)%len(c)]
        for a,b in pairs:
            q=(min(perm[a],perm[b]),max(perm[a],perm[b]))
            cl.append([-u[a,b],u[q]]); cl.append([u[a,b],-u[q]])
for t in opts:
    if t.startswith('lsym=') or t.startswith('lswap='):
        perm=list(V)
        for cyc in t.split('=',1)[1].split(';'):
            c=list(map(int,cyc.split(',')))
            for i in range(len(c)): perm[c[i]]=c[(i+1)%len(c)]
        sw=t.startswith('lswap=')
        for a,b in pairs:
            q=(min(perm[a],perm[b]),max(perm[a],perm[b]))
            for L in (0,1):
                M=1-L if sw else L
                cl.append([-x[L,(a,b)],x[M,q]]); cl.append([x[L,(a,b)],-x[M,q]])
# planarity of each layer: no K5 and no K3,3 inside one layer (implied by Kuratowski, may help)
if 'k5l' in opts:
    for L in (0,1):
        for S in itertools.combinations(V,5):
            cl.append([-x[L,p] for p in itertools.combinations(S,2)])
if 'k33l' in opts:
    for L in (0,1):
        for A in itertools.combinations(V,3):
            rest=[v for v in V if v not in A and v>A[0]]
            for B in itertools.combinations(rest,3):
                cl.append([-x[L,P(a,b)] for a in A for b in B])
# K9-free union (implied, helps)
if 'k9' in opts:
    for S in itertools.combinations(V,9):
        cl.append([-u[p] for p in itertools.combinations(S,2)])
# min U-degree >= 9 implied by K9-free + alpha<=2; add as: for each v, among any 9 others... skip
with open(out,'w') as f:
    f.write(f"p cnf {nv} {len(cl)}\n")
    for c in cl: f.write(' '.join(map(str,c))+' 0\n')
# map for decoding
with open(out+'.map','w') as f:
    for (L,p),v in x.items(): f.write(f"{L} {p[0]} {p[1]} {v}\n")
print(nv,len(cl))
