# Biplanar graphs with independence number 2 on 18 vertices

A search workspace for Open Problem 2 of Gethner and Sulanke: is there a biplanar graph whose
independence ratio is below 2/17? Szeider (arXiv:2609.28102) showed that a biplanar graph with
independence number 2 has at most 18 vertices, so an 18-vertex example would answer the question.
Nothing here is a result yet: the workflow tests families of candidates and records which ones are
not biplanar.

The candidates are clique blow-ups `F[w]`: each vertex `i` of a small graph `F` with independence
number 2 becomes a clique of `w_i` vertices, and two cliques are completely joined when their
vertices are adjacent in `F`. Then `F[w]` has independence number 2.

- `encode/DumpF.lean` writes the CNF of "`F[w]` is biplanar" (three Schnyder orders per layer, twin
  normalisation, K9 contraction clauses for 8-cliques, and clauses implied by the planarity of each
  layer: no K5 or K3,3 inside a layer, at most 3s-6 edges of an s-clique and 3n-6 edges in all).
- `data/queue1.txt` lists 1316 candidates `w|edges of F` on 18 vertices: blow-ups of the
  complements of the Andrásfai graph And(4), of the Grötzsch graph and of two 8-vertex cores, kept
  only when the complement of `F[w]` has no homomorphism to the five-cycle (a necessary condition
  by the theorem on five-cycle blow-ups in creelie/probable-fortnight).
- `scripts/shard.sh` runs one sixteenth of the queue with Kissat; `scripts/decode.py` checks a found
  drawing (both layers planar, every edge covered) with NetworkX.
- `.github/workflows/blowups.yml` runs the 16 shards; `direct.yml` runs symmetric direct searches
  (`encode/direct.py`, `data/direct.txt`). Both are started by hand.
- `.github/workflows/enum18.yml` enumerates the possible complements H on 18 vertices with nauty's
  geng and the prune hook `enum/prune.c` (built by `scripts/build_geng.sh`). The hook's last
  condition uses the theorem that no clique blow-up of the five-cycle with 17 or more vertices and
  clique number at most 8 is biplanar.
- `.github/workflows/c5probe.yml` races four solver configurations (`scripts/race.sh`) on the
  five-cycle blow-ups with 17 vertices whose formulas were slow in creelie/probable-fortnight.

Author: Deep Bhattacharjee (EGSPL).
