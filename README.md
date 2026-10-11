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
  normalisation, and K9 contraction clauses for 8-cliques).
- `data/queue1.txt` lists 1316 candidates `w|edges of F` on 18 vertices: blow-ups of the
  complements of the Andrásfai graph And(4), of the Grötzsch graph and of two 8-vertex cores, kept
  only when the complement of `F[w]` has no homomorphism to the five-cycle (a necessary condition
  by the theorem on five-cycle blow-ups in creelie/probable-fortnight).
- `scripts/shard.sh` runs one sixteenth of the queue with Kissat; `scripts/decode.py` checks a found
  drawing (both layers planar, every edge covered) with NetworkX.
- `.github/workflows/blowups.yml` runs the 16 shards.

Author: Deep Bhattacharjee (EGSPL).
