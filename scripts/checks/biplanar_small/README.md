Which dense graphs on 9 to 11 vertices are biplanar, by exhaustion.

K_n - C is biplanar iff some triangulation T on n vertices has comp(T) minus a copy of C planar (extend one layer
to a triangulation). `tri.py n N` collects the N unlabeled triangulations on n vertices by random flips
(9: 50, 10: 233, 11: 1249, as in OEIS A000109) into tri<n>.pkl; `shapes2.py n spec` tries every labeled copy of C
against every triangulation, so "NOT biplanar" is a complete check. `minC.py n e` lists the edge-minimal shapes C
with at most e edges such that nu(C - v) >= 2 for every v (K_n - C has no K9 and no K10 - K3).

Results (12-13 Oct 2026):
- n = 9: only K9 is not biplanar.
- n = 10: K10 - C is biplanar iff C has two disjoint edges; so K10 - K3 is not biplanar.
- n = 11: not biplanar: K11 - (P3 + 2K2), K11 - bowtie, K11 - 2K3. Biplanar: K11 - C5, K11 - 4K2, K11 - (P4 + K2).
These graphs are what `--underlying-clique` (scripts/sms/uc.patch) forbids.
