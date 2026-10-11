/* PRUNE hook for geng: complements U of 18-vertex triangle-free graphs H that could be
   biplanar with alpha(U) <= 2.  Every induced subgraph H_m (m vertices) must satisfy
   (a) alpha(H_m) <= 8          (an independent set of H is a clique of U; K9 is not biplanar)
   (b) e(H_m) >= C(m,2)-6m+12   (U_m is biplanar, so e(U_m) <= 6m-12), m >= 3
   (c) for m >= 17: H_m has no homomorphism to C5 (else U_m contains a clique blow-up of C5
       on m >= 17 vertices, which is not biplanar).
   At the final order every vertex-deleted subgraph is tested for (c) as well. */
#include "gtools.h"

static graph *gg;

/* is there an independent set of size >= need inside P? */
static int indep(setword P, int need)
{
    if (need <= 0) return 1;
    if (POPCOUNT(P) < need) return 0;
    int v = FIRSTBITNZ(P);
    setword Pv = P & ~bit[v];
    if (indep(Pv & ~gg[v], need - 1)) return 1;
    return indep(Pv, need);
}

static int ord[MAXN], dom[MAXN], col[MAXN], nord;
int c5col[MAXN];
static const int nb5[5] = { (1<<1)|(1<<4), (1<<0)|(1<<2), (1<<1)|(1<<3), (1<<2)|(1<<4), (1<<3)|(1<<0) };
static setword Sset;

static int rec(int i)
{
    if (i == nord) { for (int k = 0; k < MAXN; ++k) c5col[k] = col[k]; return 1; }
    int v = ord[i];
    int d = dom[v];
    while (d) {
        int c = __builtin_ctz(d); d &= d - 1;
        int save[2*MAXN]; int ns = 0, ok = 1;
        setword N = gg[v] & Sset;
        while (N) {
            int w = FIRSTBITNZ(N); N &= ~bit[w];
            if (col[w] >= 0) { if (!(nb5[c] >> col[w] & 1)) { ok = 0; break; } }
            else {
                int nd = dom[w] & nb5[c];
                if (!nd) { ok = 0; break; }
                if (nd != dom[w]) { save[ns++] = w; save[ns++] = dom[w]; dom[w] = nd; }
            }
        }
        if (ok) { col[v] = c; if (rec(i + 1)) return 1; col[v] = -1; }
        for (int k = ns - 2; k >= 0; k -= 2) dom[save[k]] = save[k + 1];
    }
    return 0;
}

/* does the subgraph of g induced on S admit a homomorphism to C5? */
int c5hom(graph *g, setword S)
{
    gg = g; Sset = S; nord = 0;
    setword left = S;
    for (int v = 0; v < MAXN; ++v) { dom[v] = 31; col[v] = -1; }
    int first = 1;
    while (left) {
        int r = FIRSTBITNZ(left);
        int qh = nord; ord[nord++] = r; left &= ~bit[r];
        while (qh < nord) {
            int v = ord[qh++];
            setword N = g[v] & left;
            while (N) { int w = FIRSTBITNZ(N); N &= ~bit[w]; left &= ~bit[w]; ord[nord++] = w; }
        }
        if (first) { dom[r] = 1; first = 0; }
    }
    return rec(0);
}

int myprune(graph *g, int n, int maxn)
{
    gg = g;
    int e = 0;
    for (int i = 0; i < n; ++i) e += POPCOUNT(g[i]);
    e /= 2;
    if (n >= 3 && e < n*(n-1)/2 - 6*n + 12) return 1;
    if (n >= 9) {
        setword P = ALLMASK(n) & ~bit[n-1] & ~g[n-1];
        if (indep(P, 8)) return 1;
    }
    if (n >= 17) {
        setword all = ALLMASK(n);
        if (c5hom(g, all)) return 1;
        if (n == maxn && n >= 18)
            for (int v = 0; v < n - 1; ++v)
                if (c5hom(g, all & ~bit[v])) return 1;
    }
    return 0;
}
