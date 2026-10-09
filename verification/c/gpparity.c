/* gpparity.c -- checks for "The parity conjecture for independence polynomials of
 * generalized Petersen graphs is false".
 *
 *   gpparity iso N     for every n <= N and all 1 <= k, l < n/2 with kl = +-1 (mod n),
 *                      checks that u_i -> v_{li}, v_i -> u_{li} maps the edge set of
 *                      GP(n,k) onto that of GP(n,l); and that for n = 3 (mod 4), n >= 7,
 *                      the pair (2, (n-1)/2) is such a pair with (n-1)/2 odd.
 *   gpparity poly n k  prints the independence polynomial of GP(n,k), counted by
 *                      backtracking over the 2n vertices.
 *   gpparity signs     exact sign tables of Theorem 1.1(b), (c) with big integers, and the
 *                      root-coefficient bounds used in the proof of (c).
 *
 * Exit status 0 means every claim checked here holds.  Output lines starting with
 * "ok" report a passed check; the last line is "ALL OK" when everything passed.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int failed = 0;
#define CHECK(c, ...) do { if (c) { printf("ok   "); } else { printf("FAIL "); failed = 1; } \
                           printf(__VA_ARGS__); printf("\n"); } while (0)

/* ---------- generalized Petersen graphs ---------- */
#define MAXN 512
static int adj[2 * MAXN][2 * MAXN];

static void build(int n, int k) {
    memset(adj, 0, sizeof adj);
    for (int i = 0; i < n; i++) {
        int a, b;
        a = i; b = (i + 1) % n;          adj[a][b] = adj[b][a] = 1;  /* u_i u_{i+1} */
        a = i; b = n + i;                adj[a][b] = adj[b][a] = 1;  /* u_i v_i */
        a = n + i; b = n + (i + k) % n;  adj[a][b] = adj[b][a] = 1;  /* v_i v_{i+k} */
    }
}

static int nedges(int n) {
    int m = 0;
    for (int a = 0; a < 2 * n; a++) for (int b = a + 1; b < 2 * n; b++) m += adj[a][b];
    return m;
}

/* is phi an isomorphism GP(n,k) -> GP(n,l)? */
static int is_iso(int n, int k, int l) {
    static int A[2 * MAXN][2 * MAXN];
    build(n, k);
    memcpy(A, adj, sizeof adj);
    int mk = nedges(n);
    build(n, l);
    int ml = nedges(n);
    if (mk != ml) return 0;
    int phi[2 * MAXN], seen[2 * MAXN] = {0};
    for (int i = 0; i < n; i++) {
        phi[i] = n + (int)(((long)l * i) % n);
        phi[n + i] = (int)(((long)l * i) % n);
    }
    for (int x = 0; x < 2 * n; x++) { if (seen[phi[x]]) return 0; seen[phi[x]] = 1; }
    for (int a = 0; a < 2 * n; a++)
        for (int b = 0; b < 2 * n; b++)
            if (A[a][b] && !adj[phi[a]][phi[b]]) return 0;
    return 1;
}

static int iso_check(int N) {
    long pairs = 0, fam = 0;
    int ok = 1;
    for (int n = 5; n <= N; n++)
        for (int k = 1; 2 * k < n; k++)
            for (int l = 1; 2 * l < n; l++) {
                long p = ((long)k * l) % n;
                if (p == 1 || p == n - 1) {
                    pairs++;
                    if (!is_iso(n, k, l)) { ok = 0; printf("not an isomorphism: n=%d k=%d l=%d\n", n, k, l); }
                }
            }
    CHECK(ok, "phi is an isomorphism GP(n,k) -> GP(n,l) for all %ld pairs with kl = +-1 mod n, n <= %d", pairs, N);
    int ok2 = 1;
    for (int n = 7; n <= N; n += 4) {
        int l = (n - 1) / 2;
        fam++;
        if (l % 2 != 1 || 2 * l >= n || !is_iso(n, 2, l)) { ok2 = 0; printf("family fails at n=%d\n", n); }
    }
    CHECK(ok2, "GP(n,2) = GP(n,(n-1)/2) with (n-1)/2 odd for all %ld n = 3 mod 4, 7 <= n <= %d", fam, N);
    CHECK(is_iso(13, 4, 3), "GP(13,4) = GP(13,3)");
    return ok && ok2;
}

/* ---------- independence polynomial by backtracking ---------- */
static long long cnt[2 * MAXN + 1];
static int N2;
static void rec(int v, int size, int *blocked) {
    if (v == N2) { cnt[size]++; return; }
    rec(v + 1, size, blocked);               /* v not in the set */
    if (!blocked[v]) {                       /* v in the set */
        int nb[2 * MAXN], m = 0;
        for (int w = v + 1; w < N2; w++) if (adj[v][w] && !blocked[w]) { blocked[w] = 1; nb[m++] = w; }
        rec(v + 1, size + 1, blocked);
        for (int t = 0; t < m; t++) blocked[nb[t]] = 0;
    }
}
static int indpoly(int n, int k, long long *out) {
    build(n, k);
    N2 = 2 * n;
    memset(cnt, 0, sizeof cnt);
    int blocked[2 * MAXN] = {0};
    rec(0, 0, blocked);
    int d = 0;
    for (int j = 0; j <= N2; j++) { out[j] = cnt[j]; if (cnt[j]) d = j; }
    return d;
}

/* ---------- minimal signed big integers (base 1e9) ---------- */
#define LIMBS 16
typedef struct { int neg; uint32_t d[LIMBS]; } big;
static void bset(big *a, long long v) {
    memset(a, 0, sizeof *a);
    if (v < 0) { a->neg = 1; v = -v; }
    for (int i = 0; v; i++) { a->d[i] = (uint32_t)(v % 1000000000); v /= 1000000000; }
}
static int biszero(const big *a) { for (int i = 0; i < LIMBS; i++) if (a->d[i]) return 0; return 1; }
static int cmpabs(const big *a, const big *b) {
    for (int i = LIMBS - 1; i >= 0; i--) if (a->d[i] != b->d[i]) return a->d[i] < b->d[i] ? -1 : 1;
    return 0;
}
static void addabs(big *r, const big *a, const big *b) {
    uint64_t c = 0;
    for (int i = 0; i < LIMBS; i++) { c += (uint64_t)a->d[i] + b->d[i]; r->d[i] = (uint32_t)(c % 1000000000); c /= 1000000000; }
    if (c) { fprintf(stderr, "overflow\n"); exit(2); }
}
static void subabs(big *r, const big *a, const big *b) { /* |a| >= |b| */
    int64_t c = 0;
    for (int i = 0; i < LIMBS; i++) {
        int64_t x = (int64_t)a->d[i] - b->d[i] + c;
        if (x < 0) { x += 1000000000; c = -1; } else c = 0;
        r->d[i] = (uint32_t)x;
    }
}
static void badd(big *r, const big *a, const big *b) {
    big t;
    if (a->neg == b->neg) { addabs(&t, a, b); t.neg = a->neg; }
    else if (cmpabs(a, b) >= 0) { subabs(&t, a, b); t.neg = a->neg; }
    else { subabs(&t, b, a); t.neg = b->neg; }
    if (biszero(&t)) t.neg = 0;
    *r = t;
}
static void bmuls(big *r, const big *a, long long s) {
    big t; memset(&t, 0, sizeof t);
    int neg = a->neg ^ (s < 0);
    if (s < 0) s = -s;
    unsigned __int128 c = 0;
    for (int i = 0; i < LIMBS; i++) {
        c += (unsigned __int128)a->d[i] * (unsigned long long)s;
        t.d[i] = (uint32_t)(c % 1000000000); c /= 1000000000;
    }
    if (c) { fprintf(stderr, "overflow\n"); exit(2); }
    t.neg = biszero(&t) ? 0 : neg;
    *r = t;
}
static int bsign(const big *a) { return biszero(a) ? 0 : (a->neg ? -1 : 1); }

/* sign of sum_i c[i] (p/q)^i, i.e. of sum_i c[i] p^i q^(d-i), q > 0 */
static int sign_at(const long long *c, int d, long long p, long long q) {
    big s; bset(&s, 0);
    for (int i = 0; i <= d; i++) {
        big t; bset(&t, c[i]);
        for (int j = 0; j < i; j++) bmuls(&t, &t, p);
        for (int j = 0; j < d - i; j++) bmuls(&t, &t, q);
        badd(&s, &s, &t);
    }
    return bsign(&s);
}

static int signs_check(void) {
    long long P[64], Q[64];
    int dP = indpoly(7, 2, P), dQ = indpoly(9, 2, Q);
    long long P3[64]; int dP3 = indpoly(7, 3, P3);
    long long wantP[] = {1, 14, 70, 154, 147, 49}, wantQ[] = {1, 18, 126, 438, 801, 747, 303, 27};
    int okP = dP == 5 && dP3 == 5, okQ = dQ == 7;
    for (int i = 0; i <= 5; i++) okP &= P[i] == wantP[i] && P3[i] == wantP[i];
    for (int i = 0; i <= 7; i++) okQ &= Q[i] == wantQ[i];
    CHECK(okP, "I(GP(7,2)) = I(GP(7,3)) = 1+14x+70x^2+154x^3+147x^4+49x^5");
    CHECK(okQ, "I(GP(9,2)) = 1+18x+126x^2+438x^3+801x^4+747x^5+303x^6+27x^7");

    /* Theorem 1.1(b): signs at -7/5, -13/10, -1, -3/5, -3/10, -1/5, -1/10 */
    long long xp[] = {-14, -13, -10, -6, -3, -2, -1}; /* x = xp/10 */
    int want[] = {-1, 1, 1, -1, 1, -1, 1}, okb = 1;
    for (int t = 0; t < 7; t++) okb &= sign_at(P, 5, xp[t], 10) == want[t];
    CHECK(okb, "sign table of I(GP(7,2)) at seven points: five sign changes");

    /* Theorem 1.1(c): ten bracket points (x = p / 100000) */
    long long br[5][2] = {{-828862, -828861}, {-51657, -51656}, {-31262, -31261}, {-22263, -22262}, {-16871, -16870}};
    int okc = 1;
    for (int t = 0; t < 5; t++) {
        int s0 = sign_at(Q, 7, br[t][0], 100000), s1 = sign_at(Q, 7, br[t][1], 100000);
        okc &= s0 * s1 == -1;
    }
    CHECK(okc, "I(GP(9,2)) changes sign across each of the five brackets");

    /* Vieta bounds, all in units of 1e-5 (exact integer arithmetic) */
    long long lo = 0, hi = 0;
    for (int t = 0; t < 5; t++) { lo += br[t][0]; hi += br[t][1]; }
    CHECK(lo == -950915 && hi == -950910, "sum of the five roots lies in (-9.50915, -9.50910)");
    /* r + r' = -303/27 - sum; claim -1.713123 < r+r' < -1.713071.
       27 (r+r') = -303 - 27 sum; with sum in (lo, hi)*1e-5: compare in units of 1e-6 * 27 */
    long long up = -303000000LL - 27LL * lo * 10;   /* 27e6 * upper end of r+r' */
    long long dn = -303000000LL - 27LL * hi * 10;   /* 27e6 * lower end */
    CHECK(dn > -27LL * 1713123 && up < -27LL * 1713071, "-1.713123 < r + r' < -1.713071");
    CHECK(1713123LL * 1713123LL < 29348LL * 100000000LL, "(r + r')^2 < 2.9348");
    /* |rho_1...rho_5| < 0.050278: product of the absolute lower ends, exactly */
    big pr; bset(&pr, 1);
    for (int t = 0; t < 5; t++) bmuls(&pr, &pr, -br[t][0]);
    big lim; bset(&lim, 50278);                       /* 0.050278 = 50278e-6 */
    for (int t = 0; t < 19; t++) bmuls(&lim, &lim, 10); /* scale to 1e-25 units */
    CHECK(cmpabs(&pr, &lim) < 0, "|rho_1 rho_2 rho_3 rho_4 rho_5| < 0.050278");
    /* rr' > 1/(27 * 0.050278) > 0.7366 :  1e10 > 0.7366e4 * 27 * 50278 */
    CHECK(10000000000LL > 7366LL * 27LL * 50278LL, "1/(27 * 0.050278) > 0.7366");
    CHECK(4LL * 7366 == 29464 && 29464 > 29348, "4 * 0.7366 > 2.9464 > 2.9348, so (r - r')^2 < 0");
    return okP && okQ && okb && okc;
}

int main(int argc, char **argv) {
    if (argc >= 3 && !strcmp(argv[1], "iso")) iso_check(atoi(argv[2]));
    else if (argc >= 4 && !strcmp(argv[1], "poly")) {
        int n = atoi(argv[2]), k = atoi(argv[3]);
        if (n < 3 || n > 20 || k < 1 || 2 * k >= n) { fprintf(stderr, "need 3 <= n <= 20, 1 <= k < n/2\n"); return 2; }
        long long c[2 * MAXN + 1];
        int d = indpoly(n, k, c);
        printf("I(GP(%d,%d);x) =", n, k);
        for (int j = 0; j <= d; j++) printf(" %lld", c[j]);
        printf("\n");
        return 0;
    } else if (argc >= 2 && !strcmp(argv[1], "signs")) signs_check();
    else { fprintf(stderr, "usage: gpparity iso N | poly n k | signs\n"); return 2; }
    printf(failed ? "SOME CHECKS FAILED\n" : "ALL OK\n");
    return failed;
}
