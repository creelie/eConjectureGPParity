// gpparity.cpp -- an independent check of the computational facts in
// "The parity conjecture for independence polynomials of generalized Petersen graphs is false".
//
// Independence polynomials are computed with the deletion recurrence
//     I(G) = I(G - v) + x I(G - N[v])
// memoised on vertex subsets (a different algorithm from the C program), and the number
// of real roots is counted with Sturm's theorem in exact integer arithmetic, using a
// pseudo-remainder sequence scaled by even powers of the leading coefficients.
//
//   gpparity_cpp            check GP(7,2), GP(7,3), GP(9,2) and print the real-root
//                           counts of I(GP(n,k)) for 5 <= n <= 13, 1 <= k < n/2
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <string>
#include <unordered_map>
#include <vector>

using u64 = std::uint64_t;
static bool failed = false;
static void check(bool c, const std::string &msg) {
    std::printf("%s %s\n", c ? "ok  " : "FAIL", msg.c_str());
    if (!c) failed = true;
}

// ---------------- signed big integers, base 2^32 ----------------
struct Big {
    bool neg = false;
    std::vector<std::uint32_t> d;  // little endian, no leading zeros
    Big(long long v = 0) {
        if (v < 0) { neg = true; v = -v; }
        unsigned long long u = (unsigned long long)v;
        while (u) { d.push_back((std::uint32_t)u); u >>= 32; }
    }
    bool zero() const { return d.empty(); }
    int sign() const { return zero() ? 0 : (neg ? -1 : 1); }
    void trim() { while (!d.empty() && d.back() == 0) d.pop_back(); if (d.empty()) neg = false; }
};
static int cmpabs(const Big &a, const Big &b) {
    if (a.d.size() != b.d.size()) return a.d.size() < b.d.size() ? -1 : 1;
    for (size_t i = a.d.size(); i-- > 0;) if (a.d[i] != b.d[i]) return a.d[i] < b.d[i] ? -1 : 1;
    return 0;
}
static Big addabs(const Big &a, const Big &b) {
    Big r; r.d.resize(std::max(a.d.size(), b.d.size()) + 1);
    u64 c = 0;
    for (size_t i = 0; i < r.d.size(); i++) {
        c += (i < a.d.size() ? a.d[i] : 0) + (u64)(i < b.d.size() ? b.d[i] : 0);
        r.d[i] = (std::uint32_t)c; c >>= 32;
    }
    r.trim(); return r;
}
static Big subabs(const Big &a, const Big &b) {  // |a| >= |b|
    Big r; r.d.resize(a.d.size());
    long long c = 0;
    for (size_t i = 0; i < a.d.size(); i++) {
        long long x = (long long)a.d[i] - (i < b.d.size() ? b.d[i] : 0) + c;
        if (x < 0) { x += (1LL << 32); c = -1; } else c = 0;
        r.d[i] = (std::uint32_t)x;
    }
    r.trim(); return r;
}
static Big operator+(const Big &a, const Big &b) {
    Big r;
    if (a.neg == b.neg) { r = addabs(a, b); r.neg = a.neg; }
    else if (cmpabs(a, b) >= 0) { r = subabs(a, b); r.neg = a.neg; }
    else { r = subabs(b, a); r.neg = b.neg; }
    r.trim(); return r;
}
static Big operator-(const Big &a) { Big r = a; if (!r.zero()) r.neg = !r.neg; return r; }
static Big operator-(const Big &a, const Big &b) { return a + (-b); }
static Big operator*(const Big &a, const Big &b) {
    Big r; if (a.zero() || b.zero()) return r;
    std::vector<u64> t(a.d.size() + b.d.size() + 1, 0);
    for (size_t i = 0; i < a.d.size(); i++) {
        u64 c = 0;
        for (size_t j = 0; j < b.d.size(); j++) {
            u64 cur = t[i + j] + (u64)a.d[i] * b.d[j] + c;
            t[i + j] = (std::uint32_t)cur; c = cur >> 32;
        }
        size_t k = i + b.d.size();
        while (c) { u64 cur = t[k] + c; t[k] = (std::uint32_t)cur; c = cur >> 32; k++; }
    }
    r.d.assign(t.begin(), t.end());
    for (auto &x : r.d) x = (std::uint32_t)x;
    r.neg = a.neg != b.neg; r.trim(); return r;
}

using Poly = std::vector<Big>;  // coefficient of x^i at index i
static void trimp(Poly &p) { while (!p.empty() && p.back().zero()) p.pop_back(); }

// pseudo-remainder of a by b, scaled by lc(b)^e with e even and e >= deg a - deg b + 1
static Poly prem_even(Poly a, const Poly &b) {
    int db = (int)b.size() - 1;
    int e = (int)a.size() - 1 - db + 1;
    if (e % 2) e++;
    Big lc = b.back();
    int steps = 0;
    while ((int)a.size() - 1 >= db && !a.empty()) {
        int da = (int)a.size() - 1;
        Big la = a.back();
        for (auto &c : a) c = c * lc;                 // a *= lc(b)
        for (int i = 0; i <= db; i++) a[da - db + i] = a[da - db + i] - la * b[i];
        trimp(a);
        steps++;
    }
    for (; steps < e; steps++) for (auto &c : a) c = c * lc;
    return a;
}

// number of distinct real roots, by Sturm's theorem (signs at -inf and +inf);
// *squarefree is set when the sequence ends in a nonzero constant, i.e. gcd(p, p') = 1
static int real_roots(const Poly &p0, bool *squarefree = nullptr) {
    Poly p = p0; trimp(p);
    Poly dp; for (size_t i = 1; i < p.size(); i++) dp.push_back(p[i] * Big((long long)i));
    std::vector<Poly> seq = {p, dp};
    while (seq.back().size() > 1) {
        Poly r = prem_even(seq[seq.size() - 2], seq.back());
        if (r.empty()) break;
        for (auto &c : r) c = -c;
        seq.push_back(r);
    }
    if (squarefree) *squarefree = seq.back().size() == 1;
    auto changes = [&](bool minus_inf) {
        int prev = 0, v = 0;
        for (auto &q : seq) {
            int s = q.back().sign();
            if (minus_inf && (q.size() - 1) % 2) s = -s;
            if (s && prev && s != prev) v++;
            if (s) prev = s;
        }
        return v;
    };
    return changes(true) - changes(false);
}

// independence polynomial by memoised deletion
struct Graph { int n; std::vector<u64> nb; };
static std::unordered_map<u64, std::vector<long long>> memo;
static std::vector<long long> ip(const Graph &g, u64 S) {
    if (!S) return {1};
    auto it = memo.find(S);
    if (it != memo.end()) return it->second;
    int v = __builtin_ctzll(S);
    auto a = ip(g, S & ~(1ULL << v));
    auto b = ip(g, S & ~(1ULL << v) & ~g.nb[v]);
    std::vector<long long> r(std::max(a.size(), b.size() + 1), 0);
    for (size_t i = 0; i < a.size(); i++) r[i] += a[i];
    for (size_t i = 0; i < b.size(); i++) r[i + 1] += b[i];
    memo[S] = r;
    return r;
}
static Graph gp(int n, int k) {
    Graph g{2 * n, std::vector<u64>(2 * n, 0)};
    auto e = [&](int a, int b) { g.nb[a] |= 1ULL << b; g.nb[b] |= 1ULL << a; };
    for (int i = 0; i < n; i++) { e(i, (i + 1) % n); e(i, n + i); e(n + i, n + (i + k) % n); }
    return g;
}
static std::vector<long long> indpoly(int n, int k) {
    memo.clear();
    Graph g = gp(n, k);
    u64 all = (2 * n == 64) ? ~0ULL : ((1ULL << (2 * n)) - 1);
    return ip(g, all);
}

int main() {
    auto p72 = indpoly(7, 2), p73 = indpoly(7, 3), p92 = indpoly(9, 2);
    check(p72 == std::vector<long long>{1, 14, 70, 154, 147, 49}, "I(GP(7,2)) = 1+14x+70x^2+154x^3+147x^4+49x^5");
    check(p73 == p72, "I(GP(7,3)) = I(GP(7,2))");
    check(p92 == std::vector<long long>{1, 18, 126, 438, 801, 747, 303, 27}, "I(GP(9,2)) = 1+18x+...+27x^7");
    auto toPoly = [](const std::vector<long long> &c) { Poly p; for (auto x : c) p.push_back(Big(x)); return p; };
    bool sf72 = false, sf92 = false;
    int r72 = real_roots(toPoly(p72), &sf72), r92 = real_roots(toPoly(p92), &sf92);
    check(r72 == 5, "Sturm: I(GP(7,3)) has 5 distinct real roots (degree 5): real-rooted");
    check(r92 == 5 && sf92, "Sturm: I(GP(9,2)) is squarefree with 5 real roots (degree 7): two roots are not real");
    std::printf("real-root counts of I(GP(n,k)), 5 <= n <= 13 (R = real-rooted):\n");
    for (int n = 5; n <= 13; n++) {
        std::printf("  n=%2d:", n);
        for (int k = 1; 2 * k < n; k++) {
            auto c = indpoly(n, k);
            int deg = (int)c.size() - 1, r = real_roots(toPoly(c));
            std::printf("  k=%d %d/%d%s", k, r, deg, r == deg ? " R" : "");
        }
        std::printf("\n");
    }
    std::printf(failed ? "SOME CHECKS FAILED\n" : "ALL OK\n");
    return failed ? 1 : 0;
}
