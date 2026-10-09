#!/usr/bin/env python3
"""verify_gp.py -- exact checks (fractions only) for
"The parity conjecture for independence polynomials of generalized Petersen graphs is false".

  * the map u_i -> v_{li}, v_i -> u_{li} is an isomorphism GP(n,k) -> GP(n,l) whenever
    kl = +-1 (mod n), for n <= 120;
  * the independence polynomials of GP(7,2), GP(7,3) and GP(9,2), by listing all
    vertex subsets;
  * Theorem 1.1(b): the sign table at seven rational points;
  * Theorem 1.1(c): the ten bracket points and every inequality of the Vieta argument,
    in exact rational arithmetic, and a Sturm count of the real roots.

Prints "ALL OK" and exits 0 when every check passes.
"""
from fractions import Fraction as F
import sys

failed = False


def check(cond, msg):
    global failed
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        failed = True


def gp_edges(n, k):
    E = set()
    for i in range(n):
        for a, b in ((("u", i), ("u", (i + 1) % n)), (("u", i), ("v", i)), (("v", i), ("v", (i + k) % n))):
            E.add(frozenset((a, b)))
    return E


def phi(n, l, x):
    side, i = x
    return ("v" if side == "u" else "u", (l * i) % n)


def is_iso(n, k, l):
    Ek, El = gp_edges(n, k), gp_edges(n, l)
    img = {frozenset(phi(n, l, x) for x in e) for e in Ek}
    verts = [(s, i) for s in "uv" for i in range(n)]
    return len({phi(n, l, x) for x in verts}) == 2 * n and img == El


def indpoly(n, k):
    E = gp_edges(n, k)
    verts = [(s, i) for s in "uv" for i in range(n)]
    idx = {v: j for j, v in enumerate(verts)}
    nbr = [0] * (2 * n)
    for e in E:
        a, b = tuple(e)
        nbr[idx[a]] |= 1 << idx[b]
        nbr[idx[b]] |= 1 << idx[a]
    c = [0] * (2 * n + 1)
    for S in range(1 << (2 * n)):
        T, ok = S, True
        while T:
            j = (T & -T).bit_length() - 1
            if nbr[j] & S:
                ok = False
                break
            T &= T - 1
        if ok:
            c[bin(S).count("1")] += 1
    while c and c[-1] == 0:
        c.pop()
    return c


def ev(c, x):
    return sum(F(a) * x ** i for i, a in enumerate(c))


def sturm_count(c):
    """number of distinct real roots and whether gcd(p, p') is constant"""
    p = [F(a) for a in c]
    dp = [i * p[i] for i in range(1, len(p))]

    def rem(a, b):
        a = a[:]
        while len(a) >= len(b) and any(a):
            q = a[-1] / b[-1]
            s = len(a) - len(b)
            for i in range(len(b)):
                a[s + i] -= q * b[i]
            a.pop()
            while a and a[-1] == 0:
                a.pop()
        return a

    seq = [p, dp]
    while len(seq[-1]) > 1:
        r = rem(seq[-2], seq[-1])
        if not r:
            break
        seq.append([-x for x in r])

    def changes(minus):
        prev, v = 0, 0
        for q in seq:
            s = 1 if q[-1] > 0 else -1
            if minus and (len(q) - 1) % 2:
                s = -s
            if prev and s != prev:
                v += 1
            prev = s
        return v

    return changes(True) - changes(False), len(seq[-1]) == 1


def main():
    # isomorphisms
    pairs = [(n, k, l) for n in range(5, 121) for k in range(1, (n + 1) // 2) for l in range(1, (n + 1) // 2)
             if 2 * k < n and 2 * l < n and (k * l) % n in (1, n - 1)]
    check(all(is_iso(*t) for t in pairs), f"phi is an isomorphism for all {len(pairs)} pairs kl = +-1 mod n, n <= 120")
    fam = [n for n in range(7, 121, 4)]
    check(all((n - 1) // 2 % 2 == 1 and is_iso(n, 2, (n - 1) // 2) for n in fam),
          f"GP(n,2) = GP(n,(n-1)/2), (n-1)/2 odd, for all {len(fam)} n = 3 mod 4 in [7,120]")

    P, P3, Q = indpoly(7, 2), indpoly(7, 3), indpoly(9, 2)
    check(P == [1, 14, 70, 154, 147, 49] and P3 == P, "I(GP(7,2)) = I(GP(7,3)) = 1+14x+70x^2+154x^3+147x^4+49x^5")
    check(Q == [1, 18, 126, 438, 801, 747, 303, 27], "I(GP(9,2)) = 1+18x+126x^2+438x^3+801x^4+747x^5+303x^6+27x^7")
    check(P[1] == 14 and P[2] == 14 * 13 // 2 - 21, "a_1 = 2n and a_2 = C(2n,2) - 3n for n = 7")

    xs = [F(-7, 5), F(-13, 10), F(-1), F(-3, 5), F(-3, 10), F(-1, 5), F(-1, 10)]
    vals = [ev(P, x) for x in xs]
    check(vals == [F(-8733, 3125), F(67513, 100000), F(1), F(-697, 3125), F(1363, 100000), F(-39, 3125), F(16021, 100000)],
          "the seven values of I(GP(7,2)) in Theorem 1.1(b)")
    check(sum(1 for a, b in zip(vals, vals[1:]) if a * b < 0) == 5, "five sign changes, so five real roots")

    br = [(F("-8.28862"), F("-8.28861")), (F("-0.51657"), F("-0.51656")), (F("-0.31262"), F("-0.31261")),
          (F("-0.22263"), F("-0.22262")), (F("-0.16871"), F("-0.16870"))]
    check(all(ev(Q, a) * ev(Q, b) < 0 for a, b in br), "I(GP(9,2)) changes sign in each of the five brackets")
    check(all(br[i][1] < br[i + 1][0] for i in range(4)), "the five brackets are disjoint")
    lo, hi = sum(a for a, _ in br), sum(b for _, b in br)
    check(lo == F("-9.50915") and hi == F("-9.50910"), "-9.50915 < sum rho_i < -9.50910")
    s_lo, s_hi = F(-303, 27) - hi, F(-303, 27) - lo
    check(F("-1.713123") < s_lo and s_hi < F("-1.713071"), "-1.713123 < r + r' < -1.713071")
    check(max(s_lo ** 2, s_hi ** 2) < F("2.9348"), "(r + r')^2 < 2.9348")
    prod = 1
    for a, _ in br:
        prod *= -a
    check(prod < F("0.050278"), "|rho_1 ... rho_5| < 0.050278")
    check(1 / (27 * F("0.050278")) > F("0.7366") and 4 * F("0.7366") > F("2.9348"), "4 r r' > 2.9464 > 2.9348 > (r + r')^2")
    nr, sf = sturm_count(Q)
    check(nr == 5 and sf, "Sturm: I(GP(9,2)) is squarefree with exactly 5 real roots")
    nr, sf = sturm_count(P)
    check(nr == 5 and sf, "Sturm: I(GP(7,3)) has 5 distinct real roots, so it is real-rooted")
    print("SOME CHECKS FAILED" if failed else "ALL OK")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
