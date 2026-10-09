# verify_gp.jl -- exact checks (BigInt and Rational{BigInt}) for
# "The parity conjecture for independence polynomials of generalized Petersen graphs is false".
#
#  * independence polynomials of GP(n,k), 5 <= n <= 11, by bitmask enumeration of all
#    independent sets (depth-first, a third algorithm besides the C and C++ programs);
#  * that isomorphic pairs GP(n,k) = GP(n,l) (kl = +-1 mod n) have equal polynomials;
#  * Theorem 1.1(b), (c) sign tables and the Vieta inequalities in exact rationals.
# Prints "ALL OK" when every check passes.

failed = false
function check(c, msg)
    global failed
    println(c ? "ok   " : "FAIL ", msg)
    c || (failed = true)
end

function nbrs(n, k)
    nb = zeros(UInt64, 2n)
    add(a, b) = (nb[a+1] |= UInt64(1) << b; nb[b+1] |= UInt64(1) << a)
    for i in 0:n-1
        add(i, mod(i + 1, n)); add(i, n + i); add(n + i, n + mod(i + k, n))
    end
    nb
end

function indpoly(n, k)
    nb = nbrs(n, k)
    c = zeros(BigInt, 2n + 1)
    function go(v, size, forbidden)
        if v == 2n
            c[size+1] += 1
            return
        end
        go(v + 1, size, forbidden)
        if (forbidden >> v) & 1 == 0
            go(v + 1, size + 1, forbidden | nb[v+1])
        end
    end
    go(0, 0, UInt64(0))
    while c[end] == 0
        pop!(c)
    end
    c
end

ev(c, x) = sum(c[i] * x^(i - 1) for i in eachindex(c))

P, P3, Q = indpoly(7, 2), indpoly(7, 3), indpoly(9, 2)
check(P == [1, 14, 70, 154, 147, 49] && P3 == P, "I(GP(7,2)) = I(GP(7,3)) = 1+14x+70x^2+154x^3+147x^4+49x^5")
check(Q == [1, 18, 126, 438, 801, 747, 303, 27], "I(GP(9,2)) = 1+18x+...+27x^7")

ok = true
npairs = 0
for n in 5:11, k in 1:(n-1)÷2, l in 1:(n-1)÷2
    if mod(k * l, n) in (1, n - 1)
        global npairs += 1
        global ok &= indpoly(n, k) == indpoly(n, l)
    end
end
check(ok, "equal polynomials for all $npairs isomorphic pairs with n <= 11")

xs = [-7 // 5, -13 // 10, -1 // 1, -3 // 5, -3 // 10, -1 // 5, -1 // 10]
vals = [ev(P, big(x)) for x in xs]
check(vals == [-8733 // 3125, 67513 // 100000, 1 // 1, -697 // 3125, 1363 // 100000, -39 // 3125, 16021 // 100000],
      "the seven values in Theorem 1.1(b)")
check(count(i -> vals[i] * vals[i+1] < 0, 1:6) == 5, "five sign changes: I(GP(7,3)) is real-rooted")

br = [(-828862 // 100000, -828861 // 100000), (-51657 // 100000, -51656 // 100000), (-31262 // 100000, -31261 // 100000),
      (-22263 // 100000, -22262 // 100000), (-16871 // 100000, -16870 // 100000)]
br = [(big(a), big(b)) for (a, b) in br]
check(all(ev(Q, a) * ev(Q, b) < 0 for (a, b) in br), "sign change of I(GP(9,2)) in each bracket")
lo, hi = sum(first.(br)), sum(last.(br))
s_lo, s_hi = -303 // 27 - hi, -303 // 27 - lo
check(-1713123 // 1000000 < s_lo && s_hi < -1713071 // 1000000, "-1.713123 < r + r' < -1.713071")
check(max(s_lo^2, s_hi^2) < 29348 // 10000, "(r + r')^2 < 2.9348")
prodabs = prod(-a for (a, _) in br)
check(prodabs < 50278 // 1000000, "|rho_1 ... rho_5| < 0.050278")
check(1 / (27 * (50278 // 1000000)) > 7366 // 10000 && 4 * (7366 // 10000) > 29348 // 10000,
      "4 r r' > 2.9464 > (r + r')^2, so the remaining pair is not real")

println(failed ? "SOME CHECKS FAILED" : "ALL OK")
exit(failed ? 1 : 0)
