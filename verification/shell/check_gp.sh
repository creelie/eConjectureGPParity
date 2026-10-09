#!/usr/bin/env bash
# check_gp.sh -- bash integer arithmetic only.
#   1. For every n = 3 (mod 4), 7 <= n <= 199: the map u_i -> v_{li}, v_i -> u_{li} with
#      l = (n-1)/2 sends every edge of GP(n,2) to an edge of GP(n,l), and l is odd.
#   2. Theorem 1.1(b): 10^5 * P(x) at the seven points, P = I(GP(7,2)).
#   3. Theorem 1.1(c): the sums of the bracket ends and the bounds on r + r', (r + r')^2,
#      |rho_1...rho_5| (the last with upward rounding at each step).
# Prints "ALL OK" when everything passes.
set -u
fail=0
ok() { echo "ok   $*"; }
bad() { echo "FAIL $*"; fail=1; }

# 1. isomorphism GP(n,2) -> GP(n,(n-1)/2)
count=0
for ((n = 7; n <= 199; n += 4)); do
  l=$(((n - 1) / 2))
  ((l % 2 == 1)) || bad "l even at n=$n"
  # edges of GP(n,l) as a lookup table: key "a,b" with a<b; u_i = i, v_i = n+i
  declare -A E=()
  for ((i = 0; i < n; i++)); do
    for pair in "$i $(((i + 1) % n))" "$i $((n + i))" "$((n + i)) $((n + (i + l) % n))"; do
      set -- $pair; a=$1; b=$2; ((a > b)) && { t=$a; a=$b; b=$t; }; E["$a,$b"]=1
    done
  done
  img() { local x=$1; if ((x < n)); then echo $((n + (l * x) % n)); else echo $(((l * (x - n)) % n)); fi; }
  for ((i = 0; i < n; i++)); do
    for pair in "$i $(((i + 1) % n))" "$i $((n + i))" "$((n + i)) $((n + (i + 2) % n))"; do
      set -- $pair; a=$(img $1); b=$(img $2); ((a > b)) && { t=$a; a=$b; b=$t; }
      [[ -n "${E["$a,$b"]:-}" ]] || bad "edge $1-$2 of GP($n,2) not mapped to an edge"
    done
  done
  unset E
  count=$((count + 1))
done
((fail == 0)) && ok "GP(n,2) = GP(n,(n-1)/2), (n-1)/2 odd, for all $count n = 3 mod 4 in [7,199]"

# 2. P(x) = 1+14x+70x^2+154x^3+147x^4+49x^5 at x = p/10; 10^5 P(p/10) = sum c_i p^i 10^(5-i)
c=(1 14 70 154 147 49)
want=(-279456 67513 100000 -22304 1363 -1248 16021)   # 10^5 * values (exact: denominators divide 10^5)
pts=(-14 -13 -10 -6 -3 -2 -1)
okb=1
for t in 0 1 2 3 4 5 6; do
  p=${pts[$t]}; s=0; pw=1
  for i in 0 1 2 3 4 5; do
    s=$((s + c[i] * pw * 10 ** (5 - i))); pw=$((pw * p))
  done
  ((s == want[t])) || { okb=0; echo "  P(${p}/10)*10^5 = $s, expected ${want[$t]}"; }
done
((okb)) && ok "10^5 P at -7/5,-13/10,-1,-3/5,-3/10,-1/5,-1/10: -279456 67513 100000 -22304 1363 -1248 16021 (five sign changes)" \
        || bad "sign table of I(GP(7,2))"

# 3. Vieta bounds, in units of 1e-5 and 1e-6
lo=(-828862 -51657 -31262 -22263 -16871); hi=(-828861 -51656 -31261 -22262 -16870)
L=0; H=0; for i in 0 1 2 3 4; do L=$((L + lo[i])); H=$((H + hi[i])); done
((L == -950915 && H == -950910)) && ok "-9.50915 < sum rho_i < -9.50910" || bad "sum of brackets"
# 27e6 (r + r') lies in (-303e6 - 270 H, -303e6 - 270 L)
dn=$((-303000000 - 270 * H)); up=$((-303000000 - 270 * L))
((dn > -27 * 1713123 && up < -27 * 1713071)) && ok "-1.713123 < r + r' < -1.713071" || bad "r + r'"
((1713123 * 1713123 < 29348 * 100000000)) && ok "(r + r')^2 < 1.713123^2 < 2.9348" || bad "(r+r')^2"
# product of |lo_i| (each in units of 1e-5), rounded up to units of 1e-6 after each step
prod=1000000   # 1.000000
for i in 0 1 2 3 4; do a=$((-lo[i])); prod=$(((prod * a + 99999) / 100000)); done
((prod < 50278)) && ok "|rho_1...rho_5| < $prod e-6 < 0.050278" || bad "product bound ($prod)"
((10000000000 > 7366 * 27 * 50278 && 4 * 7366 > 29348)) && ok "4 r r' > 4/(27*0.050278) > 2.9464 > 2.9348" || bad "rr' bound"

if ((fail == 0)); then echo "ALL OK"; else echo "SOME CHECKS FAILED"; fi
exit $fail
