#!/usr/bin/env bash
# run_all.sh -- re-run every check of "The parity conjecture for independence polynomials of
# generalized Petersen graphs is false".
#
#   C       verification/c/gpparity.c        isomorphisms for n <= 300, the polynomials of
#                                            GP(7,2), GP(7,3), GP(9,2), the sign tables and the
#                                            Vieta bounds in big-integer arithmetic
#   C++     verification/cpp/gpparity.cpp    the polynomials by a second algorithm, Sturm counts
#                                            of real roots, real-root counts for n <= 13
#   Shell   verification/shell/check_gp.sh   bash integer arithmetic only
#   Python  verification/python/verify_gp.py exact fractions, Sturm counts
#   Julia   verification/julia/verify_gp.jl  (if julia is on PATH or $JULIA is set)
#   Lean    verification/lean/GPParity.lean  (if lean is on PATH; the folder pins v4.34.1)
#           verification/lean/mathlib        (MATHLIB=1 only: lake fetches Mathlib's cache and
#                                             builds the proofs of Lemma 2.1 and Theorem 1.1)
#
# Exit status 0 means every check that ran passed.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
V="$ROOT/verification"
BUILD="$ROOT/build"
mkdir -p "$BUILD"
FAILED=0
fail() { echo "FAIL: $*"; FAILED=1; }
ok() { echo "ok:   $*"; }

echo "== C and C++"
cc -O2 -Wall -o "$BUILD/gpparity" "$V/c/gpparity.c" || fail "compile gpparity.c"
c++ -O2 -Wall -std=c++17 -o "$BUILD/gpparity_cpp" "$V/cpp/gpparity.cpp" || fail "compile gpparity.cpp"
"$BUILD/gpparity" iso 300 > "$BUILD/c_iso.txt" && ok "C: isomorphisms for n <= 300" \
  || fail "C: isomorphisms (see build/c_iso.txt)"
"$BUILD/gpparity" signs > "$BUILD/c_signs.txt" && ok "C: sign tables and Vieta bounds" \
  || fail "C: signs (see build/c_signs.txt)"
want72="1 14 70 154 147 49"; want92="1 18 126 438 801 747 303 27"
p72=$("$BUILD/gpparity" poly 7 2 | sed 's/.*= //'); p73=$("$BUILD/gpparity" poly 7 3 | sed 's/.*= //')
p92=$("$BUILD/gpparity" poly 9 2 | sed 's/.*= //')
[ "$p72" = "$want72" ] && [ "$p73" = "$want72" ] && [ "$p92" = "$want92" ] \
  && ok "C: I(GP(7,2)) = I(GP(7,3)) and I(GP(9,2))" || fail "C: polynomials ($p72 / $p73 / $p92)"
"$BUILD/gpparity_cpp" > "$BUILD/cpp.txt" && grep -q '^ALL OK' "$BUILD/cpp.txt" \
  && ok "C++: polynomials, Sturm counts" || fail "C++ (see build/cpp.txt)"

echo "== Shell"
bash "$V/shell/check_gp.sh" > "$BUILD/sh.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/sh.txt" \
  && ok "check_gp.sh" || fail "check_gp.sh (see build/sh.txt)"

echo "== Python"
python3 "$V/python/verify_gp.py" > "$BUILD/py.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/py.txt" \
  && ok "verify_gp.py" || fail "verify_gp.py (see build/py.txt)"

echo "== Julia"
JULIA="${JULIA:-$(command -v julia || true)}"
if [ -z "$JULIA" ]; then echo "julia not found: skipping"; else
  "$JULIA" "$V/julia/verify_gp.jl" > "$BUILD/jl.txt" 2>&1 && grep -q '^ALL OK' "$BUILD/jl.txt" \
    && ok "verify_gp.jl" || fail "verify_gp.jl (see build/jl.txt)"
fi

echo "== Lean"
if ! command -v lean > /dev/null; then echo "lean not found: skipping (install elan)"; else
  out=$(cd "$V/lean" && lean GPParity.lean 2>&1); st=$?
  echo "$out" > "$BUILD/lean.txt"
  if [ $st -eq 0 ] && ! grep -q "error\|sorryAx" <<< "$out" \
       && grep -q "'iso_family' does not depend on any axioms" <<< "$out" \
       && grep -q "'poly92' depends on axioms: \[propext\]" <<< "$out" \
       && grep -q "'vieta_c' does not depend on any axioms" <<< "$out"; then
    ok "GPParity.lean (kernel-checked)"
  else fail "GPParity.lean (see build/lean.txt)"; fi
  if [ "${MATHLIB:-0}" = 1 ]; then
    out=$(cd "$V/lean/mathlib" && lake exe cache get > /dev/null && lake build 2>&1); st=$?
    echo "$out" > "$BUILD/lean_mathlib.txt"
    n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" <<< "$out")
    if [ $st -eq 0 ] && [ "$n" = 3 ] && ! grep -q "sorryAx\|error" <<< "$out"; then
      ok "mathlib/GPParityMathlib.lean (Lemma 2.1, Theorem 1.1; standard axioms only)"
    else fail "mathlib/GPParityMathlib.lean (see build/lean_mathlib.txt)"; fi
  else echo "Mathlib proof skipped (set MATHLIB=1)"; fi
fi

if [ $FAILED -eq 0 ]; then echo "ALL CHECKS PASSED"; else echo "SOME CHECKS FAILED"; fi
exit $FAILED
