# The parity conjecture for independence polynomials of generalized Petersen graphs is false

Deep Bhattacharjee

Pandey (2026, Conjecture 4.1) proposed that for all integers n ≥ 2k + 1 the independence
polynomial of the generalized Petersen graph GP(n,k) has only real roots if and only if k is even.

The conjecture contradicts itself. If n ≡ 3 (mod 4), then 2 · (n − 1)/2 ≡ −1 (mod n), so the map
u_i ↦ v_{li}, v_i ↦ u_{li} with l = (n − 1)/2 is an isomorphism GP(n,2) ≅ GP(n,l), and l is odd. The
conjecture asks the same polynomial to be real-rooted (k = 2) and not real-rooted (k = l), so it
fails at one of the two pairs for every such n. Each direction also fails on its own:

- I(GP(7,3); x) = 1 + 14x + 70x² + 154x³ + 147x⁴ + 49x⁵ has five real roots, although 3 is odd;
- I(GP(9,2); x) = 1 + 18x + 126x² + 438x³ + 801x⁴ + 747x⁵ + 303x⁶ + 27x⁷ has exactly five real roots
  and a pair of non-real roots near −0.85655 ± 0.05554i, although 2 is even.

## Paper

`preprintGPParity/` holds the paper (LaTeX source and the TikZ figure); `dist/` holds the PDF, a
source zip with the figure as PNG and an arXiv tarball, rebuilt by `scripts/build_paper.sh`.

## Checks

```
verification/c/gpparity.c              isomorphisms for all pairs kl = ±1 (mod n), n <= 300; the three
                                       polynomials by backtracking; sign tables and Vieta bounds in big integers
verification/cpp/gpparity.cpp          the polynomials by the deletion recurrence; Sturm counts of real roots
                                       in exact integer arithmetic; real-root counts for all GP(n,k), n <= 13
verification/shell/check_gp.sh         bash integer arithmetic only: isomorphisms for n <= 199, sign table, bounds
verification/python/verify_gp.py       exact fractions: isomorphisms for n <= 120, polynomials by all subsets, Sturm
verification/julia/verify_gp.jl        BigInt and Rational: polynomials for n <= 11, sign tables, Vieta bounds
verification/lean/GPParity.lean        Lean 4 kernel check of the isomorphisms (n <= 199), the three polynomials,
                                       the sign tables and the Vieta inequalities
verification/lean/mathlib/             Lean 4 + Mathlib proof of Lemma 2.1 for every n, Theorem 1.1(a) for every
                                       n = 3 (mod 4), the refutation of the conjecture as stated, and the root
                                       counts of Theorem 1.1(b), (c); standard axioms only
```

`scripts/run_all.sh` runs them all (`MATHLIB=1` also builds the Mathlib proof); the `verify` workflow
runs them on every pull request.

## Citation

See `CITATION.cff`. The Zenodo DOI will be added after the first release.

## Licence

MIT, see `LICENSE`.
