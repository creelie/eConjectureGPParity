**The parity conjecture for independence polynomials of generalized Petersen graphs is false**, by Deep Bhattacharjee.

Pandey (2026) conjectured that for n ≥ 2k + 1 the independence polynomial of GP(n,k) has only real roots if and only if k is even. The paper shows that the statement contradicts itself and that each direction fails on its own.

| Claim | Reason |
|---|---|
| The conjecture contradicts itself for every n ≡ 3 (mod 4), n ≥ 7 | GP(n,2) ≅ GP(n,(n−1)/2) and (n−1)/2 is odd |
| "k odd ⇒ not real-rooted" fails | I(GP(7,3)) has five real roots in five disjoint intervals |
| "k even ⇒ real-rooted" fails | I(GP(9,2)) has exactly five real roots out of seven |

The proofs are by hand. Every finite claim is re-checked in C, C++, Bash, Python, Julia and Lean 4: a Lean proof with Mathlib covers the isomorphism lemma for every n, the self-contradiction for every n ≡ 3 (mod 4) and the root counts, using only the standard axioms, and a kernel check covers the isomorphisms for n ≤ 199, the three polynomials and the numerical inequalities.

Files:
- `gp-parity-conjecture.pdf`: the paper
- `gp-parity-conjecture-tex.zip`: LaTeX source with the figure as PNG (and its TikZ source)
- `gp-parity-conjecture-arxiv.tar.gz`: LaTeX source with the figure as PDF, ready for arXiv

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
