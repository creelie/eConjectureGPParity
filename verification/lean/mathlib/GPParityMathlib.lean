/-
  The parity conjecture for independence polynomials of generalized Petersen graphs is false.

  Conjecture 4.1 of Pandey (2026): for all integers n ≥ 2k + 1 (k ≥ 1), the independence polynomial
  of GP(n,k) has only real roots if and only if k is even.

  Proved below with Mathlib:
  * `gp_iso` (Lemma 2.1): if kl = ±1 in ZMod n, then u_i ↦ v_{li}, v_i ↦ u_{li} is an isomorphism
    GP(n,k) ≃g GP(n,l);
  * `indepPoly_iso`: isomorphic graphs have the same independence polynomial;
  * `part_a` (Theorem 1.1(a)): for every n ≡ 3 (mod 4), n ≥ 7, GP(n,2) ≃g GP(n,(n-1)/2), the step
    (n-1)/2 is odd and both pairs satisfy n ≥ 2k + 1;
  * `parity_conjecture_fails_at`: hence for every such n the conjecture fails at (n,2) or at
    (n,(n-1)/2), and `parity_conjecture_false`: the conjecture, as stated, is false;
  * `part_b` (Theorem 1.1(b)): P = 1 + 14x + 70x² + 154x³ + 147x⁴ + 49x⁵ has only real roots;
  * `part_c` (Theorem 1.1(c)): Q = 1 + 18x + 126x² + 438x³ + 801x⁴ + 747x⁵ + 303x⁶ + 27x⁷ has
    exactly five real roots counted with multiplicity, so two of its seven complex roots are not
    real.
  That P = I(GP(7,2)) = I(GP(7,3)) and Q = I(GP(9,2)) is checked by the kernel in `../GPParity.lean`
  and by the C, C++, Python and Julia programs.

  Vertices of GP(n,k) are Bool × ZMod n: (false, i) is u_i and (true, i) is v_i.
  "Only real roots" for p ∈ ℝ[X] means that p has natDegree p real roots counted with multiplicity.
-/
import Mathlib

open Polynomial SimpleGraph Finset

namespace GPParity

/-! ### Generalized Petersen graphs and their isomorphisms -/

/-- the edges u_i u_{i+1}, u_i v_i, v_i v_{i+k}, each in one direction -/
def gpRel (n k : ℕ) (x y : Bool × ZMod n) : Prop :=
  (x.1 = false ∧ y.1 = false ∧ y.2 = x.2 + 1) ∨
  (x.1 = false ∧ y.1 = true ∧ y.2 = x.2) ∨
  (x.1 = true ∧ y.1 = true ∧ y.2 = x.2 + k)

/-- the generalized Petersen graph GP(n,k) -/
def GP (n k : ℕ) : SimpleGraph (Bool × ZMod n) := SimpleGraph.fromRel (gpRel n k)

/-- Lemma 2.1: if kl = ±1 in ZMod n, then u_i ↦ v_{li}, v_i ↦ u_{li} is an isomorphism. -/
theorem gp_iso (n k l : ℕ) (h : (k : ZMod n) * l = 1 ∨ (k : ZMod n) * l = -1) :
    Nonempty (GP n k ≃g GP n l) := by
  obtain ⟨m, hm⟩ : ∃ m : ZMod n, m * l = 1 := by
    rcases h with h | h
    · exact ⟨k, h⟩
    · exact ⟨-k, by rw [neg_mul, h, neg_neg]⟩
  have hinj : ∀ s t : ZMod n, (l : ZMod n) * s = l * t ↔ s = t := by
    intro s t
    constructor
    · intro hst
      calc s = m * l * s := by rw [hm, one_mul]
        _ = m * (l * s) := by ring
        _ = m * (l * t) := by rw [hst]
        _ = m * l * t := by ring
        _ = t := by rw [hm, one_mul]
    · rintro rfl
      rfl
  -- the three kinds of edges, after multiplying by l
  have hout : ∀ s t : ZMod n, (l : ZMod n) * t = l * s + l ↔ t = s + 1 := by
    intro s t
    rw [show (l : ZMod n) * s + l = l * (s + 1) by ring]
    exact hinj _ _
  have hin : ∀ s t : ZMod n, t = s + k ↔ (l : ZMod n) * t = l * s + k * l := by
    intro s t
    rw [show (l : ZMod n) * s + k * l = l * (s + k) by ring]
    exact (hinj _ _).symm
  let e : Bool × ZMod n ≃ Bool × ZMod n :=
    { toFun := fun x => (!x.1, l * x.2)
      invFun := fun y => (!y.1, m * y.2)
      left_inv := fun x => by
        obtain ⟨a, i⟩ := x
        simp only [Bool.not_not, Prod.mk.injEq, true_and]
        rw [← mul_assoc, hm, one_mul]
      right_inv := fun y => by
        obtain ⟨b, j⟩ := y
        simp only [Bool.not_not, Prod.mk.injEq, true_and]
        rw [← mul_assoc, mul_comm (l : ZMod n) m, hm, one_mul] }
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  rintro ⟨a, i⟩ ⟨b, j⟩
  have hne : (e (a, i) ≠ e (b, j)) ↔ ((a, i) ≠ (b, j)) := e.injective.ne_iff
  simp only [GP, fromRel_adj]
  rw [hne]
  apply and_congr_right
  intro _
  simp only [gpRel, e, Equiv.coe_fn_mk]
  cases a <;> cases b <;> simp only [Bool.not_false, Bool.not_true, true_and, false_and, and_false,
    or_false, false_or, Bool.false_eq_true, reduceCtorEq]
  · -- two outer vertices go to two inner vertices
    rw [hout, hout]
  · -- u_i, v_j
    rw [hinj]
    exact eq_comm
  · -- v_i, u_j
    rw [hinj]
    exact eq_comm
  · -- two inner vertices go to two outer vertices
    rw [hin, hin]
    rcases h with h | h
    · rw [h]
    · rw [h, or_comm]
      constructor <;> rintro (h' | h') <;> [left; right; left; right] <;> linear_combination -h'

/-! ### Independence polynomials -/

open Classical in
/-- I(G; x): the sum of x^|s| over the independent vertex sets s of G -/
noncomputable def indepPoly {V : Type*} [Fintype V] (G : SimpleGraph V) : ℝ[X] :=
  ∑ s ∈ univ.filter (fun s : Finset V => G.IsIndepSet (s : Set V)), X ^ s.card

/-- isomorphic graphs have the same independence polynomial -/
theorem indepPoly_iso {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) : indepPoly G = indepPoly H := by
  classical
  unfold indepPoly
  refine Finset.sum_equiv e.toEquiv.finsetCongr (fun s => ?_) (fun s _ => ?_)
  · simp only [mem_filter, mem_univ, true_and, Equiv.finsetCongr_apply, coe_map]
    rw [isIndepSet_iff, isIndepSet_iff]
    constructor
    · rintro hs _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab hadj
      exact hs ha hb (fun h => hab (h ▸ rfl)) (e.map_adj_iff.1 hadj)
    · intro hs a ha b hb hab hadj
      exact hs (Set.mem_image_of_mem _ ha) (Set.mem_image_of_mem _ hb)
        (fun h => hab (e.injective h)) (e.map_adj_iff.2 hadj)
  · simp [Equiv.finsetCongr_apply]

/-- p has only real roots: natDegree p real roots counted with multiplicity -/
def RealRooted (p : ℝ[X]) : Prop := Multiset.card p.roots = p.natDegree

/-- Conjecture 4.1 of Pandey, as stated -/
def ParityConjecture : Prop :=
  ∀ (n : ℕ) [NeZero n] (k : ℕ), 1 ≤ k → 2 * k + 1 ≤ n →
    (RealRooted (indepPoly (GP n k)) ↔ Even k)

/-- Theorem 1.1(a) -/
theorem part_a (n : ℕ) (hn : n % 4 = 3) (h7 : 7 ≤ n) :
    Nonempty (GP n 2 ≃g GP n ((n - 1) / 2)) ∧ Odd ((n - 1) / 2) ∧ 2 * 2 + 1 ≤ n ∧
      2 * ((n - 1) / 2) + 1 ≤ n := by
  refine ⟨gp_iso n 2 ((n - 1) / 2) (Or.inr ?_), ⟨(n - 3) / 4, by omega⟩, by omega, by omega⟩
  have h2 : 2 * ((n - 1) / 2) + 1 = n := by omega
  have h0 : ((2 * ((n - 1) / 2) + 1 : ℕ) : ZMod n) = 0 := by
    rw [h2]
    exact ZMod.natCast_self n
  push_cast at h0
  linear_combination h0

/-- For every n ≡ 3 (mod 4), n ≥ 7, the conjecture fails at (n,2) or at (n,(n-1)/2). -/
theorem parity_conjecture_fails_at (n : ℕ) [NeZero n] (hn : n % 4 = 3) (h7 : 7 ≤ n) :
    ¬ (RealRooted (indepPoly (GP n 2)) ↔ Even 2) ∨
      ¬ (RealRooted (indepPoly (GP n ((n - 1) / 2))) ↔ Even ((n - 1) / 2)) := by
  obtain ⟨⟨e⟩, hodd, -, -⟩ := part_a n hn h7
  rw [← indepPoly_iso e]
  by_contra! h
  exact (Nat.not_even_iff_odd.mpr hodd) (h.2.1 (h.1.2 even_two))

/-- The conjecture is false. -/
theorem parity_conjecture_false : ¬ ParityConjecture := by
  intro H
  have h := parity_conjecture_fails_at 7 (by norm_num) (by norm_num)
  rcases h with h | h
  · exact h (H 7 2 (by norm_num) (by norm_num))
  · exact h (H 7 3 (by norm_num) (by norm_num))

/-! ### Theorem 1.1(b) and (c) -/

/-- I(GP(7,2); x) = I(GP(7,3); x) -/
noncomputable def P : ℝ[X] :=
  C 49 * X ^ 5 + C 147 * X ^ 4 + C 154 * X ^ 3 + C 70 * X ^ 2 + C 14 * X + 1

/-- I(GP(9,2); x) -/
noncomputable def Q : ℝ[X] :=
  C 27 * X ^ 7 + C 303 * X ^ 6 + C 747 * X ^ 5 + C 801 * X ^ 4 + C 438 * X ^ 3 + C 126 * X ^ 2 +
    C 18 * X + 1

lemma P_eval (x : ℝ) : P.eval x = 49 * x ^ 5 + 147 * x ^ 4 + 154 * x ^ 3 + 70 * x ^ 2 + 14 * x + 1 := by
  simp [P]

lemma Q_eval (x : ℝ) : Q.eval x =
    27 * x ^ 7 + 303 * x ^ 6 + 747 * x ^ 5 + 801 * x ^ 4 + 438 * x ^ 3 + 126 * x ^ 2 + 18 * x + 1 := by
  simp [Q]

lemma P_natDegree : P.natDegree = 5 := by
  unfold P
  compute_degree!

lemma Q_natDegree : Q.natDegree = 7 := by
  unfold Q
  compute_degree!

lemma P_ne_zero : P ≠ 0 := by
  intro h
  have := P_natDegree
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

lemma Q_ne_zero : Q ≠ 0 := by
  intro h
  have := Q_natDegree
  rw [h, natDegree_zero] at this
  exact absurd this (by norm_num)

/-- a sign change gives a root in between -/
lemma root_of_sign_change (p : ℝ[X]) {a b : ℝ} (hab : a < b) (h : p.eval a * p.eval b < 0) :
    ∃ c, a < c ∧ c < b ∧ p.eval c = 0 := by
  rcases mul_neg_iff.1 h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨hb, ha⟩
    exact ⟨c, hc.1, hc.2, hc0⟩
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨ha, hb⟩
    exact ⟨c, hc.1, hc.2, hc0⟩

/-- five roots x₁ < ⋯ < x₅ of p ≠ 0 form a sub-multiset of its roots -/
lemma five_le_roots (p : ℝ[X]) (hp : p ≠ 0) {x₁ x₂ x₃ x₄ x₅ : ℝ}
    (h12 : x₁ < x₂) (h23 : x₂ < x₃) (h34 : x₃ < x₄) (h45 : x₄ < x₅)
    (r₁ : p.eval x₁ = 0) (r₂ : p.eval x₂ = 0) (r₃ : p.eval x₃ = 0) (r₄ : p.eval x₄ = 0)
    (r₅ : p.eval x₅ = 0) :
    ({x₁, x₂, x₃, x₄, x₅} : Multiset ℝ) ≤ p.roots := by
  rw [Multiset.le_iff_subset]
  · intro x hx
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rw [mem_roots hp]
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, Multiset.nodup_singleton, not_or]
    repeat' apply And.intro
    all_goals first | trivial | (intro h; linarith)

/-- Theorem 1.1(b): P has five real roots, one in each of five disjoint intervals, so it has
    only real roots. -/
theorem part_b : RealRooted P := by
  obtain ⟨x₁, a₁, b₁, h₁⟩ := root_of_sign_change P (a := -7/5) (b := -13/10) (by norm_num)
    (by rw [P_eval, P_eval]; norm_num)
  obtain ⟨x₂, a₂, b₂, h₂⟩ := root_of_sign_change P (a := -1) (b := -3/5) (by norm_num)
    (by rw [P_eval, P_eval]; norm_num)
  obtain ⟨x₃, a₃, b₃, h₃⟩ := root_of_sign_change P (a := -3/5) (b := -3/10) (by norm_num)
    (by rw [P_eval, P_eval]; norm_num)
  obtain ⟨x₄, a₄, b₄, h₄⟩ := root_of_sign_change P (a := -3/10) (b := -1/5) (by norm_num)
    (by rw [P_eval, P_eval]; norm_num)
  obtain ⟨x₅, a₅, b₅, h₅⟩ := root_of_sign_change P (a := -1/5) (b := -1/10) (by norm_num)
    (by rw [P_eval, P_eval]; norm_num)
  have hle := five_le_roots P P_ne_zero (by linarith) (by linarith) (by linarith) (by linarith)
    h₁ h₂ h₃ h₄ h₅
  have h5 := Multiset.card_le_card hle
  have h7 := card_roots' P
  simp only [Multiset.insert_eq_cons, Multiset.card_cons, Multiset.card_singleton] at h5
  unfold RealRooted
  rw [P_natDegree] at h7 ⊢
  omega

/-- if p ≠ 0 is the product of the factors X - a over its roots times g, then g has no root -/
lemma quotient_has_no_root (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ g : ℝ[X], g.roots = 0 ∧ g.natDegree + Multiset.card p.roots = p.natDegree := by
  obtain ⟨g, hg⟩ := p.prod_multiset_X_sub_C_dvd
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hg
    exact hp hg
  refine ⟨g, ?_, ?_⟩
  · have h := roots_mul (hg ▸ hp)
    rw [← hg, roots_multiset_prod_X_sub_C] at h
    simpa using h.symm
  · have h := natDegree_mul (monic_multisetProd_X_sub_C p.roots).ne_zero hg0
    rw [← hg, natDegree_multiset_prod_X_sub_C_eq_card] at h
    omega

lemma Q_leadingCoeff : Q.leadingCoeff = 27 := by
  rw [leadingCoeff, Q_natDegree]
  simp [Q, coeff_X_pow, coeff_one]

lemma Q_nextCoeff : Q.nextCoeff = 303 := by
  rw [nextCoeff_of_natDegree_pos (by rw [Q_natDegree]; norm_num), Q_natDegree]
  simp [Q, coeff_X_pow, coeff_one]

set_option maxHeartbeats 1000000 in
/-- Theorem 1.1(c): Q has exactly five real roots counted with multiplicity, so it does not have
    only real roots. -/
theorem part_c : Multiset.card Q.roots = 5 ∧ ¬ RealRooted Q := by
  obtain ⟨ρ₁, a₁, b₁, h₁⟩ := root_of_sign_change Q (a := -828862/100000) (b := -828861/100000)
    (by norm_num) (by rw [Q_eval, Q_eval]; norm_num)
  obtain ⟨ρ₂, a₂, b₂, h₂⟩ := root_of_sign_change Q (a := -51657/100000) (b := -51656/100000)
    (by norm_num) (by rw [Q_eval, Q_eval]; norm_num)
  obtain ⟨ρ₃, a₃, b₃, h₃⟩ := root_of_sign_change Q (a := -31262/100000) (b := -31261/100000)
    (by norm_num) (by rw [Q_eval, Q_eval]; norm_num)
  obtain ⟨ρ₄, a₄, b₄, h₄⟩ := root_of_sign_change Q (a := -22263/100000) (b := -22262/100000)
    (by norm_num) (by rw [Q_eval, Q_eval]; norm_num)
  obtain ⟨ρ₅, a₅, b₅, h₅⟩ := root_of_sign_change Q (a := -16871/100000) (b := -16870/100000)
    (by norm_num) (by rw [Q_eval, Q_eval]; norm_num)
  have hle := five_le_roots Q Q_ne_zero (by linarith) (by linarith) (by linarith) (by linarith)
    h₁ h₂ h₃ h₄ h₅
  obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.1 hle
  have hcard : Multiset.card Q.roots = 5 + Multiset.card t := by
    rw [ht, Multiset.card_add]
    simp
  have hmax := card_roots' Q
  rw [Q_natDegree] at hmax
  -- six real roots are impossible: the quotient would be linear and have a root
  have h6 : Multiset.card t ≠ 1 := by
    intro h1
    obtain ⟨g, hg, hdeg⟩ := quotient_has_no_root Q Q_ne_zero
    rw [Q_natDegree, hcard, h1] at hdeg
    have hg1 : g.degree = 1 := by
      rw [degree_eq_natDegree (by rintro rfl; simp at hdeg)]
      norm_cast
      omega
    obtain ⟨c, hc⟩ := exists_root_of_degree_eq_one hg1
    have : c ∈ g.roots := (mem_roots (by rintro rfl; simp at hg1)).2 hc
    rw [hg] at this
    simp at this
  -- seven real roots are impossible, by the relations between roots and coefficients
  have h7 : Multiset.card t ≠ 2 := by
    intro h2
    obtain ⟨r, r', hrr⟩ := Multiset.card_eq_two.1 h2
    have hroots : Multiset.card Q.roots = Q.natDegree := by rw [Q_natDegree, hcard, h2]
    have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
    rw [Q_leadingCoeff, ht, hrr] at hfac
    have hprod := congrArg (eval 0) hfac
    have hsum := congrArg nextCoeff hfac
    rw [nextCoeff_C_mul, multiset_prod_X_sub_C_nextCoeff, Q_nextCoeff] at hsum
    simp only [Multiset.insert_eq_cons, Multiset.sum_add, Multiset.sum_cons,
      Multiset.sum_singleton] at hsum
    simp only [eval_mul, eval_C, Multiset.insert_eq_cons, Multiset.map_add,
      Multiset.map_cons, Multiset.map_singleton, Multiset.prod_add, Multiset.prod_cons,
      Multiset.prod_singleton, eval_sub, eval_X, zero_sub, Q_eval] at hprod
    -- the products of the |ρ_i|
    have q₁ : 0 < -ρ₁ := by linarith
    have q₂ : 0 < -ρ₂ := by linarith
    have q₃ : 0 < -ρ₃ := by linarith
    have q₄ : 0 < -ρ₄ := by linarith
    have q₅ : 0 < -ρ₅ := by linarith
    have p12 : -ρ₁ * -ρ₂ < (828862/100000) * (51657/100000) :=
      mul_lt_mul'' (by linarith) (by linarith) q₁.le q₂.le
    have p123 : -ρ₁ * -ρ₂ * -ρ₃ < (828862/100000) * (51657/100000) * (31262/100000) :=
      mul_lt_mul'' p12 (by linarith) (mul_pos q₁ q₂).le q₃.le
    have p1234 : -ρ₁ * -ρ₂ * -ρ₃ * -ρ₄ <
        (828862/100000) * (51657/100000) * (31262/100000) * (22263/100000) :=
      mul_lt_mul'' p123 (by linarith) (mul_pos (mul_pos q₁ q₂) q₃).le q₄.le
    have p12345 : -ρ₁ * -ρ₂ * -ρ₃ * -ρ₄ * -ρ₅ <
        (828862/100000) * (51657/100000) * (31262/100000) * (22263/100000) * (16871/100000) :=
      mul_lt_mul'' p1234 (by linarith) (mul_pos (mul_pos (mul_pos q₁ q₂) q₃) q₄).le q₅.le
    obtain ⟨π₀, hπ₀⟩ : ∃ x : ℝ, x = -ρ₁ * -ρ₂ * -ρ₃ * -ρ₄ * -ρ₅ := ⟨_, rfl⟩
    have hπpos : 0 < π₀ := by
      rw [hπ₀]
      exact mul_pos (mul_pos (mul_pos (mul_pos q₁ q₂) q₃) q₄) q₅
    have hnum : (828862/100000 : ℝ) * (51657/100000) * (31262/100000) * (22263/100000) *
        (16871/100000) < 50278 / 1000000 := by norm_num
    have hπ : π₀ < 50278 / 1000000 := by rw [hπ₀]; linarith
    -- 27 π₀ r r' = 1 and r + r' = -303/27 - Σ ρ_i
    have hq : 27 * π₀ * (r * r') = 1 := by
      rw [hπ₀]
      linear_combination hprod
    have hs : r + r' = -303 / 27 - (ρ₁ + ρ₂ + ρ₃ + ρ₄ + ρ₅) := by
      linear_combination -hsum / 27
    have hs_lo : -1713123 / 1000000 < r + r' := by rw [hs]; linarith
    have hs_hi : r + r' < -1713071 / 1000000 := by rw [hs]; linarith
    have hs2 : (r + r') ^ 2 < 29348 / 10000 := by
      have h1 := mul_neg_of_pos_of_neg (show (0:ℝ) < r + r' + 1713123 / 1000000 by linarith)
        (show r + r' - 1713123 / 1000000 < (0:ℝ) by linarith)
      calc (r + r') ^ 2 = (r + r' + 1713123 / 1000000) * (r + r' - 1713123 / 1000000) +
            (1713123 / 1000000) ^ 2 := by ring
        _ < 0 + (1713123 / 1000000) ^ 2 := by linarith
        _ < 29348 / 10000 := by norm_num
    have hq' : π₀ * (r * r') = 1 / 27 := by linear_combination hq / 27
    have hqpos : 0 < r * r' := by
      by_contra! hneg
      have := mul_nonpos_of_nonneg_of_nonpos hπpos.le hneg
      linarith
    have hq_lo : 7366 / 10000 < r * r' := by
      have := mul_lt_mul_of_pos_right hπ hqpos
      linarith
    have hdisc : (r - r') ^ 2 = (r + r') ^ 2 - 4 * (r * r') := by ring
    linarith [sq_nonneg (r - r')]
  refine ⟨?_, ?_⟩
  · have : Multiset.card t ≤ 2 := by omega
    have : Multiset.card t = 0 := by omega
    omega
  · unfold RealRooted
    rw [Q_natDegree]
    omega

#print axioms parity_conjecture_false
#print axioms part_b
#print axioms part_c

end GPParity
