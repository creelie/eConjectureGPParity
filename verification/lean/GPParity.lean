/-
  Kernel-checked certificate for
  "The parity conjecture for independence polynomials of generalized Petersen graphs is false".

  GP(n,k) has vertices u_0..u_{n-1} (numbered 0..n-1) and v_0..v_{n-1} (numbered n..2n-1) and the
  edges u_i u_{i+1}, u_i v_i, v_i v_{i+k}, indices mod n.

  * `iso_family`: for every n = 3 (mod 4), 7 ≤ n ≤ 199, the map u_i ↦ v_{li}, v_i ↦ u_{li},
    l = (n-1)/2, sends each of the 3n edges of GP(n,2) to an edge of GP(n,l); l is odd and
    prime to n, so the map is a bijection on vertices and hence an isomorphism.
  * `iso_pairs`: the same for every pair k, l < n/2 with kl = ±1 (mod n), 5 ≤ n ≤ 60.
  * `poly72`, `poly73`, `poly92`: the independence polynomials of GP(7,2), GP(7,3), GP(9,2),
    by enumerating independent sets (each vertex in turn is left out, or taken when none of its
    neighbours has been taken).
  * `signs_b`: Theorem 1.1(b), the seven values of 10^5 P(x), and five sign changes.
  * `signs_c`, `vieta_c`: Theorem 1.1(c), the sign changes of Q in the five brackets and every
    numerical inequality of the Vieta argument, scaled to integers.

  The general statements (Lemma 2.1 for all n, Theorem 1.1(a) for all n = 3 (mod 4), the
  refutation of the conjecture as stated, and the root counts deduced from the sign tables) are
  proved with Mathlib in `mathlib/GPParityMathlib.lean`.
  This file uses Lean 4 core only; every statement is checked by the kernel (`decide +kernel`).
-/

/-- edge test for GP(n,k) -/
def isEdge (n k a b : Nat) : Bool :=
  (a < n && b < n && ((a + 1) % n == b || (b + 1) % n == a)) ||
  (a < n && b == a + n) || (b < n && a == b + n) ||
  (n ≤ a && n ≤ b && a < 2 * n && b < 2 * n &&
    ((a - n + k) % n == b - n || (b - n + k) % n == a - n))

/-- the 3n edges of GP(n,k) -/
def edges (n k : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => [(i, (i + 1) % n), (i, n + i), (n + i, n + (i + k) % n)]

/-- φ(u_i) = v_{li}, φ(v_i) = u_{li} -/
def phi (n l x : Nat) : Nat := if x < n then n + l * x % n else l * (x - n) % n

/-- φ sends every edge of GP(n,k) to an edge of GP(n,l), and l is invertible mod n -/
def isoOK (n k l : Nat) : Bool :=
  Nat.gcd l n == 1 && (edges n k).all fun e => isEdge n l (phi n l e.1) (phi n l e.2)

def family : List Nat := (List.range 200).filter fun n => 7 ≤ n && n % 4 == 3

theorem iso_family :
    family.length = 49 ∧
    family.all (fun n => ((n - 1) / 2) % 2 == 1 && 2 * 2 + 1 ≤ n && 2 * ((n - 1) / 2) + 1 ≤ n &&
      isoOK n 2 ((n - 1) / 2)) = true := by
  decide +kernel

/-- all pairs (n,k,l), 5 ≤ n ≤ 60, 1 ≤ k, l < n/2, kl = ±1 (mod n) -/
def pairs : List (Nat × Nat × Nat) :=
  (List.range 61).flatMap fun n =>
    (List.range n).flatMap fun k =>
      ((List.range n).filter fun l =>
        5 ≤ n && 1 ≤ k && 2 * k < n && 1 ≤ l && 2 * l < n &&
        ((k * l) % n == 1 || (k * l) % n == n - 1)).map fun l => (n, k, l)

theorem iso_pairs : pairs.length = 548 ∧ pairs.all (fun t => isoOK t.1 t.2.1 t.2.2) = true := by
  decide +kernel

theorem iso_13 : isoOK 13 4 3 = true ∧ isoOK 7 2 3 = true := by decide +kernel

/-! Independence polynomials -/

/-- neighbourhood of x in GP(n,k), as a bit mask -/
def nbMask (n k x : Nat) : Nat :=
  (List.range (2 * n)).foldl (fun m y => if isEdge n k x y then m ||| (1 <<< y) else m) 0

/-- coefficientwise sum of two coefficient lists -/
def addL : List Nat → List Nat → List Nat
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addL p q

/-- independent sets of GP(n,k) inside {v, ..., 2n-1} avoiding the mask `forb`, by size;
    `fuel` = 2n - v -/
def ipAux (n k : Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => [1]
  | fuel + 1, v, forb =>
    if forb.testBit v then ipAux n k fuel (v + 1) forb
    else addL (ipAux n k fuel (v + 1) forb)
              (0 :: ipAux n k fuel (v + 1) (forb ||| nbMask n k v))

/-- coefficient list of I(GP(n,k); x), constant term first -/
def indPoly (n k : Nat) : List Nat := ipAux n k (2 * n) 0 0

theorem poly72 : indPoly 7 2 = [1, 14, 70, 154, 147, 49] := by decide +kernel
theorem poly73 : indPoly 7 3 = [1, 14, 70, 154, 147, 49] := by decide +kernel
theorem poly92 : indPoly 9 2 = [1, 18, 126, 438, 801, 747, 303, 27] := by decide +kernel

/-- a_1 = 2n and a_2 = C(2n,2) - 3n for n = 7 and n = 9 -/
theorem low_coeffs : 14 * 13 / 2 - 21 = 70 ∧ 18 * 17 / 2 - 27 = 126 := by decide +kernel

/-! Theorem 1.1(b): with P = 1 + 14x + 70x^2 + 154x^3 + 147x^4 + 49x^5 and x = p/10,
    10^5 P(p/10) = Σ c_i p^i 10^(5-i). -/

def evalScaled (c : List Int) (p : Int) (d : Nat) (s : Int) : Int :=
  -- s^d · c(p/s) for d = deg c
  ((c.zipIdx).map fun (a, i) => a * p ^ i * s ^ (d - i)).foldl (· + ·) 0

def P : List Int := [1, 14, 70, 154, 147, 49]
def Q : List Int := [1, 18, 126, 438, 801, 747, 303, 27]

def ptsB : List Int := [-14, -13, -10, -6, -3, -2, -1]
def valsB : List Int := ptsB.map fun p => evalScaled P p 5 10

def signChanges : List Int → Nat
  | a :: b :: t => (if a * b < 0 then 1 else 0) + signChanges (b :: t)
  | _ => 0

/-- -8733/3125 = -279456/10^5, -697/3125 = -22304/10^5, -39/3125 = -1248/10^5 -/
theorem signs_b :
    valsB = [-279456, 67513, 100000, -22304, 1363, -1248, 16021] ∧ signChanges valsB = 5 ∧
    -8733 * 32 = -279456 ∧ -697 * 32 = -22304 ∧ -39 * 32 = -1248 := by
  decide +kernel

/-! Theorem 1.1(c): brackets in units of 10^-5. -/

def lo : List Int := [-828862, -51657, -31262, -22263, -16871]
def hi : List Int := [-828861, -51656, -31261, -22262, -16870]

/-- 10^35 Q(p / 10^5) -/
def Qs (p : Int) : Int := evalScaled Q p 7 100000

theorem signs_c :
    (lo.zip hi).all (fun (a, b) => Qs a * Qs b < 0) = true ∧
    (Qs (-828862) < 0 ∧ 0 < Qs (-828861) ∧ 0 < Qs (-51657) ∧ Qs (-51656) < 0 ∧
     Qs (-31262) < 0 ∧ 0 < Qs (-31261) ∧ 0 < Qs (-22263) ∧ Qs (-22262) < 0 ∧
     Qs (-16871) < 0 ∧ 0 < Qs (-16870)) ∧
    -828861 < -51657 ∧ -51656 < -31262 ∧ -31261 < -22263 ∧ -22262 < -16871 := by
  decide +kernel

/-- The Vieta inequalities, all in integers:
  * Σ lo = -950915 and Σ hi = -950910 (units of 10^-5);
  * r + r' = -303/27 - Σρ lies strictly between -303/27 + 9.50910 and -303/27 + 9.50915,
    and -1.713123 < -303/27 + 9.50910, -303/27 + 9.50915 < -1.713071;
  * (r + r')^2 < 1.713123^2 < 2.9348;
  * ∏ |lo_i| < 0.050278 · 10^25, so |ρ_1⋯ρ_5| < 0.050278;
  * 1/(27 · 0.050278) > 0.7366 and 4 · 0.7366 = 2.9464 > 2.9348. -/
theorem vieta_c :
    lo.foldl (· + ·) 0 = -950915 ∧ hi.foldl (· + ·) 0 = -950910 ∧
    -- 27·10^5 (r + r') lies in (-303·10^5 + 27·950910, -303·10^5 + 27·950915)
    (-1713123 : Int) * 27 < (-303 * 100000 + 27 * 950910) * 10 ∧
    (-303 * 100000 + 27 * 950915 : Int) * 10 < (-1713071 : Int) * 27 ∧
    (1713123 : Int) ^ 2 < 29348 * 10 ^ 8 ∧
    (828862 * 51657 * 31262 * 22263 * 16871 : Int) < 50278 * 10 ^ 19 ∧
    (10 : Int) ^ 10 > 7366 * 27 * 50278 ∧ 4 * 7366 > (29348 : Int) := by
  decide +kernel

#print axioms iso_family
#print axioms poly92
#print axioms vieta_c
