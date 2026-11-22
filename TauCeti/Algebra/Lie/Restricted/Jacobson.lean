/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Free
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Matrix.CharP
import TauCeti.Algebra.CharP.Lemmas
import TauCeti.Algebra.Lie.AdjointAction.Frobenius
import TauCeti.Algebra.Polynomial.Derivative

/-!
# Jacobson's formula

In an associative algebra of prime characteristic `p` the Frobenius `a ↦ a ^ p` is not additive,
but its failure to be additive is a Lie polynomial: Jacobson's formula reads

`(a + b) ^ p = a ^ p + b ^ p + Λ_p(a, b)`,

where `Λ_p(x, y) = ∑_{0 < i < p} s_i(x, y)` and `i • s_i(x, y)` is the coefficient of `t ^ (i - 1)`
in `ad(t x + y) ^ (p - 1) (x)`. This is the identity behind the axioms of a restricted Lie algebra,
whose `p`-map satisfies `(x + y)^[p] = x^[p] + y^[p] + Λ_p(x, y)`, and behind the additivity of
the `p`-th power of derivations and of the `p`-curvature of a flat connection.

We work in an arbitrary Lie ring `L`. `jacobsonCoeff x y k j` is the coefficient of `t ^ j` in
`ad(t x + y) ^ k (x)`, defined by the recursion that `ad(t x + y)` induces on coefficients;
equivalently it is the sum, over the words `z_1 ⋯ z_k` in the letters `x, y` with exactly `j`
letters `x`, of the brackets `⁅z_1, ⁅z_2, … ⁅z_k, x⁆ …⁆⁆`. The value of Jacobson's polynomial is
`jacobson p x y = ∑_{j < p - 1} c_j • jacobsonCoeff x y (p - 1) j`, where `c_j` is the
natural-number representative of `(j + 1)⁻¹` modulo `p`. Since the coefficients are natural
numbers, `jacobson p x y` makes sense in every Lie ring, and `jacobsonLie R p` is the universal
case, the Lie polynomial in the free Lie algebra on two generators over any commutative ring `R`.

## Main definitions

* `TauCeti.LieAlgebra.jacobsonCoeff`: the coefficients of `t ↦ ad(t x + y) ^ k (x)`.
* `TauCeti.LieAlgebra.jacobson`: the value `Λ_p(x, y)` of Jacobson's Lie polynomial.
* `TauCeti.LieAlgebra.jacobsonLie`: Jacobson's Lie polynomial in `FreeLieAlgebra R (Fin 2)`.

## Main statements

* `TauCeti.LieAlgebra.add_pow_eq_jacobson`: **Jacobson's formula**,
  `(a + b) ^ p = a ^ p + b ^ p + jacobson p a b` in a ring of exponential characteristic `p`.
* `LieHom.map_jacobson`, `TauCeti.LieAlgebra.lift_jacobsonLie`: `Λ_p` is natural for Lie algebra
  morphisms, and is the value of the Lie polynomial `jacobsonLie R p`.
* `TauCeti.LieAlgebra.jacobson_eq_zero_of_lie_eq_zero`: `Λ_p(x, y) = 0` when `⁅x, y⁆ = 0`.
* `TauCeti.LieAlgebra.jacobson_smul_smul`: `p`-homogeneity `Λ_p(c • x, c • y) = c ^ p • Λ_p(x, y)`.
* `TauCeti.LieAlgebra.jacobson_eq_ad_pow_of_lie_ad_pow_eq_zero`: rank-one collapse
  `Λ_p(x, y) = (ad R L y ^ (p - 1)) x` when `⁅x, (ad R L y ^ k) x⁆ = 0` for all `k` (`1 < p`).
* `TauCeti.LieAlgebra.sum_nsmul_jacobsonCoeff_eq_jacobson`: when `p • z = 0` for every `z`, any
  choice of representatives of the inverses `(j + 1)⁻¹` modulo `p` gives the same value.
* `TauCeti.LieAlgebra.jacobson_two`, `TauCeti.LieAlgebra.jacobson_three`:
  `Λ_2(x, y) = ⁅y, x⁆` and `Λ_3(x, y) = ⁅y, ⁅y, x⁆⁆ + 2 • ⁅x, ⁅y, x⁆⁆`.
* `TauCeti.LieAlgebra.jacobson_single_single`: for `2 × 2` matrices over `ZMod p`, `p` odd,
  `Λ_p(E₀₁, E₁₀) = E₀₁ + E₁₀`, so the Lie term of Jacobson's formula does not vanish.

## Implementation notes

The proof of Jacobson's formula is the classical one. In the polynomial ring `A[t]`, put
`P = (C a * t + C b) ^ p`. Its coefficients in degrees `0` and `p` are `b ^ p` and `a ^ p`, and the
sum of all its coefficients is `(a + b) ^ p`. Its derivative is
`∑_{m < p} (C a * t + C b) ^ m * C a * (C a * t + C b) ^ (p - 1 - m)`, which in characteristic `p`
is the `(p - 1)`-fold commutator of `C a * t + C b` with `C a`
(`TauCeti.LieAlgebra.ad_pow_sub_one_apply`); its coefficients are the `jacobsonCoeff a b (p - 1) j`.
Comparing coefficients, `(j + 1) • P_{j + 1} = jacobsonCoeff a b (p - 1) j`, and `j + 1` is
invertible modulo `p` for `j < p - 1`.

## References

* N. Jacobson, *Abstract derivation and Lie algebras*, Trans. Amer. Math. Soc. **42** (1937),
  206–224.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), 175–232, (5.2.4)–(5.2.5).
* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V, §7.
-/

public section

open Finset Polynomial

namespace TauCeti.LieAlgebra

section LieRing

variable {L : Type*} [LieRing L]

/-- The coefficient of `t ^ j` in `ad(t x + y) ^ k (x)`: the sum, over the words `z_1 ⋯ z_k` in
the letters `x, y` containing exactly `j` letters `x`, of the brackets
`⁅z_1, ⁅z_2, … ⁅z_k, x⁆ …⁆⁆`. -/
def jacobsonCoeff (x y : L) : ℕ → ℕ → L
  | 0, 0 => x
  | 0, _ + 1 => 0
  | k + 1, 0 => ⁅y, jacobsonCoeff x y k 0⁆
  | k + 1, j + 1 => ⁅x, jacobsonCoeff x y k j⁆ + ⁅y, jacobsonCoeff x y k (j + 1)⁆

@[simp]
theorem jacobsonCoeff_zero_zero (x y : L) : jacobsonCoeff x y 0 0 = x := by
  simp [jacobsonCoeff]

@[simp]
theorem jacobsonCoeff_zero_succ (x y : L) (j : ℕ) : jacobsonCoeff x y 0 (j + 1) = 0 := by
  simp [jacobsonCoeff]

@[simp]
theorem jacobsonCoeff_succ_zero (x y : L) (k : ℕ) :
    jacobsonCoeff x y (k + 1) 0 = ⁅y, jacobsonCoeff x y k 0⁆ := by
  simp [jacobsonCoeff]

@[simp]
theorem jacobsonCoeff_succ_succ (x y : L) (k j : ℕ) :
    jacobsonCoeff x y (k + 1) (j + 1) =
      ⁅x, jacobsonCoeff x y k j⁆ + ⁅y, jacobsonCoeff x y k (j + 1)⁆ := by
  simp [jacobsonCoeff]

/-- The value `Λ_p(x, y)` of Jacobson's Lie polynomial: the sum over `j < p - 1` of
`jacobsonCoeff x y (p - 1) j`, weighted by the natural-number representative of `(j + 1)⁻¹`
modulo `p`. -/
def jacobson (p : ℕ) (x y : L) : L :=
  ∑ j ∈ range (p - 1), ((j + 1 : ZMod p)⁻¹).val • jacobsonCoeff x y (p - 1) j

theorem jacobson_def (p : ℕ) (x y : L) :
    jacobson p x y =
      ∑ j ∈ range (p - 1), ((j + 1 : ZMod p)⁻¹).val • jacobsonCoeff x y (p - 1) j := by
  simp [jacobson]

/-- If `x` and `y` commute, every bracket `⁅z_1, … ⁅z_k, x⁆ …⁆` with `k ≥ 1` vanishes. -/
theorem jacobsonCoeff_succ_eq_zero_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) (k j : ℕ) :
    jacobsonCoeff x y (k + 1) j = 0 := by
  induction k generalizing j with
  | zero =>
    rcases j with _ | _ | j <;> simp [← lie_skew y x, h]
  | succ k ih =>
    cases j
    · rw [jacobsonCoeff_succ_zero, ih, lie_zero]
    · rw [jacobsonCoeff_succ_succ, ih, ih, lie_zero, lie_zero, add_zero]

/-- Jacobson's polynomial vanishes on commuting elements. -/
theorem jacobson_eq_zero_of_lie_eq_zero (p : ℕ) {x y : L} (h : ⁅x, y⁆ = 0) :
    jacobson p x y = 0 := by
  refine sum_eq_zero fun j hj ↦ ?_
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = k + 1 := ⟨p - 2, by grind⟩
  rw [hk, jacobsonCoeff_succ_eq_zero_of_lie_eq_zero h, smul_zero]

/-- `Λ_0(x, y) = 0`. -/
@[simp]
theorem jacobson_zero (x y : L) : jacobson 0 x y = 0 := by
  simp [jacobson_def]

/-- `Λ_1(x, y) = 0`. -/
@[simp]
theorem jacobson_one (x y : L) : jacobson 1 x y = 0 := by
  simp [jacobson_def]

/-- `Λ_p(0, y) = 0` for every `p : ℕ`. -/
@[simp]
theorem jacobson_zero_left (p : ℕ) (y : L) : jacobson p 0 y = 0 :=
  jacobson_eq_zero_of_lie_eq_zero p (zero_lie y)

/-- `Λ_p(x, 0) = 0` for every `p : ℕ`. -/
@[simp]
theorem jacobson_zero_right (p : ℕ) (x : L) : jacobson p x 0 = 0 :=
  jacobson_eq_zero_of_lie_eq_zero p (lie_zero x)

/-- `Λ_p(x, x) = 0` for every `p : ℕ`. -/
@[simp]
theorem jacobson_self (p : ℕ) (x : L) : jacobson p x x = 0 :=
  jacobson_eq_zero_of_lie_eq_zero p (lie_self x)

/-- `Λ_2(x, y) = ⁅y, x⁆`. -/
@[simp]
theorem jacobson_two (x y : L) : jacobson 2 x y = ⁅y, x⁆ := by
  simp [jacobson_def, show (1 : ZMod 2).val = 1 by decide]

/-- `Λ_3(x, y) = ⁅y, ⁅y, x⁆⁆ + 2 • ⁅x, ⁅y, x⁆⁆`: the word `y y` has weight `1⁻¹ = 1` and the
words `x y`, `y x` have weight `2⁻¹ = 2` modulo `3`. -/
theorem jacobson_three (x y : L) : jacobson 3 x y = ⁅y, ⁅y, x⁆⁆ + 2 • ⁅x, ⁅y, x⁆⁆ := by
  have h2 : ((1 + 1 : ZMod 3)⁻¹).val = 2 := by
    rw [ZMod.inv_eq_of_mul_eq_one 3 (1 + 1) 2 (by decide)]
    decide
  rw [jacobson_def, show 3 - 1 = 1 + 1 from rfl]
  simp [sum_range_succ, h2, show (1 : ZMod 3).val = 1 by decide]

/-- **Independence of the representatives.**  If `p • z = 0` for every `z : L`, the value of
Jacobson's polynomial does not depend on the natural numbers chosen to represent the inverses
`(j + 1)⁻¹` modulo `p`. -/
theorem sum_nsmul_jacobsonCoeff_eq_jacobson {p : ℕ} (hL : ∀ z : L, p • z = 0) (c : ℕ → ℕ)
    (hc : ∀ j < p - 1, (c j : ZMod p) * (j + 1) = 1) (x y : L) :
    ∑ j ∈ range (p - 1), c j • jacobsonCoeff x y (p - 1) j = jacobson p x y := by
  rcases p.eq_zero_or_pos with rfl | hp
  · simp [jacobson_def]
  have : NeZero p := ⟨hp.ne'⟩
  have hmod : ∀ (m : ℕ) (z : L), m • z = (m % p) • z := fun m z ↦ by
    conv_lhs => rw [← Nat.mod_add_div m p, add_nsmul, mul_comm, mul_nsmul, hL, add_zero]
  refine sum_congr rfl fun j hj ↦ ?_
  have hcj : (c j : ZMod p) = (((j + 1 : ZMod p)⁻¹).val : ℕ) := by
    rw [ZMod.natCast_zmod_val,
      ZMod.inv_eq_of_mul_eq_one _ _ _ ((mul_comm _ _).trans (hc j (mem_range.1 hj)))]
  rw [ZMod.natCast_eq_natCast_iff'] at hcj
  rw [hmod (c j), hcj, ← hmod]

end LieRing

section LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Homogeneity of the Jacobson coefficients:
`jacobsonCoeff (c • x) (c • y) k j = c ^ (k + 1) • jacobsonCoeff x y k j`. -/
theorem jacobsonCoeff_smul_smul (c : R) (x y : L) (k j : ℕ) :
    jacobsonCoeff (c • x) (c • y) k j = c ^ (k + 1) • jacobsonCoeff x y k j := by
  induction k generalizing j with
  | zero => cases j <;> simp
  | succ k ih =>
    cases j with
    | zero =>
      rw [jacobsonCoeff_succ_zero, ih, smul_lie, lie_smul, smul_smul, ← pow_succ',
        jacobsonCoeff_succ_zero]
    | succ j =>
      rw [jacobsonCoeff_succ_succ, ih, ih, smul_lie, lie_smul, smul_lie, lie_smul, smul_smul,
        smul_smul, ← pow_succ', ← smul_add, jacobsonCoeff_succ_succ]

/-- Homogeneity of Jacobson's Lie polynomial:
`Λ_p(c • x, c • y) = c ^ p • Λ_p(x, y)`. -/
theorem jacobson_smul_smul (p : ℕ) (c : R) (x y : L) :
    jacobson p (c • x) (c • y) = c ^ p • jacobson p x y := by
  rcases p with _ | p
  · simp
  · rw [jacobson_def, jacobson_def, Finset.smul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [jacobsonCoeff_smul_smul, Nat.add_sub_cancel, smul_comm]

/-- The `j = 0` Jacobson coefficient `jacobsonCoeff x y k 0` is `(ad R L y ^ k) x`. -/
theorem jacobsonCoeff_zero_eq_ad_pow (x y : L) (k : ℕ) :
    jacobsonCoeff x y k 0 = (LieAlgebra.ad R L y ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [jacobsonCoeff_succ_zero, ih, pow_succ', mul_apply_eq_comp, LieAlgebra.ad_apply]

private theorem jacobsonCoeff_succ_eq_zero_of_lie_ad_pow_eq_zero {x y : L}
    (h : ∀ k, ⁅x, (LieAlgebra.ad R L y ^ k) x⁆ = 0) (k j : ℕ) :
    jacobsonCoeff x y k (j + 1) = 0 := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    cases j with
    | zero =>
      rw [jacobsonCoeff_succ_succ, jacobsonCoeff_zero_eq_ad_pow (R := R), h k, ih 0, lie_zero,
        add_zero]
    | succ j =>
      rw [jacobsonCoeff_succ_succ, ih j, ih (j + 1), lie_zero, lie_zero, add_zero]

/-- **Rank-one collapse of Jacobson's Lie polynomial.** If `1 < p` and `x` commutes with
`(ad R L y ^ k) x` for every `k : ℕ`, then only `jacobsonCoeff x y (p - 1) 0` survives in
`Λ_p(x, y)`, yielding `jacobson p x y = (LieAlgebra.ad R L y ^ (p - 1)) x`. -/
theorem jacobson_eq_ad_pow_of_lie_ad_pow_eq_zero {p : ℕ} (hp : 1 < p) {x y : L}
    (h : ∀ k, ⁅x, (LieAlgebra.ad R L y ^ k) x⁆ = 0) :
    jacobson p x y = (LieAlgebra.ad R L y ^ (p - 1)) x := by
  rw [jacobson_def, Finset.sum_eq_single 0]
  · simp [ZMod.val_one'' (by omega : p ≠ 1), jacobsonCoeff_zero_eq_ad_pow (R := R)]
  · intro j _ hj0
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    rw [jacobsonCoeff_succ_eq_zero_of_lie_ad_pow_eq_zero (R := R) h, smul_zero]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

end LieAlgebra

end TauCeti.LieAlgebra

open TauCeti.LieAlgebra in
/-- The coefficients `jacobsonCoeff` are natural for Lie algebra morphisms. -/
@[simp]
theorem LieHom.map_jacobsonCoeff {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') (x y : L) (k j : ℕ) :
    f (jacobsonCoeff x y k j) = jacobsonCoeff (f x) (f y) k j := by
  induction k generalizing j with
  | zero => cases j <;> simp
  | succ k ih => cases j <;> simp [ih]

open TauCeti.LieAlgebra in
/-- **Naturality of Jacobson's polynomial.**  A Lie algebra morphism maps `Λ_p(x, y)` to
`Λ_p(f x, f y)`. -/
@[simp]
theorem LieHom.map_jacobson {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') (p : ℕ) (x y : L) :
    f (jacobson p x y) = jacobson p (f x) (f y) := by
  simp [jacobson_def, map_sum, map_nsmul]

namespace TauCeti.LieAlgebra

/-- **Jacobson's Lie polynomial** `Λ_p(x, y)` in the free Lie algebra over `R` on the two
generators `x = of R 0` and `y = of R 1`. -/
noncomputable def jacobsonLie (R : Type*) [CommRing R] (p : ℕ) : FreeLieAlgebra R (Fin 2) :=
  jacobson p (FreeLieAlgebra.of R 0) (FreeLieAlgebra.of R 1)

theorem jacobsonLie_def (R : Type*) [CommRing R] (p : ℕ) :
    jacobsonLie R p = jacobson p (FreeLieAlgebra.of R 0) (FreeLieAlgebra.of R 1) := by
  rw [jacobsonLie]

/-- Evaluating the Lie polynomial `jacobsonLie R p` at `x, y` gives `Λ_p(x, y)`. -/
@[simp]
theorem lift_jacobsonLie {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (p : ℕ)
    (x y : L) : FreeLieAlgebra.lift R ![x, y] (jacobsonLie R p) = jacobson p x y := by
  simp [jacobsonLie_def]

section Associative

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A]

/-- The coefficients of `ad(C a * t + C b) ^ k (C a)` in `A[t]` are the `jacobsonCoeff a b k j`. -/
private theorem coeff_ad_pow_apply (a b : A) (k j : ℕ) :
    ((LieAlgebra.ad ℤ A[X] (C a * X + C b) ^ k) (C a)).coeff j = jacobsonCoeff a b k j := by
  induction k generalizing j with
  | zero => cases j <;> simp [coeff_C]
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, LieAlgebra.ad_apply, Ring.lie_def]
    generalize (LieAlgebra.ad ℤ A[X] (C a * X + C b) ^ k) (C a) = q at ih
    rw [add_mul, mul_add, mul_assoc, ← mul_assoc q]
    cases j with
    | zero => simp [ih, Ring.lie_def]
    | succ j =>
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_mul, coeff_mul_C, coeff_mul_X, ih,
        jacobsonCoeff_succ_succ, Ring.lie_def]
      abel

/-- The coefficients of `(C a * t + C b) ^ p` strictly between degrees `0` and `p`. -/
private theorem coeff_pow_succ_eq (p : ℕ) [hp : Fact p.Prime] [CharP A p] (a b : A) {j : ℕ}
    (hj : j < p - 1) :
    ((C a * X + C b) ^ p).coeff (j + 1) =
      ((j + 1 : ZMod p)⁻¹).val • jacobsonCoeff a b (p - 1) j := by
  have : ExpChar A p := ExpChar.prime hp.out
  have hder : ((C a * X + C b) ^ p).coeff (j + 1) * ((j + 1 : ℕ) : A) =
      jacobsonCoeff a b (p - 1) j := by
    rw [← coeff_ad_pow_apply, ad_pow_sub_one_apply p, Nat.cast_succ, ← coeff_derivative,
      derivative_pow_eq_sum]
    simp
  have hinv : ((j + 1 : ℕ) : A) * (((j + 1 : ZMod p)⁻¹).val : A) = 1 := by
    simpa using natCast_mul_natCast_val_inv_eq_one (R := A) p
      (Nat.coprime_comm.1 (Nat.coprime_of_lt_prime (n := j + 1) (by omega) (by omega) hp.out))
  rw [nsmul_eq_mul, ← hder, Nat.cast_comm, mul_assoc, hinv, mul_one]

/-- **Jacobson's formula.**  In a ring of exponential characteristic `p`,
`(a + b) ^ p = a ^ p + b ^ p + Λ_p(a, b)` for the ring commutator. -/
theorem add_pow_eq_jacobson (p : ℕ) [hp : ExpChar A p] (a b : A) :
    (a + b) ^ p = a ^ p + b ^ p + jacobson p a b := by
  obtain _ | ⟨hprime⟩ := hp
  · simp
  · have : Fact p.Prime := ⟨hprime⟩
    have hlin : (C a * X + C b).natDegree ≤ 1 := natDegree_linear_le
    have hdeg : ((C a * X + C b) ^ p).natDegree < p + 1 :=
      (natDegree_pow_le.trans (Nat.mul_le_mul_left p hlin)).trans_lt (by omega)
    -- Evaluating at `t = 1`, which is central, gives the sum of the coefficients.
    have hsum : (a + b) ^ p = ∑ i ∈ range (p + 1), ((C a * X + C b) ^ p).coeff i := by
      let φ := eval₂RingHom' (RingHom.id A) 1 fun _ ↦ Commute.one_right _
      have hφ : φ (C a * X + C b) = a + b := by simp [φ]
      rw [← hφ, ← map_pow]
      simp [φ, eval₂_eq_sum_range' _ hdeg]
    have h0 : ((C a * X + C b) ^ p).coeff 0 = b ^ p := by
      rw [← constantCoeff_apply, map_pow]
      simp
    have htop : ((C a * X + C b) ^ p).coeff p = a ^ p := by
      simpa using coeff_pow_of_natDegree_le (m := p) hlin
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hprime.one_le).symm⟩
    rw [hsum, sum_range_succ, sum_range_succ', h0, htop, jacobson_def, Nat.add_sub_cancel,
      sum_congr rfl fun j hj ↦ coeff_pow_succ_eq (q + 1) a b (by simpa using hj)]
    ac_rfl

/-- For odd `p`, `Λ_p(E₀₁, E₁₀) = E₀₁ + E₁₀ ≠ 0` for the matrix units of `2 × 2` matrices over
`ZMod p`: their `p`-th powers vanish while `(E₀₁ + E₁₀) ^ p = E₀₁ + E₁₀`, so the Frobenius of a
noncommutative ring of characteristic `p` is not additive and the Lie term of Jacobson's formula
is needed. -/
theorem jacobson_single_single (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    jacobson p (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ZMod p)) (Matrix.single 1 0 1) =
      Matrix.single 0 1 1 + Matrix.single 1 0 1 := by
  have : ExpChar (Matrix (Fin 2) (Fin 2) (ZMod p)) p := ExpChar.prime Fact.out
  set a : Matrix (Fin 2) (Fin 2) (ZMod p) := Matrix.single 0 1 1
  set b : Matrix (Fin 2) (Fin 2) (ZMod p) := Matrix.single 1 0 1
  have ha : a ^ 2 = 0 := by simp [a, sq]
  have hb : b ^ 2 = 0 := by simp [b, sq]
  have hab : (a + b) ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a, b, sq, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp
  have hpow : ∀ c : Matrix (Fin 2) (Fin 2) (ZMod p), c ^ p = (c ^ 2) ^ k * c := fun c ↦ by
    rw [← pow_mul, ← pow_succ, ← hk]
  have hk0 : k ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
  have h := add_pow_eq_jacobson p a b
  rw [hpow, hpow a, hpow b, hab, ha, hb, one_pow, one_mul, zero_pow hk0, zero_mul, zero_mul] at h
  simpa using h.symm

end Associative

end TauCeti.LieAlgebra
