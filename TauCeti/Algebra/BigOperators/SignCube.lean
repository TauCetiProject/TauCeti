/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.LinearCombination

/-!
# Averages over the sign cube and moments of Rademacher sums

The *sign cube* of a finite type `ι` is the finite group `ι → ℤˣ` of sign vectors. Averaging over
it is the expectation with respect to independent symmetric random signs `εᵢ`, the Rademacher
variables. For a family `x : ι → E` in an additive group, the Rademacher sum `∑ᵢ εᵢ xᵢ` is the
random sum whose moments control Khintchine-type inequalities; the coefficients may lie in a
noncommutative ring, such as a C⋆-algebra, so products are kept in order throughout.

## Main declarations

* `TauCeti.signAverage f`: the average `2⁻ⁿ ∑_ε f ε` of a function on the sign cube with values
  in a real vector space. It is linear, fixes constants, commutes with multiplication by a fixed
  element and with `star`, is monotone, and is bounded in norm by any bound of `f`.
* `TauCeti.rademacherSum x ε`: the Rademacher sum `∑ᵢ εᵢ • xᵢ`.
* `TauCeti.signAverage_units_smul`, `TauCeti.signAverage_units_mul_units_smul`: the first and
  second sign moments, `𝔼 εᵢ = 0` and `𝔼 εᵢ εⱼ = δᵢⱼ`.
* `TauCeti.signAverage_rademacherSum`, `TauCeti.signAverage_rademacherSum_mul_self`: a
  Rademacher sum `S` has `𝔼 S = 0` and `𝔼 S² = ∑ᵢ xᵢ²`.
* `TauCeti.signAverage_rademacherSum_mul_four`: in a possibly noncommutative, possibly
  nonunital ring, the fourth moment of a Rademacher sum expands over the three pairings of four
  indices as `𝔼 S⁴ = (∑ᵢ xᵢ²)² + ∑ᵢ xᵢ (∑ⱼ xⱼ²) xᵢ + ∑ᵢ ∑ⱼ xᵢ xⱼ xᵢ xⱼ - 2 ∑ᵢ xᵢ⁴`. For
  commuting scalars this is the classical `𝔼 S⁴ = 3 (∑ᵢ xᵢ²)² - 2 ∑ᵢ xᵢ⁴`.
* `TauCeti.sum_star_mul_le_signAverage_star_mul`, `TauCeti.sum_mul_star_le_signAverage_mul_star`:
  Bessel's inequality in a star-ordered ring. For any `Φ` on the sign cube, the coefficients
  `yₖ = 𝔼 εₖ Φ` satisfy `∑ₖ yₖ* yₖ ≤ 𝔼 Φ* Φ` and `∑ₖ yₖ yₖ* ≤ 𝔼 Φ Φ*`.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  237–323, §9 (the expansion in the proof of Lemma 9.2, and the orthogonality estimate (9.11)
  in the proof of Theorem 9.1).
-/

public section

noncomputable section

open Finset

namespace TauCeti

variable {ι E : Type*} [Fintype ι]

/-- The Rademacher sum `∑ᵢ εᵢ • xᵢ` of a finite family `x` at the sign vector `ε`. -/
def rademacherSum [AddCommGroup E] (x : ι → E) (ε : ι → ℤˣ) : E :=
  ∑ i, (ε i : ℤ) • x i

/-- Unfolding lemma for `TauCeti.rademacherSum`. -/
theorem rademacherSum_def [AddCommGroup E] (x : ι → E) (ε : ι → ℤˣ) :
    rademacherSum x ε = ∑ i, (ε i : ℤ) • x i := (rfl)

/-- The adjoint of a Rademacher sum is the Rademacher sum of the adjoints. -/
theorem star_rademacherSum [AddCommGroup E] [StarAddMonoid E] (x : ι → E) (ε : ι → ℤˣ) :
    star (rademacherSum x ε) = rademacherSum (fun i => star (x i)) ε := by
  simp only [rademacherSum_def, star_sum, star_zsmul]

/-- A Rademacher sum of self-adjoint elements is self-adjoint. -/
theorem isSelfAdjoint_rademacherSum [AddCommGroup E] [StarAddMonoid E] {x : ι → E}
    (hx : ∀ i, IsSelfAdjoint (x i)) (ε : ι → ℤˣ) : IsSelfAdjoint (rademacherSum x ε) := by
  simp only [isSelfAdjoint_iff, star_rademacherSum, fun i => (hx i).star_eq]

variable [DecidableEq ι]

/-! ### Sums of sign monomials -/

section SignSums

/-- A function on the sign cube that changes sign when the `m`-th sign is flipped sums to zero. -/
private theorem sum_eq_zero_of_flip (m : ι) {g : (ι → ℤˣ) → ℤ}
    (hg : ∀ ε, g (Pi.mulSingle m (-1) * ε) = -g ε) : ∑ ε, g ε = 0 := by
  have h := Equiv.sum_comp (Equiv.mulLeft (Pi.mulSingle m (-1) : ι → ℤˣ)) g
  simp only [Equiv.coe_mulLeft, hg, Finset.sum_neg_distrib] at h
  omega

omit [Fintype ι] in
private theorem coe_mulSingle_mul_apply_self (m : ι) (ε : ι → ℤˣ) :
    (((Pi.mulSingle m (-1) : ι → ℤˣ) * ε) m : ℤ) = -(ε m : ℤ) := by
  simp

omit [Fintype ι] in
private theorem mulSingle_mul_apply_of_ne {m k : ι} (h : k ≠ m) (ε : ι → ℤˣ) :
    ((Pi.mulSingle m (-1) : ι → ℤˣ) * ε) k = ε k := by
  simp [Pi.mulSingle_eq_of_ne h]

/-- The first sign moment: the signs `εᵢ` have mean zero. -/
theorem sum_units_apply_eq_zero (i : ι) : ∑ ε : ι → ℤˣ, (ε i : ℤ) = 0 :=
  sum_eq_zero_of_flip i fun ε => coe_mulSingle_mul_apply_self i ε

/-- The second sign moment: distinct signs are orthogonal and each sign squares to one. -/
theorem sum_units_apply_mul_units_apply (i j : ι) :
    ∑ ε : ι → ℤˣ, (ε i : ℤ) * ε j = if i = j then (Fintype.card (ι → ℤˣ) : ℤ) else 0 := by
  split_ifs with h
  · subst h
    simp [Int.units_coe_mul_self]
  · refine sum_eq_zero_of_flip i fun ε => ?_
    rw [coe_mulSingle_mul_apply_self i ε, mulSingle_mul_apply_of_ne (Ne.symm h), neg_mul]

/-- The fourth sign moment `𝔼 εᵢ εⱼ εₖ εₗ`: it is one when the indices match in pairs and zero
otherwise, written as the sum over the three pairings corrected on the diagonal. -/
private theorem sum_units_apply_mul_four (i j k l : ι) :
    ∑ ε : ι → ℤˣ, (ε i : ℤ) * ε j * ε k * ε l =
      ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) - 2 * (if i = j ∧ j = k ∧ k = l then 1 else 0)) *
        (Fintype.card (ι → ℤˣ) : ℤ) := by
  by_cases hij : i = j
  · subst hij
    have h (ε : ι → ℤˣ) : (ε i : ℤ) * ε i * ε k * ε l = ε k * ε l := by
      rw [Int.units_coe_mul_self, one_mul]
    simp only [h, sum_units_apply_mul_units_apply]
    by_cases hkl : k = l <;> by_cases hik : i = k <;> simp_all
  by_cases hik : i = k
  · subst hik
    have h (ε : ι → ℤˣ) : (ε i : ℤ) * ε j * ε i * ε l = ε j * ε l := by
      linear_combination (ε j * ε l : ℤ) * Int.units_coe_mul_self (ε i)
    simp only [h, sum_units_apply_mul_units_apply]
    by_cases hjl : j = l <;> simp_all
  by_cases hil : i = l
  · subst hil
    have h (ε : ι → ℤˣ) : (ε i : ℤ) * ε j * ε k * ε i = ε j * ε k := by
      linear_combination (ε j * ε k : ℤ) * Int.units_coe_mul_self (ε i)
    simp only [h, sum_units_apply_mul_units_apply]
    by_cases hjk : j = k <;> simp_all
  have h0 : ∑ ε : ι → ℤˣ, (ε i : ℤ) * ε j * ε k * ε l = 0 := sum_eq_zero_of_flip i fun ε => by
    rw [coe_mulSingle_mul_apply_self i ε, mulSingle_mul_apply_of_ne (Ne.symm hij),
      mulSingle_mul_apply_of_ne (Ne.symm hik), mulSingle_mul_apply_of_ne (Ne.symm hil)]
    ring
  simp [h0, hij, hik, hil]

end SignSums

/-! ### The average over the sign cube -/

section Average

variable [AddCommGroup E] [Module ℝ E]

/-- The average `2⁻ⁿ ∑_ε f ε` of a function `f` on the sign cube `ι → ℤˣ`, where `n` is the
cardinality of `ι`: the expectation of `f` under independent symmetric random signs. -/
def signAverage (f : (ι → ℤˣ) → E) : E :=
  (Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, f ε

/-- Unfolding lemma for `TauCeti.signAverage`. -/
theorem signAverage_def (f : (ι → ℤˣ) → E) :
    signAverage f = (Fintype.card (ι → ℤˣ) : ℝ)⁻¹ • ∑ ε, f ε := (rfl)

private theorem card_signCube_ne_zero : (Fintype.card (ι → ℤˣ) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

/-- Averaging a constant function returns the constant. -/
@[simp]
theorem signAverage_const (a : E) : signAverage (fun _ : ι → ℤˣ => a) = a := by
  rw [signAverage_def, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ,
    inv_smul_smul₀ card_signCube_ne_zero]

/-- The average over the sign cube is additive. -/
@[simp]
theorem signAverage_add (f g : (ι → ℤˣ) → E) :
    signAverage (fun ε => f ε + g ε) = signAverage f + signAverage g := by
  simp only [signAverage_def, Finset.sum_add_distrib, smul_add]

/-- The average over the sign cube commutes with negation. -/
@[simp]
theorem signAverage_neg (f : (ι → ℤˣ) → E) :
    signAverage (fun ε => -f ε) = -signAverage f := by
  simp only [signAverage_def, Finset.sum_neg_distrib, smul_neg]

/-- The average over the sign cube commutes with subtraction. -/
@[simp]
theorem signAverage_sub (f g : (ι → ℤˣ) → E) :
    signAverage (fun ε => f ε - g ε) = signAverage f - signAverage g := by
  simp only [signAverage_def, Finset.sum_sub_distrib, smul_sub]

/-- The average over the sign cube is homogeneous. -/
@[simp]
theorem signAverage_smul (c : ℝ) (f : (ι → ℤˣ) → E) :
    signAverage (fun ε => c • f ε) = c • signAverage f := by
  simp only [signAverage_def, ← Finset.smul_sum, smul_comm c]

/-- The average over the sign cube commutes with finite sums. -/
theorem signAverage_sum {κ : Type*} (s : Finset κ) (f : κ → (ι → ℤˣ) → E) :
    signAverage (fun ε => ∑ k ∈ s, f k ε) = ∑ k ∈ s, signAverage (f k) := by
  simp only [signAverage_def, Finset.smul_sum]
  exact Finset.sum_comm

/-- Averaging integer multiples `n ε • a` of a fixed vector, when the integers `n ε` sum to
`c` times the number of sign vectors. -/
private theorem signAverage_zsmul_const {n : (ι → ℤˣ) → ℤ} {c : ℤ}
    (hn : ∑ ε, n ε = c * Fintype.card (ι → ℤˣ)) (a : E) :
    signAverage (fun ε => n ε • a) = c • a := by
  rw [signAverage_def, ← Finset.sum_smul, hn, ← Int.cast_smul_eq_zsmul ℝ (c * _),
    ← Int.cast_smul_eq_zsmul ℝ c, smul_smul]
  congr 1
  push_cast
  rw [mul_left_comm, inv_mul_cancel₀ card_signCube_ne_zero, mul_one]

/-- The first sign moment: `𝔼 εᵢ a = 0`. -/
@[simp]
theorem signAverage_units_smul (i : ι) (a : E) :
    signAverage (fun ε : ι → ℤˣ => (ε i : ℤ) • a) = 0 := by
  rw [signAverage_zsmul_const (c := 0) (by rw [sum_units_apply_eq_zero, zero_mul]), zero_smul]

/-- The second sign moment: `𝔼 εᵢ εⱼ a = δᵢⱼ a`. -/
@[simp]
theorem signAverage_units_mul_units_smul (i j : ι) (a : E) :
    signAverage (fun ε : ι → ℤˣ => ((ε i : ℤ) * ε j) • a) = if i = j then a else 0 := by
  rw [signAverage_zsmul_const (c := if i = j then 1 else 0)
    (by rw [sum_units_apply_mul_units_apply]; split_ifs <;> simp)]
  split_ifs <;> simp

/-- The fourth sign moment, in the form used to expand fourth powers of Rademacher sums. -/
private theorem signAverage_units_mul_four_smul (i j k l : ι) (a : E) :
    signAverage (fun ε : ι → ℤˣ => ((ε i : ℤ) * ε j * ε k * ε l) • a) =
      ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) - 2 * (if i = j ∧ j = k ∧ k = l then 1 else 0) : ℤ) •
        a :=
  signAverage_zsmul_const (sum_units_apply_mul_four i j k l) a

section Ring

variable {R : Type*} [NonUnitalRing R] [Module ℝ R]

/-- Right multiplication by a fixed element commutes with the average over the sign cube. -/
theorem signAverage_mul_const [IsScalarTower ℝ R R] (f : (ι → ℤˣ) → R) (a : R) :
    signAverage (fun ε => f ε * a) = signAverage f * a := by
  simp only [signAverage_def, smul_mul_assoc, Finset.sum_mul]

/-- Left multiplication by a fixed element commutes with the average over the sign cube. -/
theorem signAverage_const_mul [SMulCommClass ℝ R R] (a : R) (f : (ι → ℤˣ) → R) :
    signAverage (fun ε => a * f ε) = a * signAverage f := by
  simp only [signAverage_def, mul_smul_comm, Finset.mul_sum]

end Ring

/-- The average over the sign cube commutes with `star`. -/
theorem star_signAverage [StarAddMonoid E] [StarModule ℝ E] (f : (ι → ℤˣ) → E) :
    star (signAverage f) = signAverage fun ε => star (f ε) := by
  simp only [signAverage_def, star_smul, star_sum, star_trivial]

/-- The average over the sign cube is monotone. -/
theorem signAverage_mono [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E]
    {f g : (ι → ℤˣ) → E} (h : ∀ ε, f ε ≤ g ε) : signAverage f ≤ signAverage g := by
  rw [signAverage_def, signAverage_def]
  exact smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun ε _ => h ε) (by positivity)

/-- The average of a nonnegative function over the sign cube is nonnegative. -/
theorem signAverage_nonneg [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono ℝ E]
    {f : (ι → ℤˣ) → E} (h : ∀ ε, 0 ≤ f ε) : 0 ≤ signAverage f := by
  simpa using signAverage_mono (f := fun _ => 0) h

end Average

/-- The norm of an average over the sign cube is at most any uniform bound of the function. -/
theorem norm_signAverage_le [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℤˣ) → E} {r : ℝ} (h : ∀ ε, ‖f ε‖ ≤ r) : ‖signAverage f‖ ≤ r := by
  have hcard : (0 : ℝ) < Fintype.card (ι → ℤˣ) := Nat.cast_pos.2 Fintype.card_pos
  rw [signAverage_def, norm_smul, norm_inv, Real.norm_natCast, inv_mul_le_iff₀ hcard]
  calc ‖∑ ε, f ε‖ ≤ ∑ ε, ‖f ε‖ := norm_sum_le _ _
    _ ≤ ∑ _ε : ι → ℤˣ, r := Finset.sum_le_sum fun ε _ => h ε
    _ = Fintype.card (ι → ℤˣ) * r := by simp

/-! ### Rademacher sums -/

section Rademacher

/-- A Rademacher sum has mean zero. -/
@[simp]
theorem signAverage_rademacherSum [AddCommGroup E] [Module ℝ E] (x : ι → E) :
    signAverage (rademacherSum x) = 0 := by
  have h : rademacherSum x = fun ε => ∑ i, (ε i : ℤ) • x i := funext (rademacherSum_def x)
  rw [h, signAverage_sum]
  simp

variable {R : Type*} [NonUnitalRing R] [Module ℝ R]

omit [DecidableEq ι] [Module ℝ R] in
/-- Rademacher sums of two families are products of signs times products of coefficients. -/
private theorem rademacherSum_mul_rademacherSum (x y : ι → R) (ε : ι → ℤˣ) :
    rademacherSum x ε * rademacherSum y ε = ∑ i, ∑ j, ((ε i : ℤ) * ε j) • (x i * y j) := by
  rw [rademacherSum_def, rademacherSum_def, Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm]

/-- The second moment of a Rademacher sum: `𝔼 (∑ᵢ εᵢ xᵢ) (∑ⱼ εⱼ yⱼ) = ∑ᵢ xᵢ yᵢ`. -/
theorem signAverage_rademacherSum_mul_rademacherSum (x y : ι → R) :
    signAverage (fun ε => rademacherSum x ε * rademacherSum y ε) = ∑ i, x i * y i := by
  simp only [rademacherSum_mul_rademacherSum, signAverage_sum,
    signAverage_units_mul_units_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The second moment of a Rademacher sum: `𝔼 S² = ∑ᵢ xᵢ²`. -/
theorem signAverage_rademacherSum_mul_self (x : ι → R) :
    signAverage (fun ε => rademacherSum x ε * rademacherSum x ε) = ∑ i, x i * x i :=
  signAverage_rademacherSum_mul_rademacherSum x x

/-- **The fourth moment of a Rademacher sum.** In a possibly noncommutative ring, averaging
`S⁴` for `S = ∑ᵢ εᵢ xᵢ` keeps the terms whose four indices match in pairs. The pairings
`(i = j, k = l)`, `(i = l, j = k)` and `(i = k, j = l)` give `(∑ᵢ xᵢ²)²`, `∑ᵢ xᵢ (∑ⱼ xⱼ²) xᵢ`
and `∑ᵢ ∑ⱼ xᵢ xⱼ xᵢ xⱼ`, and the diagonal `i = j = k = l`, counted by all three pairings, is
corrected by `- 2 ∑ᵢ xᵢ⁴`. -/
theorem signAverage_rademacherSum_mul_four (x : ι → R) :
    signAverage (fun ε => rademacherSum x ε * rademacherSum x ε * rademacherSum x ε *
        rademacherSum x ε) =
      (∑ i, x i * x i) * (∑ i, x i * x i) + ∑ i, x i * (∑ j, x j * x j) * x i +
        ∑ i, ∑ j, x i * x j * x i * x j - 2 • ∑ i, x i * x i * x i * x i := by
  -- `simp` pulls the sum of the right factor outside first, hence the order of the sums
  have hS (ε : ι → ℤˣ) : rademacherSum x ε * rademacherSum x ε * rademacherSum x ε *
      rademacherSum x ε =
        ∑ l, ∑ k, ∑ j, ∑ i, ((ε i : ℤ) * ε j * ε k * ε l) • (x i * x j * x k * x l) := by
    simp only [rademacherSum_def, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm (f := fun i j => x i * x j * x i * x j)]
  -- average each monomial with the fourth sign moment, then collapse the pairings
  simp only [hS, signAverage_sum, signAverage_units_mul_four_smul]
  simp only [sub_smul, add_smul, mul_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ite_and, ite_smul, one_smul, zero_smul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul,
    Finset.mul_sum, two_smul, mul_assoc]
  abel

end Rademacher

/-! ### Bessel's inequality for the sign functions

In a star-ordered ring, the sign functions `ε ↦ εₖ` are orthonormal for the pairing
`(Φ, Ψ) ↦ 𝔼 Φ* Ψ`, which gives Bessel's inequality for the coefficients `𝔼 εₖ Φ`. -/

section Bessel

variable {R : Type*} [NonUnitalRing R] [StarRing R] [Module ℝ R] [StarModule ℝ R]
  [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]

omit [SMulCommClass ℝ R R] in
/-- Averaging `star (Φ ε) * ∑ₖ εₖ yₖ` against the signs recovers the coefficients of `Φ`. -/
private theorem signAverage_star_mul_rademacherSum (Φ : (ι → ℤˣ) → R) :
    signAverage (fun ε => star (Φ ε) * rademacherSum
        (fun k => signAverage fun ε => (ε k : ℤ) • Φ ε) ε) =
      ∑ k, star (signAverage fun ε => (ε k : ℤ) • Φ ε) *
        signAverage fun ε => (ε k : ℤ) • Φ ε := by
  simp only [rademacherSum_def, Finset.mul_sum, mul_smul_comm, ← smul_mul_assoc,
    signAverage_sum, signAverage_mul_const, star_signAverage, star_zsmul]

variable [PartialOrder R] [StarOrderedRing R]

/-- **Bessel's inequality for the sign functions.** For `Φ : (ι → ℤˣ) → R`, the coefficients
`yₖ = 𝔼 εₖ Φ` satisfy `∑ₖ yₖ* yₖ ≤ 𝔼 Φ* Φ`. -/
theorem sum_star_mul_le_signAverage_star_mul (Φ : (ι → ℤˣ) → R) :
    ∑ k, star (signAverage fun ε => (ε k : ℤ) • Φ ε) * signAverage (fun ε => (ε k : ℤ) • Φ ε) ≤
      signAverage fun ε => star (Φ ε) * Φ ε := by
  set y : ι → R := fun k => signAverage fun ε => (ε k : ℤ) • Φ ε
  -- the remainder `Φ - ∑ₖ εₖ yₖ` has `𝔼 (Φ - ∑ₖ εₖ yₖ)* (Φ - ∑ₖ εₖ yₖ) = 𝔼 Φ* Φ - ∑ₖ yₖ* yₖ`
  have h₁ : signAverage (fun ε => star (Φ ε) * rademacherSum y ε) = ∑ k, star (y k) * y k :=
    signAverage_star_mul_rademacherSum Φ
  have h₂ : signAverage (fun ε => star (rademacherSum y ε) * Φ ε) = ∑ k, star (y k) * y k := by
    have := congrArg star h₁
    simpa only [star_signAverage, star_mul, star_star, star_sum] using this
  have h₃ : signAverage (fun ε => star (rademacherSum y ε) * rademacherSum y ε) =
      ∑ k, star (y k) * y k := by
    simpa only [star_rademacherSum] using
      signAverage_rademacherSum_mul_rademacherSum (fun k => star (y k)) y
  have h₀ : 0 ≤ signAverage fun ε => star (Φ ε - rademacherSum y ε) * (Φ ε - rademacherSum y ε) :=
    signAverage_nonneg fun ε => star_mul_self_nonneg _
  have hexp (ε : ι → ℤˣ) : star (Φ ε - rademacherSum y ε) * (Φ ε - rademacherSum y ε) =
      star (Φ ε) * Φ ε - star (Φ ε) * rademacherSum y ε - star (rademacherSum y ε) * Φ ε +
        star (rademacherSum y ε) * rademacherSum y ε := by
    simp only [star_sub, sub_mul, mul_sub]
    abel
  simp only [hexp, signAverage_add, signAverage_sub, h₁, h₂, h₃] at h₀
  rw [← sub_nonneg]
  convert h₀ using 1
  abel

/-- **Bessel's inequality for the sign functions, row form.** For `Φ : (ι → ℤˣ) → R`, the
coefficients `yₖ = 𝔼 εₖ Φ` satisfy `∑ₖ yₖ yₖ* ≤ 𝔼 Φ Φ*`. -/
theorem sum_mul_star_le_signAverage_mul_star (Φ : (ι → ℤˣ) → R) :
    ∑ k, signAverage (fun ε => (ε k : ℤ) • Φ ε) * star (signAverage fun ε => (ε k : ℤ) • Φ ε) ≤
      signAverage fun ε => Φ ε * star (Φ ε) := by
  simpa only [star_signAverage, star_zsmul, star_star] using
    sum_star_mul_le_signAverage_star_mul fun ε => star (Φ ε)

end Bessel

end TauCeti
