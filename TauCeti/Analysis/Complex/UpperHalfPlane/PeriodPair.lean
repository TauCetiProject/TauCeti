/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# The period lattice of a point of the upper half-plane

A point `z` of the upper half-plane determines the period pair `(z, 1)`
(`UpperHalfPlane.periodPair`), whose lattice is `ℤ z + ℤ`. This file records the Weierstrass
function `℘(x; ℤ z + ℤ)` of Mathlib's `PeriodPair.weierstrassP` in the coordinates of modular
forms:

* as a series over integer pairs `y`,
  `℘(x; ℤ z + ℤ) = ∑_y ((x - (y₀ z + y₁))⁻² - (y₀ z + y₁)⁻²)`;
* under `γ ∈ SL(2, ℤ)` the lattice of `γ z` is `(c z + d)⁻¹ (ℤ z + ℤ)`, so
  `℘(x / (c z + d); ℤ γz + ℤ) = (c z + d)² ℘(x; ℤ z + ℤ)`;
* summing first along the rows `y₀ = m`,
  `℘(x; ℤ z + ℤ) = ∑_m (P(x - m z) - P(m z))` with `P(w) = ∑_n (w + n)⁻²`, and `P(w)` decays like
  `e^(-2π Im w)` as `Im w → ∞` (`UpperHalfPlane.norm_tsum_one_div_add_sq_le`).

These are the inputs that make the values of `℘` at the `N`-division points of `ℤ z + ℤ` weight-two
modular forms of level `Γ(N)`.

## Main definitions

* `UpperHalfPlane.periodPair`: the period pair `(z, 1)`.

## Main results

* `UpperHalfPlane.hasSum_weierstrassP_periodPair`: the series over integer pairs.
* `UpperHalfPlane.intCast_mul_smul_add_intCast`: the lattice points of `γ z` in terms of those
  of `z`.
* `UpperHalfPlane.weierstrassP_periodPair_smul`: the modular transformation law.
* `UpperHalfPlane.hasSum_weierstrassP_periodPair_rows`: the sum along rows.
* `UpperHalfPlane.norm_tsum_one_div_add_sq_le`: the exponential decay of the rows.
-/

public section

noncomputable section

open Complex PeriodPair Matrix
open scoped MatrixGroups Real

namespace UpperHalfPlane

/-- The period pair `(z, 1)` of a point `z` of the upper half-plane; its lattice is `ℤ z + ℤ`. -/
def periodPair (z : ℍ) : PeriodPair where
  ω₁ := z
  ω₂ := 1
  indep := by
    refine LinearIndependent.pair_iff.mpr fun s t h ↦ ?_
    have hs : s = 0 := by
      have him := congrArg Complex.im h
      simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, mul_one, Complex.zero_im] at him
      exact (mul_eq_zero.mp him).resolve_right z.im_pos.ne'
    subst hs
    simpa using h

@[simp]
lemma periodPair_ω₁ (z : ℍ) : z.periodPair.ω₁ = z := (rfl)

@[simp]
lemma periodPair_ω₂ (z : ℍ) : z.periodPair.ω₂ = 1 := (rfl)

/-- The points `m z + n` with `m n : ℤ` lie in the lattice of `z.periodPair`. -/
lemma intCast_mul_add_intCast_mem_lattice_periodPair (z : ℍ) (m n : ℤ) :
    (m : ℂ) * z + n ∈ z.periodPair.lattice :=
  mem_lattice.mpr ⟨m, n, by simp⟩

/-- The integer pairs parametrize the lattice of `z.periodPair` by `y ↦ y₀ z + y₁`. -/
private def latticeEquiv (z : ℍ) : (Fin 2 → ℤ) ≃ z.periodPair.lattice :=
  (finTwoArrowEquiv ℤ).trans z.periodPair.latticeEquivProd.symm.toEquiv

private lemma coe_latticeEquiv (z : ℍ) (y : Fin 2 → ℤ) :
    (latticeEquiv z y : ℂ) = y 0 * z + y 1 := by
  simp [latticeEquiv, latticeEquiv_symm_apply]

/-- **The Weierstrass function of `ℤ z + ℤ` as a series over integer pairs**:
`℘(x; ℤ z + ℤ) = ∑_y ((x - (y₀ z + y₁))⁻² - (y₀ z + y₁)⁻²)`, the series converging absolutely. -/
theorem hasSum_weierstrassP_periodPair (z : ℍ) (x : ℂ) :
    HasSum (fun y : Fin 2 → ℤ ↦ 1 / (x - (y 0 * z + y 1)) ^ 2 - 1 / ((y 0 : ℂ) * z + y 1) ^ 2)
      (℘[z.periodPair] x) := by
  have h := z.periodPair.hasSum_weierstrassP x
  rw [← (latticeEquiv z).hasSum_iff] at h
  simpa only [Function.comp_def, coe_latticeEquiv] using h

/-- In the coordinates of `γ z`, the lattice point `y₀ γz + y₁` is `(y γ)₀ z + (y γ)₁` divided by
`c z + d`. -/
lemma intCast_mul_smul_add_intCast (γ : SL(2, ℤ)) (z : ℍ) (y : Fin 2 → ℤ) :
    (y 0 : ℂ) * ↑(γ • z) + y 1 =
      (((y ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 : ℂ) * z +
        (y ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) 1) / denom γ z := by
  have hD := denom_ne_zero γ z
  rw [ModularGroup.denom_apply] at hD ⊢
  rw [coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq, eq_intCast, Complex.ofReal_intCast]
  rw [eq_div_iff hD, add_mul, mul_assoc, div_mul_cancel₀ _ hD]
  simp only [vecMul, dotProduct, Fin.sum_univ_two, Int.cast_add, Int.cast_mul]
  ring

/-- **The modular transformation of `℘`.** For `γ ∈ SL(2, ℤ)` the lattice of `γ z` is
`(c z + d)⁻¹ (ℤ z + ℤ)`, so `℘(x / (c z + d); ℤ γz + ℤ) = (c z + d)² ℘(x; ℤ z + ℤ)`. -/
theorem weierstrassP_periodPair_smul (γ : SL(2, ℤ)) (z : ℍ) (x : ℂ) :
    ℘[(γ • z).periodPair] (x / denom γ z) = denom γ z ^ 2 * ℘[z.periodPair] x := by
  have hD := denom_ne_zero γ z
  -- reindex the integer pairs by `y ↦ y γ`
  let e : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
    Matrix.toLinearEquivRight'OfInv
      (M := ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      (M' := (γ : Matrix (Fin 2) (Fin 2) ℤ))
      (by simp [Matrix.adjugate_mul]) (by simp [Matrix.mul_adjugate])
  have h := (hasSum_weierstrassP_periodPair z x).mul_left (denom γ z ^ 2)
  rw [← e.toEquiv.hasSum_iff] at h
  refine (hasSum_weierstrassP_periodPair (γ • z) (x / denom γ z)).unique (h.congr_fun fun y ↦ ?_)
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, e,
    Matrix.toLinearEquivRight'OfInv_apply, Matrix.toLinearMapRight'_apply,
    intCast_mul_smul_add_intCast γ z y]
  rw [← sub_div, div_pow, div_pow, one_div_div, one_div_div]
  ring

/-- The rows `∑_n (w + n)⁻²` of the lattice series are absolutely convergent. -/
private lemma summable_one_div_add_intCast_sq (w : ℂ) :
    Summable fun n : ℤ ↦ 1 / (w + n) ^ 2 := by
  simpa [one_div] using EisensteinSeries.linear_right_summable w 1 (k := 2) le_rfl

/-- **The Weierstrass function of `ℤ z + ℤ` summed along rows**:
`℘(x; ℤ z + ℤ) = ∑_m (∑_n (x - m z + n)⁻² - ∑_n (m z + n)⁻²)`. -/
theorem hasSum_weierstrassP_periodPair_rows (z : ℍ) (x : ℂ) :
    HasSum (fun m : ℤ ↦ ∑' n : ℤ, 1 / (x - m * z + n) ^ 2 - ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2)
      (℘[z.periodPair] x) := by
  have h := hasSum_weierstrassP_periodPair z x
  rw [← (finTwoArrowEquiv ℤ).symm.hasSum_iff] at h
  refine h.prod_fiberwise fun m ↦ ?_
  have hrow : ∑' n : ℤ, 1 / (x - m * z + n) ^ 2 = ∑' n : ℤ, 1 / (x - (m * z + n)) ^ 2 := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n ↦ ?_
    simp only [Equiv.neg_apply, Int.cast_neg]
    ring_nf
  rw [hrow]
  have h₁ : Summable fun n : ℤ ↦ 1 / (x - (m * z + n)) ^ 2 := by
    have := (summable_one_div_add_intCast_sq (x - m * z)).comp_injective neg_injective
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply, Int.cast_neg]
    ring_nf
  simpa [Function.comp_def] using
    h₁.hasSum.sub (summable_one_div_add_intCast_sq ((m : ℂ) * z)).hasSum

/-- **The rows decay exponentially**: for `w` in the upper half-plane and `q = e^(2π i w)`,
`‖∑_n (w + n)⁻²‖ ≤ 4 π² ‖q‖ / (1 - ‖q‖)²`. -/
theorem norm_tsum_one_div_add_sq_le (w : ℍ) :
    ‖∑' n : ℤ, 1 / ((w : ℂ) + n) ^ 2‖ ≤
      4 * π ^ 2 * ‖cexp (2 * π * Complex.I * w)‖ /
        (1 - ‖cexp (2 * π * Complex.I * w)‖) ^ 2 := by
  have H := EisensteinSeries.qExpansion_identity (k := 1) le_rfl w
  simp only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at H
  set q := cexp (2 * π * Complex.I * w)
  have hq : ‖q‖ < 1 := norm_exp_two_pi_I_lt_one w
  have hq' : 0 < 1 - ‖q‖ := by linarith
  have h1 : 1 - ‖q‖ ≤ ‖1 - q‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) q
  have h2 : ‖(-2 * π * Complex.I : ℂ)‖ ^ 2 = 4 * π ^ 2 := by
    simp [abs_of_pos Real.pi_pos]
    ring
  rw [H, tsum_coe_mul_geometric_of_norm_lt_one hq, norm_mul, norm_div, norm_pow, norm_pow, h2,
    mul_div_assoc]
  gcongr

end UpperHalfPlane
