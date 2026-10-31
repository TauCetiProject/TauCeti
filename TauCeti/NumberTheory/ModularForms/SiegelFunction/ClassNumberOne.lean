/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import TauCeti.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Bounds

/-!
# Siegel function estimates for the class number one problem

At a CM point `τ`, suitable twelfth powers of Siegel function values are algebraic integers, and
their norms are rational integers equal to products of twelfth powers of Siegel function values at
`τ`. A nonzero integer has absolute value at least one, so such a product cannot be small. This
file applies the product bounds of `TauCeti.NumberTheory.ModularForms.SiegelFunction.Bounds` to
certify the two numerical inequalities used there, with rational bounds on `π`, square roots and
the exponential. Write `A = |q| = e^{-2π Im τ}`.

* For `Im τ ≥ √31 / 2`, that is `A ≤ e^{-π √31}`, both `|g_{(0, 1/2)}(τ)|` and
  `|g_{(0, 1/2)}(τ) g_{(1/2, b)}(τ)|` are less than one, through the bound
  `2 A^{1/24} exp ((2A + 2A^{1/2}) / (1 - A)) < 1`.
* For `Im τ ≥ √51 / 2`, that is `A ≤ e^{-π √51}`, the product
  `|g_{(0, 1/3)}(τ) g_{(a, b)}(τ) g_{(a', b')}(τ)|` with `a, a' ∈ {1/3, 2/3}` is less than one,
  through the bound `√3 A^{1/36} exp ((2A + 4A^{1/3}) / (1 - A)) < 1`.

## Main results

* `TauCeti.ModularForm.level_two_bound_lt_one`,
  `TauCeti.ModularForm.level_three_bound_lt_one`: the two numerical inequalities.
* `TauCeti.ModularForm.norm_siegelFunction_zero_half_lt_one`,
  `TauCeti.ModularForm.norm_siegelFunction_zero_half_mul_lt_one`: the level-two estimates for
  `Im τ ≥ √31 / 2`.
* `TauCeti.ModularForm.norm_siegelFunction_zero_third_mul_mul_lt_one`: the level-three estimate
  for `Im τ ≥ √51 / 2`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5 (the use of the
  product estimates in the class number one problem).
* H. M. Stark, *A complete determination of the complex quadratic fields of class number one*,
  Michigan Math. J. 14 (1967), 1–27.
-/

public section

open Complex
open scoped Real

namespace TauCeti.ModularForm

/-! ### Certified numerical inequalities -/

/-- **The level-two numerical inequality.** The bound
`2 A^{1/24} exp ((2A + 2A^{1/2}) / (1 - A)) < 1` for `0 < A ≤ e^{-π √31}`. -/
theorem level_two_bound_lt_one {A : ℝ} (hA : 0 < A) (hAt : A ≤ Real.exp (-(π * √31))) :
    2 * A ^ (1 / 24 : ℝ) * Real.exp ((2 * A + 2 * A ^ (1 / 2 : ℝ)) / (1 - A)) < 1 := by
  have hpi := Real.pi_gt_d4
  have h31 : (5.5677 : ℝ) < √31 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  have ht : (17.49 : ℝ) ≤ π * √31 := by nlinarith
  -- The small terms: `A ≤ A^{1/2} ≤ e^{-7} ≤ 1/150`.
  have hsqrt : A ^ (1 / 2 : ℝ) ≤ 1 / 150 := by
    have h : (150 : ℝ) ≤ Real.exp 7 :=
      le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (x := 7) (by norm_num) 5)
    refine (Real.rpow_le_exp_neg_mul hA.le hAt (by norm_num)).trans ?_
    refine (Real.exp_le_exp.2 (by linarith : -(1 / 2 * (π * √31)) ≤ -7)).trans ?_
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h
  have hA1 : A ≤ 1 := hAt.trans (Real.exp_le_one_iff.2 (by linarith))
  have hAsqrt : A ≤ A ^ (1 / 2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hA hA1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  -- The exponential factor is at most `1 / (1 - 4/149) = 149/145`.
  have hc : (2 * A + 2 * A ^ (1 / 2 : ℝ)) / (1 - A) ≤ 4 / 149 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hexp : Real.exp ((2 * A + 2 * A ^ (1 / 2 : ℝ)) / (1 - A)) ≤ 149 / 145 := by
    refine (Real.exp_le_exp.2 hc).trans ((Real.exp_bound_div_one_sub_of_interval
      (by norm_num) (by norm_num)).trans_eq (by norm_num))
  -- The main factor: `A^{1/24} ≤ e^{-0.728} ≤ 1 / 2.07`.
  have hmain : A ^ (1 / 24 : ℝ) ≤ 1 / 2.07 := by
    have h : (2.07 : ℝ) ≤ Real.exp 0.728 :=
      le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (x := 0.728) (by norm_num) 8)
    refine (Real.rpow_le_exp_neg_mul hA.le hAt (by norm_num)).trans ?_
    refine (Real.exp_le_exp.2 (by linarith : -(1 / 24 * (π * √31)) ≤ -0.728)).trans ?_
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h
  calc 2 * A ^ (1 / 24 : ℝ) * Real.exp ((2 * A + 2 * A ^ (1 / 2 : ℝ)) / (1 - A))
      ≤ 2 * (1 / 2.07) * (149 / 145) := by gcongr
    _ < 1 := by norm_num

/-- **The level-three numerical inequality.** The bound
`√3 A^{1/36} exp ((2A + 4A^{1/3}) / (1 - A)) < 1` for `0 < A ≤ e^{-π √51}`. -/
theorem level_three_bound_lt_one {A : ℝ} (hA : 0 < A) (hAt : A ≤ Real.exp (-(π * √51))) :
    √3 * A ^ (1 / 36 : ℝ) * Real.exp ((2 * A + 4 * A ^ (1 / 3 : ℝ)) / (1 - A)) < 1 := by
  have hpi := Real.pi_gt_d4
  have h51 : (7.1414 : ℝ) < √51 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  have h3 : √3 < 1.7321 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have ht : (22.43 : ℝ) ≤ π * √51 := by nlinarith
  -- The small terms: `A ≤ A^{1/3} ≤ e^{-7} ≤ 1/150`.
  have hcbrt : A ^ (1 / 3 : ℝ) ≤ 1 / 150 := by
    have h : (150 : ℝ) ≤ Real.exp 7 :=
      le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (x := 7) (by norm_num) 5)
    refine (Real.rpow_le_exp_neg_mul hA.le hAt (by norm_num)).trans ?_
    refine (Real.exp_le_exp.2 (by linarith : -(1 / 3 * (π * √51)) ≤ -7)).trans ?_
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h
  have hA1 : A ≤ 1 := hAt.trans (Real.exp_le_one_iff.2 (by linarith))
  have hAcbrt : A ≤ A ^ (1 / 3 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hA hA1 (by norm_num : (1 / 3 : ℝ) ≤ 1)
  -- The exponential factor is at most `1 / (1 - 6/149) = 149/143`.
  have hc : (2 * A + 4 * A ^ (1 / 3 : ℝ)) / (1 - A) ≤ 6 / 149 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hexp : Real.exp ((2 * A + 4 * A ^ (1 / 3 : ℝ)) / (1 - A)) ≤ 149 / 143 := by
    refine (Real.exp_le_exp.2 hc).trans ((Real.exp_bound_div_one_sub_of_interval
      (by norm_num) (by norm_num)).trans_eq (by norm_num))
  -- The main factor: `A^{1/36} ≤ e^{-0.623} ≤ 1 / 1.864`.
  have hmain : A ^ (1 / 36 : ℝ) ≤ 1 / 1.864 := by
    have h : (1.864 : ℝ) ≤ Real.exp 0.623 :=
      le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
        (Real.sum_le_exp_of_nonneg (x := 0.623) (by norm_num) 8)
    refine (Real.rpow_le_exp_neg_mul hA.le hAt (by norm_num)).trans ?_
    refine (Real.exp_le_exp.2 (by linarith : -(1 / 36 * (π * √51)) ≤ -0.623)).trans ?_
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h
  calc √3 * A ^ (1 / 36 : ℝ) * Real.exp ((2 * A + 4 * A ^ (1 / 3 : ℝ)) / (1 - A))
      ≤ 1.7321 * (1 / 1.864) * (149 / 143) := by gcongr
    _ < 1 := by norm_num

/-! ### The level-two and level-three estimates -/

/-- The bound `|g_{(0, 1/2)}(τ)| ≤ 2 A^{1/12} exp (2A / (1 - A))`. -/
private theorem norm_siegelFunction_zero_half_le {τ : ℂ} (hτ : 0 < τ.im) :
    ‖siegelFunction ![0, 1 / 2] τ‖ ≤ 2 * ‖cexp (2 * π * I * τ)‖ ^ (1 / 12 : ℝ) *
      Real.exp (2 * ‖cexp (2 * π * I * τ)‖ / (1 - ‖cexp (2 * π * I * τ)‖)) := by
  refine (norm_siegelFunction_le_of_apply_zero_eq_zero (by simp) hτ).trans_eq ?_
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one,
    UpperHalfPlane.norm_one_sub_exp_two_pi_I_mul]
  rw [show π * (1 / 2 : ℝ) = π / 2 by ring, Real.sin_pi_div_two, mul_one, abs_two]
  ring

/-- **The level-two estimate for one Siegel function.** If `Im τ ≥ √31 / 2`, then
`|g_{(0, 1/2)}(τ)| < 1`. -/
theorem norm_siegelFunction_zero_half_lt_one {τ : ℂ} (hτ : √31 / 2 ≤ τ.im) :
    ‖siegelFunction ![0, 1 / 2] τ‖ < 1 := by
  have hτ₀ : 0 < τ.im := lt_of_lt_of_le (by positivity) hτ
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ₀⟩
  have hA : 0 < ‖cexp (2 * π * I * τ)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have h₀ := norm_siegelFunction_zero_half_le hτ₀
  have hAt : ‖cexp (2 * π * I * τ)‖ ≤ Real.exp (-(π * √31)) :=
    (UpperHalfPlane.norm_exp_two_pi_I_mul_le hτ).trans_eq (by ring_nf)
  generalize ‖cexp (2 * π * I * τ)‖ = A at hq hA h₀ hAt
  refine h₀.trans_lt (lt_of_le_of_lt ?_ (level_two_bound_lt_one hA hAt))
  have h₁ : A ^ (1 / 12 : ℝ) ≤ A ^ (1 / 24 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hA hq.le (by norm_num)
  have h₂ : 0 ≤ A ^ (1 / 2 : ℝ) := by positivity
  gcongr
  linarith

/-- **The level-two estimate for a product of two Siegel functions.** If `Im τ ≥ √31 / 2` and
`a = 1/2`, then `|g_{(0, 1/2)}(τ) g_{(a, b)}(τ)| < 1`. -/
theorem norm_siegelFunction_zero_half_mul_lt_one {τ : ℂ} (hτ : √31 / 2 ≤ τ.im)
    {r : Fin 2 → ℝ} (hr : r 0 = 1 / 2) :
    ‖siegelFunction ![0, 1 / 2] τ * siegelFunction r τ‖ < 1 := by
  have hτ₀ : 0 < τ.im := lt_of_lt_of_le (by positivity) hτ
  have hA : 0 < ‖cexp (2 * π * I * τ)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have h₀ := norm_siegelFunction_zero_half_le hτ₀
  have h₁ : ‖siegelFunction r τ‖ ≤ ‖cexp (2 * π * I * τ)‖ ^ (-(1 / 24) : ℝ) *
      Real.exp (2 * ‖cexp (2 * π * I * τ)‖ ^ (1 / 2 : ℝ) / (1 - ‖cexp (2 * π * I * τ)‖)) := by
    refine (norm_siegelFunction_le_of_le_half hr.le hτ₀).trans_eq ?_
    rw [hr, bernoulliFun_two]
    norm_num
  have hAt : ‖cexp (2 * π * I * τ)‖ ≤ Real.exp (-(π * √31)) :=
    (UpperHalfPlane.norm_exp_two_pi_I_mul_le hτ).trans_eq (by ring_nf)
  generalize ‖cexp (2 * π * I * τ)‖ = A at hA h₀ h₁ hAt
  refine lt_of_le_of_lt ?_ (level_two_bound_lt_one hA hAt)
  have hpow : A ^ (1 / 12 : ℝ) * A ^ (-(1 / 24) : ℝ) = A ^ (1 / 24 : ℝ) := by
    rw [← Real.rpow_add hA]
    norm_num
  rw [norm_mul, add_div, Real.exp_add, ← hpow]
  refine (mul_le_mul h₀ h₁ (norm_nonneg _) (by positivity)).trans_eq ?_
  ring

/-- `|g_{(a, b)}(τ)| ≤ A^{-1/36} exp (2 A^{1/3} / (1 - A))` for `a ∈ {1/3, 2/3}`. -/
private theorem norm_siegelFunction_le_of_third {r : Fin 2 → ℝ} (hr : r 0 = 1 / 3 ∨ r 0 = 2 / 3)
    {τ : ℂ} (hτ : 0 < τ.im) :
    ‖siegelFunction r τ‖ ≤ ‖cexp (2 * π * I * τ)‖ ^ (-(1 / 36) : ℝ) *
      Real.exp (2 * ‖cexp (2 * π * I * τ)‖ ^ (1 / 3 : ℝ) / (1 - ‖cexp (2 * π * I * τ)‖)) := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have hA : 0 < ‖cexp (2 * π * I * τ)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have h : ‖cexp (2 * π * I * τ)‖ ^ (2 / 3 : ℝ) ≤ ‖cexp (2 * π * I * τ)‖ ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hA hq.le (by norm_num)
  refine (norm_siegelFunction_le_exp r hτ).trans ?_
  rcases hr with hr | hr <;>
  · rw [hr, bernoulliFun_two]
    norm_num
    gcongr
    linarith

/-- **The level-three estimate.** If `Im τ ≥ √51 / 2` and `a, a' ∈ {1/3, 2/3}`, then
`|g_{(0, 1/3)}(τ) g_{(a, b)}(τ) g_{(a', b')}(τ)| < 1`. -/
theorem norm_siegelFunction_zero_third_mul_mul_lt_one {τ : ℂ} (hτ : √51 / 2 ≤ τ.im)
    {r r' : Fin 2 → ℝ} (hr : r 0 = 1 / 3 ∨ r 0 = 2 / 3) (hr' : r' 0 = 1 / 3 ∨ r' 0 = 2 / 3) :
    ‖siegelFunction ![0, 1 / 3] τ * siegelFunction r τ * siegelFunction r' τ‖ < 1 := by
  have hτ₀ : 0 < τ.im := lt_of_lt_of_le (by positivity) hτ
  have hA : 0 < ‖cexp (2 * π * I * τ)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have h₀ : ‖siegelFunction ![0, 1 / 3] τ‖ ≤ √3 * ‖cexp (2 * π * I * τ)‖ ^ (1 / 12 : ℝ) *
      Real.exp (2 * ‖cexp (2 * π * I * τ)‖ / (1 - ‖cexp (2 * π * I * τ)‖)) := by
    refine (norm_siegelFunction_le_of_apply_zero_eq_zero (by simp) hτ₀).trans_eq ?_
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one,
    UpperHalfPlane.norm_one_sub_exp_two_pi_I_mul]
    rw [show π * (1 / 3 : ℝ) = π / 3 by ring, Real.sin_pi_div_three,
      show 2 * (√3 / 2) = √3 by ring, abs_of_nonneg (Real.sqrt_nonneg 3)]
    ring
  have h₁ := norm_siegelFunction_le_of_third hr hτ₀
  have h₂ := norm_siegelFunction_le_of_third hr' hτ₀
  have hAt : ‖cexp (2 * π * I * τ)‖ ≤ Real.exp (-(π * √51)) :=
    (UpperHalfPlane.norm_exp_two_pi_I_mul_le hτ).trans_eq (by ring_nf)
  generalize ‖cexp (2 * π * I * τ)‖ = A at hA h₀ h₁ h₂ hAt
  refine lt_of_le_of_lt ?_ (level_three_bound_lt_one hA hAt)
  have hpow : A ^ (1 / 12 : ℝ) * A ^ (-(1 / 36) : ℝ) * A ^ (-(1 / 36) : ℝ) =
      A ^ (1 / 36 : ℝ) := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA]
    norm_num
  rw [norm_mul, norm_mul, ← hpow, show (2 * A + 4 * A ^ (1 / 3 : ℝ)) / (1 - A) =
      2 * A / (1 - A) + 2 * A ^ (1 / 3 : ℝ) / (1 - A) + 2 * A ^ (1 / 3 : ℝ) / (1 - A) by ring,
    Real.exp_add, Real.exp_add]
  refine (mul_le_mul (mul_le_mul h₀ h₁ (norm_nonneg _) (by positivity)) h₂ (norm_nonneg _)
    (by positivity)).trans_eq ?_
  ring

end TauCeti.ModularForm
