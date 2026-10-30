/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import TauCeti.NumberTheory.ModularForms.SiegelFunction

/-!
# Effective bounds for Siegel functions

Write `A = |q| = e^{-2π Im τ}` for `τ` in the upper half-plane. Bounding each factor of the
product defining the Siegel function `g_r(τ)` by `|1 - x| ≤ 1 + |x| ≤ e^{|x|}` gives
`|g_{(a, b)}(τ)| ≤ A^{B₂(a)/2} |1 - w| exp ((A^{1+a} + A^{1-a}) / (1 - A))` for every real
`r = (a, b)`, where `w = e^{2π i (a τ + b)}` has `|w| = A^a` and `B₂(x) = x² - x + 1/6`. Two
consequences are
`|g_{(a, b)}(τ)| ≤ A^{B₂(a)/2} exp (2 A^a / (1 - A))` for `a ≤ 1/2` and
`|g_{(0, b)}(τ)| ≤ A^{1/12} |1 - e^{2π i b}| exp (2A / (1 - A))`.

These are the analytic estimates of the class number one problem. At a CM point `τ`, suitable
twelfth powers of Siegel function values are algebraic integers, and their norms are rational
integers equal to products of twelfth powers of Siegel function values at `τ`. A nonzero integer
has absolute value at least one, so such a product cannot be small. This file certifies the two
numerical inequalities used there, with rational bounds on `π`, square roots and the exponential:

* for `Im τ ≥ √31 / 2`, that is `A ≤ e^{-π √31}`, both `|g_{(0, 1/2)}(τ)|` and
  `|g_{(0, 1/2)}(τ) g_{(1/2, b)}(τ)|` are less than one, through the bound
  `2 A^{1/24} exp ((2A + 2A^{1/2}) / (1 - A)) < 1`;
* for `Im τ ≥ √51 / 2`, that is `A ≤ e^{-π √51}`, the product
  `|g_{(0, 1/3)}(τ) g_{(a, b)}(τ) g_{(a', b')}(τ)|` with `a, a' ∈ {1/3, 2/3}` is less than one,
  through the bound `√3 A^{1/36} exp ((2A + 4A^{1/3}) / (1 - A)) < 1`.

## Main results

* `TauCeti.ModularForm.norm_siegelFunction_le`: the bound with the exact factor `|1 - w|`.
* `TauCeti.ModularForm.norm_siegelFunction_le_exp`: `|g_{(a, b)}(τ)|` is at most
  `A^{B₂(a)/2} exp ((A^a + A^{1-a}) / (1 - A))`.
* `TauCeti.ModularForm.norm_siegelFunction_le_of_le_half`: for `a ≤ 1/2`, the bound
  `A^{B₂(a)/2} exp (2 A^a / (1 - A))`.
* `TauCeti.ModularForm.norm_siegelFunction_le_of_apply_zero_eq_zero`: for `a = 0`, the bound
  `A^{1/12} |1 - e^{2π i b}| exp (2A / (1 - A))`.
* `TauCeti.ModularForm.norm_siegelFunction_zero_half_lt_one`,
  `TauCeti.ModularForm.norm_siegelFunction_zero_half_mul_lt_one`: the level-two estimates for
  `Im τ ≥ √31 / 2`.
* `TauCeti.ModularForm.norm_siegelFunction_zero_third_mul_mul_lt_one`: the level-three estimate
  for `Im τ ≥ √51 / 2`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5 (the product
  estimates for Siegel functions and their use in the class number one problem).
* H. M. Stark, *A complete determination of the complex quadratic fields of class number one*,
  Michigan Math. J. 14 (1967), 1–27.
-/

public section

open Complex
open scoped Real

namespace TauCeti.ModularForm

/-- `|q| = e^{-2π Im τ}` for `q = e^{2π i τ}`. -/
private theorem norm_exp_two_pi_I_mul (τ : ℂ) :
    ‖cexp (2 * π * I * τ)‖ = Real.exp (-(2 * π * τ.im)) := by
  simp [Complex.norm_exp]

/-- `‖e^{2π i (a τ + b)}‖ = |q|^a` for `q = e^{2π i τ}`. -/
private theorem norm_exp_two_pi_I_mul_add (a b : ℝ) (τ : ℂ) :
    ‖cexp (2 * π * I * (a * τ + b))‖ = ‖cexp (2 * π * I * τ)‖ ^ a := by
  rw [Complex.norm_exp, norm_exp_two_pi_I_mul, ← Real.exp_mul]
  congr 1
  simp
  ring

/-- **The product bound for Siegel functions.** With `A = |q| = e^{-2π Im τ}` and
`w = e^{2π i (a τ + b)}`, every Siegel function satisfies
`|g_{(a, b)}(τ)| ≤ A^{B₂(a)/2} |1 - w| exp ((A^{1+a} + A^{1-a}) / (1 - A))` on the upper
half-plane, where `B₂(x) = x² - x + 1/6`. -/
theorem norm_siegelFunction_le (r : Fin 2 → ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖siegelFunction r τ‖ ≤ ‖cexp (2 * π * I * τ)‖ ^ (bernoulliFun 2 (r 0) / 2) *
      ‖1 - cexp (2 * π * I * (r 0 * τ + r 1))‖ *
      Real.exp ((‖cexp (2 * π * I * τ)‖ ^ (1 + r 0) + ‖cexp (2 * π * I * τ)‖ ^ (1 - r 0)) /
        (1 - ‖cexp (2 * π * I * τ)‖)) := by
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have hA : 0 < ‖cexp (2 * π * I * τ)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hB : ‖cexp (π * I * bernoulliFun 2 (r 0) * τ)‖ =
      ‖cexp (2 * π * I * τ)‖ ^ (bernoulliFun 2 (r 0) / 2) := by
    rw [Complex.norm_exp, norm_exp_two_pi_I_mul, ← Real.exp_mul]
    generalize bernoulliFun 2 (r 0) = B
    congr 1
    simp
    ring
  have hph : ‖cexp (π * I * r 1 * (r 0 - 1))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [siegelFunction_eq_qTheta, norm_mul, norm_mul, norm_neg, hB, hph, mul_one]
  refine (mul_le_mul_of_nonneg_left ((norm_qTheta_le hq _).trans_eq ?_) (by positivity)).trans_eq
    (mul_assoc _ _ _).symm
  rw [norm_exp_two_pi_I_mul_add, Real.rpow_add hA, Real.rpow_sub hA, Real.rpow_one]
  congr 2
  field_simp

/-- With `A = |q|`, every Siegel function satisfies
`|g_{(a, b)}(τ)| ≤ A^{B₂(a)/2} exp ((A^a + A^{1-a}) / (1 - A))` on the upper half-plane. -/
theorem norm_siegelFunction_le_exp (r : Fin 2 → ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    ‖siegelFunction r τ‖ ≤ ‖cexp (2 * π * I * τ)‖ ^ (bernoulliFun 2 (r 0) / 2) *
      Real.exp ((‖cexp (2 * π * I * τ)‖ ^ r 0 + ‖cexp (2 * π * I * τ)‖ ^ (1 - r 0)) /
        (1 - ‖cexp (2 * π * I * τ)‖)) := by
  set A := ‖cexp (2 * π * I * τ)‖ with hA_def
  have hq : A < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have hA : 0 < A := norm_pos_iff.2 (Complex.exp_ne_zero _)
  -- `|1 - w| ≤ 1 + |w| ≤ e^{|w|}`, and `A^a + (A^{1+a} + A^{1-a}) / (1 - A)` simplifies.
  have hw : ‖1 - cexp (2 * π * I * (r 0 * τ + r 1))‖ ≤ Real.exp (A ^ r 0) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_exp_two_pi_I_mul_add, add_comm]
    exact Real.add_one_le_exp _
  have hsum : A ^ r 0 + (A ^ (1 + r 0) + A ^ (1 - r 0)) / (1 - A) =
      (A ^ r 0 + A ^ (1 - r 0)) / (1 - A) := by
    rw [Real.rpow_add hA, Real.rpow_one]
    field_simp [(sub_pos.2 hq).ne']
    ring
  refine (norm_siegelFunction_le r hτ).trans ?_
  rw [mul_assoc, ← hsum, Real.exp_add]
  gcongr

/-- **The product bound for `a ≤ 1/2`.** With `A = |q|`, a Siegel function `g_{(a, b)}` with
`a ≤ 1/2` satisfies `|g_{(a, b)}(τ)| ≤ A^{B₂(a)/2} exp (2 A^a / (1 - A))` on the upper
half-plane. -/
theorem norm_siegelFunction_le_of_le_half {r : Fin 2 → ℝ} (hr : r 0 ≤ 1 / 2) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ‖siegelFunction r τ‖ ≤ ‖cexp (2 * π * I * τ)‖ ^ (bernoulliFun 2 (r 0) / 2) *
      Real.exp (2 * ‖cexp (2 * π * I * τ)‖ ^ r 0 / (1 - ‖cexp (2 * π * I * τ)‖)) := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have hA : 0 < ‖cexp (2 * π * I * τ)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  refine (norm_siegelFunction_le_exp r hτ).trans ?_
  have : ‖cexp (2 * π * I * τ)‖ ^ (1 - r 0) ≤ ‖cexp (2 * π * I * τ)‖ ^ r 0 :=
    Real.rpow_le_rpow_of_exponent_ge hA hq.le (by linarith)
  gcongr
  linarith

/-- **The product bound for `a = 0`.** With `A = |q|`, a Siegel function `g_{(0, b)}` satisfies
`|g_{(0, b)}(τ)| ≤ A^{1/12} |1 - e^{2π i b}| exp (2A / (1 - A))` on the upper half-plane. -/
theorem norm_siegelFunction_le_of_apply_zero_eq_zero {r : Fin 2 → ℝ} (hr : r 0 = 0) {τ : ℂ}
    (hτ : 0 < τ.im) :
    ‖siegelFunction r τ‖ ≤ ‖cexp (2 * π * I * τ)‖ ^ (1 / 12 : ℝ) *
      ‖1 - cexp (2 * π * I * r 1)‖ *
      Real.exp (2 * ‖cexp (2 * π * I * τ)‖ / (1 - ‖cexp (2 * π * I * τ)‖)) := by
  refine (norm_siegelFunction_le r hτ).trans_eq ?_
  rw [hr, bernoulliFun_two]
  simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero, sub_zero, Real.rpow_one,
    ← two_mul]
  congr 2
  norm_num

/-! ### Certified numerical inequalities -/

/-- `150 ≤ e^t` for `t ≥ 7`, from the Taylor polynomial of degree four. -/
private theorem le_exp_of_seven_le {t : ℝ} (ht : 7 ≤ t) : 150 ≤ Real.exp t := by
  refine le_trans ?_ ((Real.sum_le_exp_of_nonneg (x := 7) (by norm_num) 5).trans
    (Real.exp_le_exp.2 ht))
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- If `0 ≤ A ≤ e^{-t}` and `0 ≤ c`, then `A^c ≤ e^{-c t}`. -/
private theorem rpow_le_exp_neg_mul {A t c : ℝ} (hA : 0 ≤ A) (hAt : A ≤ Real.exp (-t))
    (hc : 0 ≤ c) : A ^ c ≤ Real.exp (-(c * t)) := by
  refine (Real.rpow_le_rpow hA hAt hc).trans_eq ?_
  rw [← Real.exp_mul]
  ring_nf

/-- The level-two numerical inequality `2 A^{1/24} exp ((2A + 2A^{1/2}) / (1 - A)) < 1` for
`0 < A ≤ e^{-π √31}`. -/
private theorem level_two_bound {A : ℝ} (hA : 0 < A) (hAt : A ≤ Real.exp (-(π * √31))) :
    2 * A ^ (1 / 24 : ℝ) * Real.exp ((2 * A + 2 * A ^ (1 / 2 : ℝ)) / (1 - A)) < 1 := by
  have hpi := Real.pi_gt_d4
  have h31 : (5.5677 : ℝ) < √31 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  have ht : (17.49 : ℝ) ≤ π * √31 := by nlinarith
  -- The small terms: `A ≤ A^{1/2} ≤ e^{-7} ≤ 1/150`.
  have hsqrt : A ^ (1 / 2 : ℝ) ≤ 1 / 150 := by
    refine (rpow_le_exp_neg_mul hA.le hAt (by norm_num)).trans ?_
    rw [Real.exp_neg]
    exact (inv_anti₀ (by norm_num)
      (le_exp_of_seven_le (t := 1 / 2 * (π * √31)) (by linarith))).trans_eq (one_div 150).symm
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
    refine (rpow_le_exp_neg_mul hA.le hAt (by norm_num)).trans ?_
    refine (Real.exp_le_exp.2 (by linarith : -(1 / 24 * (π * √31)) ≤ -0.728)).trans ?_
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h
  calc 2 * A ^ (1 / 24 : ℝ) * Real.exp ((2 * A + 2 * A ^ (1 / 2 : ℝ)) / (1 - A))
      ≤ 2 * (1 / 2.07) * (149 / 145) := by gcongr
    _ < 1 := by norm_num

/-- The level-three numerical inequality `√3 A^{1/36} exp ((2A + 4A^{1/3}) / (1 - A)) < 1` for
`0 < A ≤ e^{-π √51}`. -/
private theorem level_three_bound {A : ℝ} (hA : 0 < A) (hAt : A ≤ Real.exp (-(π * √51))) :
    √3 * A ^ (1 / 36 : ℝ) * Real.exp ((2 * A + 4 * A ^ (1 / 3 : ℝ)) / (1 - A)) < 1 := by
  have hpi := Real.pi_gt_d4
  have h51 : (7.1414 : ℝ) < √51 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  have h3 : √3 < 1.7321 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have ht : (22.43 : ℝ) ≤ π * √51 := by nlinarith
  -- The small terms: `A ≤ A^{1/3} ≤ e^{-7} ≤ 1/150`.
  have hcbrt : A ^ (1 / 3 : ℝ) ≤ 1 / 150 := by
    refine (rpow_le_exp_neg_mul hA.le hAt (by norm_num)).trans ?_
    rw [Real.exp_neg]
    exact (inv_anti₀ (by norm_num)
      (le_exp_of_seven_le (t := 1 / 3 * (π * √51)) (by linarith))).trans_eq (one_div 150).symm
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
    refine (rpow_le_exp_neg_mul hA.le hAt (by norm_num)).trans ?_
    refine (Real.exp_le_exp.2 (by linarith : -(1 / 36 * (π * √51)) ≤ -0.623)).trans ?_
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h
  calc √3 * A ^ (1 / 36 : ℝ) * Real.exp ((2 * A + 4 * A ^ (1 / 3 : ℝ)) / (1 - A))
      ≤ 1.7321 * (1 / 1.864) * (149 / 143) := by gcongr
    _ < 1 := by norm_num

/-! ### The level-two and level-three estimates -/

/-- `Im τ ≥ √N / 2` means `|q| ≤ e^{-π √N}`. -/
private theorem norm_exp_two_pi_I_mul_le {N : ℝ} {τ : ℂ} (hτ : √N / 2 ≤ τ.im) :
    ‖cexp (2 * π * I * τ)‖ ≤ Real.exp (-(π * √N)) := by
  rw [norm_exp_two_pi_I_mul, Real.exp_le_exp]
  nlinarith [Real.pi_pos]

/-- `|1 - e^{2π i b}| = |2 sin (π b)|`. -/
private theorem norm_one_sub_exp_two_pi_I_mul (b : ℝ) :
    ‖1 - cexp (2 * π * I * b)‖ = |2 * Real.sin (π * b)| := by
  rw [norm_sub_rev, show 2 * π * I * b = I * ((2 * π * b : ℝ) : ℂ) by push_cast; ring,
    norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  ring_nf

/-- The bound `|g_{(0, 1/2)}(τ)| ≤ 2 A^{1/12} exp (2A / (1 - A))`. -/
private theorem norm_siegelFunction_zero_half_le {τ : ℂ} (hτ : 0 < τ.im) :
    ‖siegelFunction ![0, 1 / 2] τ‖ ≤ 2 * ‖cexp (2 * π * I * τ)‖ ^ (1 / 12 : ℝ) *
      Real.exp (2 * ‖cexp (2 * π * I * τ)‖ / (1 - ‖cexp (2 * π * I * τ)‖)) := by
  refine (norm_siegelFunction_le_of_apply_zero_eq_zero (by simp) hτ).trans_eq ?_
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_one_sub_exp_two_pi_I_mul]
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
  have hAt := norm_exp_two_pi_I_mul_le hτ
  generalize ‖cexp (2 * π * I * τ)‖ = A at hq hA h₀ hAt
  refine h₀.trans_lt (lt_of_le_of_lt ?_ (level_two_bound hA hAt))
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
  have hAt := norm_exp_two_pi_I_mul_le hτ
  generalize ‖cexp (2 * π * I * τ)‖ = A at hA h₀ h₁ hAt
  refine lt_of_le_of_lt ?_ (level_two_bound hA hAt)
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
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, norm_one_sub_exp_two_pi_I_mul]
    rw [show π * (1 / 3 : ℝ) = π / 3 by ring, Real.sin_pi_div_three,
      show 2 * (√3 / 2) = √3 by ring, abs_of_nonneg (Real.sqrt_nonneg 3)]
    ring
  have h₁ := norm_siegelFunction_le_of_third hr hτ₀
  have h₂ := norm_siegelFunction_le_of_third hr' hτ₀
  have hAt := norm_exp_two_pi_I_mul_le hτ
  generalize ‖cexp (2 * π * I * τ)‖ = A at hA h₀ h₁ h₂ hAt
  refine lt_of_le_of_lt ?_ (level_three_bound hA hAt)
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
