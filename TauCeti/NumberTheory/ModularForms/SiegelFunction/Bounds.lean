/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic

/-!
# Effective bounds for Siegel functions

Write `A = |q| = e^{-2π Im τ}` for `τ` in the upper half-plane. Bounding each factor of the
product defining the Siegel function `g_r(τ)` by `|1 - x| ≤ 1 + |x| ≤ e^{|x|}` gives
`|g_{(a, b)}(τ)| ≤ A^{B₂(a)/2} |1 - w| exp ((A^{1+a} + A^{1-a}) / (1 - A))` for every real
`r = (a, b)`, where `w = e^{2π i (a τ + b)}` has `|w| = A^a` and `B₂(x) = x² - x + 1/6`. Two
consequences are
`|g_{(a, b)}(τ)| ≤ A^{B₂(a)/2} exp (2 A^a / (1 - A))` for `a ≤ 1/2` and
`|g_{(0, b)}(τ)| ≤ A^{1/12} |1 - e^{2π i b}| exp (2A / (1 - A))`.

These are the analytic estimates of the class number one problem; the numerical inequalities
derived from them at large imaginary part are in
`TauCeti.NumberTheory.ModularForms.SiegelFunction.ClassNumberOne`.

## Main results

* `TauCeti.ModularForm.norm_siegelFunction_le`: the bound with the exact factor `|1 - w|`.
* `TauCeti.ModularForm.norm_siegelFunction_le_exp`: `|g_{(a, b)}(τ)|` is at most
  `A^{B₂(a)/2} exp ((A^a + A^{1-a}) / (1 - A))`.
* `TauCeti.ModularForm.norm_siegelFunction_le_of_le_half`: for `a ≤ 1/2`, the bound
  `A^{B₂(a)/2} exp (2 A^a / (1 - A))`.
* `TauCeti.ModularForm.norm_siegelFunction_le_of_apply_zero_eq_zero`: for `a = 0`, the bound
  `A^{1/12} |1 - e^{2π i b}| exp (2A / (1 - A))`.

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §5 (the product
  estimates for Siegel functions).
-/

public section

open Complex
open scoped Real

namespace TauCeti.ModularForm

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
    rw [Complex.norm_exp, UpperHalfPlane.norm_exp_two_pi_I_mul, ← Real.exp_mul]
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
  rw [UpperHalfPlane.norm_exp_two_pi_I_mul_add, Real.rpow_add hA, Real.rpow_sub hA,
    Real.rpow_one]
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
    rw [norm_one, UpperHalfPlane.norm_exp_two_pi_I_mul_add, add_comm]
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

end TauCeti.ModularForm
