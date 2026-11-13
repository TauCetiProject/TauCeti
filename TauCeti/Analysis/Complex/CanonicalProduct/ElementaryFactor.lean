/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Analytic.Order

import Mathlib.Algebra.Ring.GeomSum

/-!
# Weierstrass elementary factors

The primary factor `weierstrassFactor p z` is `(1 - z)` times the exponential of the
first `p` positive logarithmic terms. Its only zero is a simple zero at one, for every genus.
The definition uses Mathlib's `Complex.logTaylor`, with an equivalent finite-sum formula.

At genus one this is `(1 - z) * exp z`. Its quadratic deviation and global logarithmic
bounds supply the estimates for the genus-one product and reciprocal Gamma function.
The paired rational logarithmic derivative retains this genus-one specialization.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11 (the genus-one case).
-/

public section

open scoped BigOperators

namespace Complex

/-- The Weierstrass elementary factor of genus `p`. -/
noncomputable def weierstrassFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (-logTaylor (p + 1) (-z))

/-- The primary factor in terms of Mathlib's logarithmic Taylor polynomial. -/
theorem weierstrassFactor_def (p : ℕ) (z : ℂ) :
    weierstrassFactor p z = (1 - z) * exp (-logTaylor (p + 1) (-z)) := by
  rfl

/-- The finite-sum formula for the primary factor, including the empty sum at genus zero. -/
theorem weierstrassFactor_eq_mul_exp_sum (p : ℕ) (z : ℂ) :
    weierstrassFactor p z =
      (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := by
  have hsign (j : ℕ) : (-1 : ℂ) ^ (j + 1) * (-z) ^ j = -z ^ j := by
    calc
      _ = -((-1 : ℂ) ^ j * (-z) ^ j) := by rw [pow_succ]; ring
      _ = -(((-1 : ℂ) * (-z)) ^ j) := by rw [mul_pow]
      _ = _ := by simp
  rw [weierstrassFactor_def]
  congr 2
  simp only [logTaylor, hsign, neg_div, ← Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_range_succ']
  simp

/-- The genus-zero factor is linear. -/
@[simp]
theorem weierstrassFactor_zero_left (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor_eq_mul_exp_sum]

/-- The genus-one factor is `(1 - z) * exp z`. -/
theorem weierstrassFactor_one_left (z : ℂ) :
    weierstrassFactor 1 z = (1 - z) * exp z := by
  simp [weierstrassFactor_eq_mul_exp_sum]

/-- Every elementary factor is normalized to one at the origin. -/
@[simp]
theorem weierstrassFactor_zero (p : ℕ) : weierstrassFactor p 0 = 1 := by
  simp [weierstrassFactor_def, logTaylor_at_zero]

/-- Every elementary factor vanishes at one. -/
@[simp]
theorem weierstrassFactor_one (p : ℕ) : weierstrassFactor p 1 = 0 := by
  simp [weierstrassFactor_def]

/-- The only zero of any elementary factor is one. -/
@[simp]
theorem weierstrassFactor_eq_zero_iff (p : ℕ) {z : ℂ} :
    weierstrassFactor p z = 0 ↔ z = 1 := by
  rw [weierstrassFactor_def, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero]
  exact eq_comm

private theorem hasDerivAt_neg_logTaylor_neg (p : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ -logTaylor (p + 1) (-w))
      (∑ j ∈ Finset.range p, z ^ j) z := by
  have h := ((hasDerivAt_logTaylor p (-z)).comp z (hasDerivAt_neg z)).neg
  simpa only [← mul_pow, neg_one_mul, neg_neg, mul_neg, mul_one, Function.comp_def] using! h

/-- The derivative of a primary factor vanishes to its genus at the origin. -/
theorem hasDerivAt_weierstrassFactor (p : ℕ) (z : ℂ) :
    HasDerivAt (weierstrassFactor p)
      (-z ^ p * exp (-logTaylor (p + 1) (-z))) z := by
  have h := ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).mul
    ((hasDerivAt_neg_logTaylor_neg p z).cexp)
  convert h using 1
  · exact funext (weierstrassFactor_def p)
  · dsimp only [Pi.sub_apply, id_eq]
    have hg := mul_neg_geom_sum z p
    linear_combination -exp (-logTaylor (p + 1) (-z)) * hg

/-- Every primary factor is complex differentiable everywhere. -/
@[fun_prop]
theorem differentiable_weierstrassFactor (p : ℕ) :
    Differentiable ℂ (weierstrassFactor p) :=
  fun z ↦ (hasDerivAt_weierstrassFactor p z).differentiableAt

/-- Every primary factor is analytic at every complex point. -/
@[fun_prop]
theorem analyticAt_weierstrassFactor (p : ℕ) (z : ℂ) :
    AnalyticAt ℂ (weierstrassFactor p) z := by
  rw [show weierstrassFactor p = fun w : ℂ ↦
      (1 - w) * exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1)) from
    funext (weierstrassFactor_eq_mul_exp_sum p)]
  fun_prop

/-- The derivative of a primary factor. -/
@[simp]
theorem deriv_weierstrassFactor (p : ℕ) (z : ℂ) :
    deriv (weierstrassFactor p) z = -z ^ p * exp (-logTaylor (p + 1) (-z)) :=
  (hasDerivAt_weierstrassFactor p z).deriv

/-- The unique zero of every elementary factor is simple. -/
theorem analyticOrderAt_weierstrassFactor_one (p : ℕ) :
    analyticOrderAt (weierstrassFactor p) 1 = 1 := by
  apply (analyticAt_weierstrassFactor p 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (weierstrassFactor_one p)
  simp [deriv_weierstrassFactor]

/-- The rational logarithmic derivative, using total division at the unique zero. -/
theorem logDeriv_weierstrassFactor (p : ℕ) (z : ℂ) :
    logDeriv (weierstrassFactor p) z = -z ^ p / (1 - z) := by
  rw [logDeriv_apply, deriv_weierstrassFactor, weierstrassFactor_def]
  exact mul_div_mul_right _ _ (exp_ne_zero _)

/-- A quadratic deviation bound, valid on the whole closed unit disk. -/
theorem norm_weierstrassFactor_one_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖weierstrassFactor 1 z - 1‖ ≤ 3 * ‖z‖ ^ 2 := by
  have hid : weierstrassFactor 1 z - 1 =
      (exp z - 1 - z) - z * (exp z - 1) := by
    rw [weierstrassFactor_one_left]
    ring
  rw [hid]
  calc
    _ ≤ ‖exp z - 1 - z‖ + ‖z * (exp z - 1)‖ := norm_sub_le _ _
    _ ≤ ‖z‖ ^ 2 + ‖z‖ * (2 * ‖z‖) := by
      rw [norm_mul]
      exact add_le_add (norm_exp_sub_one_sub_id_le hz)
        (mul_le_mul_of_nonneg_left (norm_exp_sub_one_le hz) (norm_nonneg z))
    _ = 3 * ‖z‖ ^ 2 := by ring

/-- A linear global upper bound for the logarithm of the norm. -/
theorem log_norm_weierstrassFactor_one_le (z : ℂ) :
    Real.log ‖weierstrassFactor 1 z‖ ≤ 2 * ‖z‖ := by
  by_cases hz : z = 1
  · subst z
    simp
  have h : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
  rw [weierstrassFactor_one_left, norm_mul, norm_exp,
    Real.log_mul (ne_of_gt h) (Real.exp_ne_zero _), Real.log_exp]
  have hn : ‖1 - z‖ ≤ 1 + ‖z‖ := by simpa using norm_sub_le (1 : ℂ) z
  have hl := Real.log_le_sub_one_of_pos h
  have hr := re_le_norm z
  linarith

/-- Composing any elementary factor with a nonzero slope preserves its simple root. -/
theorem analyticOrderAt_weierstrassFactor_mul (p : ℕ) {c z : ℂ} (h : c * z = 1) :
    analyticOrderAt (fun w ↦ weierstrassFactor p (c * w)) z = 1 := by
  have hc : c ≠ 0 := by intro hc; simp [hc] at h
  have hd : HasDerivAt (fun w ↦ c * w) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have hg : AnalyticAt ℂ (fun w ↦ c * w) z := by fun_prop
  have heq : (fun w ↦ weierstrassFactor p (c * w)) =
      weierstrassFactor p ∘ (fun w ↦ c * w) := rfl
  rw [heq, analyticOrderAt_comp_of_deriv_ne_zero hg (by rwa [hd.deriv]), h]
  exact analyticOrderAt_weierstrassFactor_one p

/-- The rational logarithmic derivative of the genus-one factor with slope `a`,
using total division at its pole. -/
noncomputable def logDerivWeierstrassFactorOneMul (a z : ℂ) : ℂ :=
  -a ^ 2 * z / (1 - a * z)

/-- The defining rational expression for the slope-dependent logarithmic derivative. -/
theorem logDerivWeierstrassFactorOneMul_def (a z : ℂ) :
    logDerivWeierstrassFactorOneMul a z = -a ^ 2 * z / (1 - a * z) := (rfl)

/-- The slope-dependent logarithmic derivative is quadratic in the slope while `‖a * z‖ ≤ 1 / 2`
keeps its denominator away from zero. -/
theorem norm_logDerivWeierstrassFactorOneMul_le {a z : ℂ} (h : ‖a * z‖ ≤ 1 / 2) :
    ‖logDerivWeierstrassFactorOneMul a z‖ ≤ (2 * ‖z‖) * ‖a‖ ^ 2 := by
  have hden : (1 / 2 : ℝ) ≤ ‖1 - a * z‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (a * z)
    rw [norm_one] at ht
    linarith
  calc
    _ = (‖a‖ ^ 2 * ‖z‖) / ‖1 - a * z‖ := by
      rw [logDerivWeierstrassFactorOneMul_def, norm_div, norm_mul, norm_neg, norm_pow]
    _ ≤ (‖a‖ ^ 2 * ‖z‖) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = (2 * ‖z‖) * ‖a‖ ^ 2 := by ring

/-- At an inverse slope `ρ⁻¹`, the logarithmic derivative is the paired fraction
`1 / (z - ρ) + 1 / ρ` away from the zero `ρ` of the factor. -/
theorem logDerivWeierstrassFactorOneMul_inv {ρ z : ℂ} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    logDerivWeierstrassFactorOneMul ρ⁻¹ z = 1 / (z - ρ) + 1 / ρ := by
  have hd : 1 - ρ⁻¹ * z ≠ 0 := sub_ne_zero.mpr fun h ↦
    hz ((inv_mul_eq_one₀ hρ).mp h.symm).symm
  rw [logDerivWeierstrassFactorOneMul_def]
  field_simp [hρ, hd, sub_ne_zero.mpr hz]
  ring

/-- The paired rational logarithmic derivative of an elementary factor with a complex slope. -/
@[simp]
theorem logDeriv_weierstrassFactor_one_mul (a z : ℂ) :
    logDeriv (fun w ↦ weierstrassFactor 1 (a * w)) z = logDerivWeierstrassFactorOneMul a z := by
  rw [logDerivWeierstrassFactorOneMul_def]
  have hd : HasDerivAt (fun w : ℂ ↦ a * w) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  rw [logDeriv_fun_comp (differentiable_weierstrassFactor 1 _) hd.differentiableAt,
    logDeriv_weierstrassFactor 1, hd.deriv]
  ring

/-- The global logarithmic bound in exponential form, which also covers the zero at one. -/
theorem norm_weierstrassFactor_one_le_exp (z : ℂ) :
    ‖weierstrassFactor 1 z‖ ≤ Real.exp (2 * ‖z‖) := by
  rcases (norm_nonneg (weierstrassFactor 1 z)).eq_or_lt with h | h
  · rw [← h]
    positivity
  · rw [← Real.exp_log h]
    exact Real.exp_le_exp.mpr (log_norm_weierstrassFactor_one_le z)

/-- The quadratic deviation bound in exponential form, on the closed unit disk. -/
theorem norm_weierstrassFactor_one_le_exp_sq {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖weierstrassFactor 1 z‖ ≤ Real.exp (3 * ‖z‖ ^ 2) := by
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖weierstrassFactor 1 z - 1‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ 3 * ‖z‖ ^ 2 + 1 := by
      rw [norm_one, add_comm]
      exact add_le_add_left (norm_weierstrassFactor_one_sub_one_le hz) 1
    _ ≤ Real.exp (3 * ‖z‖ ^ 2) := Real.add_one_le_exp _

end Complex
