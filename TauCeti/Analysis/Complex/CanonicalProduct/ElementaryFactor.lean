/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Analytic.Order

/-!
# The elementary factor of a genus-one canonical product

`Complex.weierstrassFactorOne z = (1 - z) * exp z` cancels the linear term of
`1 - z`. Its deviation from one is quadratic near zero, which supplies the
summable majorant for genus-one canonical products. The global logarithmic
bound supplies the elementary growth estimate used in Hadamard factorization.

The quadratic estimate uses Mathlib's `Complex.norm_exp_sub_one_sub_id_le` and
`Complex.norm_exp_sub_one_le`. The simple-zero statement uses
`AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

namespace Complex

/-- The genus-one Weierstrass elementary factor. -/
noncomputable def weierstrassFactorOne (z : ℂ) : ℂ := (1 - z) * exp z

/-- The defining formula for the genus-one elementary factor. -/
theorem weierstrassFactorOne_def (z : ℂ) :
    weierstrassFactorOne z = (1 - z) * exp z := (rfl)

/-- The elementary factor is normalized to one at the origin. -/
@[simp]
theorem weierstrassFactorOne_zero : weierstrassFactorOne 0 = 1 := by
  simp [weierstrassFactorOne]

/-- The elementary factor vanishes at one. -/
@[simp]
theorem weierstrassFactorOne_one : weierstrassFactorOne 1 = 0 := by
  simp [weierstrassFactorOne]

/-- The only zero of the elementary factor is one. -/
@[simp]
theorem weierstrassFactorOne_eq_zero_iff {z : ℂ} :
    weierstrassFactorOne z = 0 ↔ z = 1 := by
  rw [weierstrassFactorOne_def, mul_eq_zero, or_iff_left (exp_ne_zero z), sub_eq_zero]
  exact eq_comm

/-- The derivative has no constant term. -/
theorem hasDerivAt_weierstrassFactorOne (z : ℂ) :
    HasDerivAt weierstrassFactorOne (-z * exp z) z := by
  have h : HasDerivAt (fun w : ℂ ↦ (1 - w) * exp w)
      ((0 - 1) * exp z + (1 - z) * exp z) z :=
    ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).mul
    (hasDerivAt_exp z)
  convert h using 1
  · exact funext weierstrassFactorOne_def
  · ring

/-- The elementary factor is complex differentiable everywhere. -/
@[fun_prop]
theorem differentiable_weierstrassFactorOne : Differentiable ℂ weierstrassFactorOne :=
  fun z ↦ (hasDerivAt_weierstrassFactorOne z).differentiableAt

/-- The elementary factor is analytic at every complex point. -/
@[fun_prop]
theorem analyticAt_weierstrassFactorOne (z : ℂ) : AnalyticAt ℂ weierstrassFactorOne z := by
  rw [show weierstrassFactorOne = fun w : ℂ ↦ (1 - w) * exp w from
    funext weierstrassFactorOne_def]
  fun_prop

/-- The derivative of the elementary factor is `-z * exp z`. -/
@[simp]
theorem deriv_weierstrassFactorOne (z : ℂ) :
    deriv weierstrassFactorOne z = -z * exp z :=
  (hasDerivAt_weierstrassFactorOne z).deriv

/-- The unique zero of the elementary factor is simple. -/
theorem analyticOrderAt_weierstrassFactorOne_one :
    analyticOrderAt weierstrassFactorOne 1 = 1 := by
  apply (analyticAt_weierstrassFactorOne 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    weierstrassFactorOne_one
  rw [deriv_weierstrassFactorOne]
  exact mul_ne_zero (by norm_num) (exp_ne_zero _)

/-- The rational logarithmic-derivative formula. At the unique zero both sides use
total division and equal zero. -/
theorem logDeriv_weierstrassFactorOne (z : ℂ) :
    logDeriv weierstrassFactorOne z = -z / (1 - z) := by
  rw [logDeriv_apply, deriv_weierstrassFactorOne, weierstrassFactorOne_def]
  exact mul_div_mul_right _ _ (exp_ne_zero z)

/-- A quadratic deviation bound, valid on the whole closed unit disk. -/
theorem norm_weierstrassFactorOne_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖weierstrassFactorOne z - 1‖ ≤ 3 * ‖z‖ ^ 2 := by
  have hid : weierstrassFactorOne z - 1 =
      (exp z - 1 - z) - z * (exp z - 1) := by
    rw [weierstrassFactorOne_def]
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
theorem log_norm_weierstrassFactorOne_le (z : ℂ) :
    Real.log ‖weierstrassFactorOne z‖ ≤ 2 * ‖z‖ := by
  by_cases hz : z = 1
  · subst z
    simp
  have h : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))
  rw [weierstrassFactorOne_def, norm_mul, norm_exp,
    Real.log_mul (ne_of_gt h) (Real.exp_ne_zero _), Real.log_exp]
  have hn : ‖1 - z‖ ≤ 1 + ‖z‖ := by simpa using norm_sub_le (1 : ℂ) z
  have hl := Real.log_le_sub_one_of_pos h
  have hr := re_le_norm z
  linarith

/-- Composing the elementary factor with a nonzero slope preserves its simple root. -/
theorem analyticOrderAt_weierstrassFactorOne_mul {c z : ℂ} (h : c * z = 1) :
    analyticOrderAt (fun w ↦ weierstrassFactorOne (c * w)) z = 1 := by
  have hc : c ≠ 0 := by intro hc; simp [hc] at h
  have hd : HasDerivAt (fun w ↦ c * w) c z := by
    simpa using (hasDerivAt_id z).const_mul c
  have hg : AnalyticAt ℂ (fun w ↦ c * w) z := by fun_prop
  have heq : (fun w ↦ weierstrassFactorOne (c * w)) =
      weierstrassFactorOne ∘ (fun w ↦ c * w) := rfl
  rw [heq, analyticOrderAt_comp_of_deriv_ne_zero hg (by rwa [hd.deriv]), h]
  exact analyticOrderAt_weierstrassFactorOne_one

/-- The rational logarithmic derivative of the genus-one factor with slope `a`,
using total division at its pole. -/
@[expose]
noncomputable def logDerivWeierstrassFactorOneMul (a z : ℂ) : ℂ :=
  -a ^ 2 * z / (1 - a * z)

/-- The defining rational expression for the slope-dependent logarithmic derivative. -/
@[simp]
theorem logDerivWeierstrassFactorOneMul_def (a z : ℂ) :
    logDerivWeierstrassFactorOneMul a z = -a ^ 2 * z / (1 - a * z) := rfl

/-- The paired rational logarithmic derivative of an elementary factor with a complex slope. -/
theorem logDeriv_weierstrassFactorOne_mul (a z : ℂ) :
    logDeriv (fun w ↦ weierstrassFactorOne (a * w)) z = logDerivWeierstrassFactorOneMul a z := by
  rw [logDerivWeierstrassFactorOneMul_def]
  have hd : HasDerivAt (fun w : ℂ ↦ a * w) a z := by
    simpa using (hasDerivAt_id z).const_mul a
  rw [logDeriv_fun_comp (differentiable_weierstrassFactorOne _) hd.differentiableAt,
    logDeriv_weierstrassFactorOne, hd.deriv]
  ring

end Complex
