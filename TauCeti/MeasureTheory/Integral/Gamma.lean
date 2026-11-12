/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Two-sided Gamma integrals on the real line

For `0 < p`, the even function `x ↦ |x| ^ q * exp (-|x| ^ p)` is Lebesgue integrable on `ℝ`
exactly when `-1 < q`, and then its integral is `2 / p * Γ ((q + 1) / p)`.

Mathlib's `integral_rpow_mul_exp_neg_rpow` evaluates the half-line integral; folding the line onto
the positive half-line by `integral_comp_abs` doubles it. Below the threshold the integrand is
comparable to `x ^ q` near the origin, which is not integrable there.

These integrals normalize the generalized normal (exponential power) densities
`exp (-|x| ^ p)` and compute all of their absolute moments.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- **Integrability of the two-sided Gamma integrand.** For `0 < p`, the function
`x ↦ |x| ^ q * exp (-|x| ^ p)` is integrable on `ℝ` exactly when `-1 < q`. -/
theorem integrable_abs_rpow_mul_exp_neg_abs_rpow_iff {p q : ℝ} (hp : 0 < p) :
    Integrable (fun x : ℝ => |x| ^ q * Real.exp (-|x| ^ p)) ↔ -1 < q := by
  refine ⟨fun hint => ?_, fun hq => MeasureTheory.integrable_comp_abs
    (f := fun x : ℝ => x ^ q * Real.exp (-x ^ p)) (integrableOn_rpow_mul_exp_neg_rpow hq hp)⟩
  -- On `(0, 1)` the integrand dominates `exp (-1) * x ^ q`.
  have hscaled : IntegrableOn (fun x : ℝ => Real.exp (-1) * x ^ q) (Ioo 0 1) := by
    refine Integrable.mono' hint.integrableOn (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxq : 0 ≤ x ^ q := Real.rpow_nonneg hx.1.le q
    have hxp : x ^ p ≤ 1 := Real.rpow_le_one hx.1.le hx.2.le hp.le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hxq),
      abs_of_pos hx.1, mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hxp)) hxq
  have hpow : IntegrableOn (fun x : ℝ => x ^ q) (Ioo 0 1) := by
    simpa only [IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
      (Real.exp_ne_zero (-1)))] using hscaled
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mp hpow

/-- **The two-sided Gamma integral.** For `0 < p` and `-1 < q`,
`∫ x, |x| ^ q * exp (-|x| ^ p) = 2 / p * Γ ((q + 1) / p)`. -/
theorem integral_abs_rpow_mul_exp_neg_abs_rpow {p q : ℝ} (hp : 0 < p) (hq : -1 < q) :
    ∫ x : ℝ, |x| ^ q * Real.exp (-|x| ^ p) = 2 / p * Real.Gamma ((q + 1) / p) := by
  rw [integral_comp_abs (f := fun x : ℝ => x ^ q * Real.exp (-x ^ p)),
    integral_rpow_mul_exp_neg_rpow hp hq]
  ring

end TauCeti
