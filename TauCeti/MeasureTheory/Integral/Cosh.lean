/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# Integrals involving the hyperbolic cosine

An integrand dominated by `C * cosh (k * t)` has a primitive bounded by
`C * cosh (k * t) / k` for `k > 0`, in either time direction. This estimate controls
Picard iteration in a weighted space of bounded continuous functions on the whole real line.

In the other direction, `1 / cosh x ^ 2`, the derivative of `Real.tanh`, is integrable on the line
with integral `2`: `TauCeti.integrable_one_div_cosh_sq` and `TauCeti.integral_one_div_cosh_sq`.
So `(cosh x)⁻¹` is square integrable (`TauCeti.memLp_inv_cosh`), which makes it the decaying
solution of `v' = -tanh(s) v`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A hyperbolic-cosine bound on an integrand gives a hyperbolic-cosine bound on its interval
integral from zero, for either sign of the endpoint. Only an almost-everywhere bound on the
interval of integration is required. -/
theorem norm_intervalIntegral_le_cosh {k C : ℝ} (hk : 0 < k) (hC : 0 ≤ C)
    {F : ℝ → E} (t : ℝ)
    (hF : ∀ᵐ s ∂volume.restrict (uIoc 0 t), ‖F s‖ ≤ C * Real.cosh (k * s)) :
    ‖∫ s in (0 : ℝ)..t, F s‖ ≤ C * Real.cosh (k * t) / k := by
  have hg : Continuous fun s : ℝ ↦ C * Real.cosh (k * s) := by fun_prop
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ C * Real.sinh (k * s) / k)
      (C * Real.cosh (k * s)) s := by
    intro s
    simpa [← mul_assoc, hk.ne'] using
      (((hasDerivAt_id s).const_mul k).sinh.const_mul C).div_const k
  have hcalc : ∫ s in (0 : ℝ)..t, C * Real.cosh (k * s) =
      C * Real.sinh (k * t) / k := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
      (hg.intervalIntegrable _ _)]
    simp
  calc ‖∫ s in (0 : ℝ)..t, F s‖
      ≤ |∫ s in (0 : ℝ)..t, C * Real.cosh (k * s)| :=
        intervalIntegral.norm_integral_le_abs_of_norm_le hF
          (hg.intervalIntegrable _ _)
    _ = C * |Real.sinh (k * t)| / k := by
        rw [hcalc, abs_div, abs_mul, abs_of_nonneg hC, abs_of_pos hk]
    _ ≤ C * Real.cosh (k * t) / k := by
        gcongr
        rw [Real.abs_sinh, ← Real.cosh_abs (k * t)]
        exact (Real.sinh_lt_cosh _).le

/-- `1 / cosh x ^ 2` is integrable on the line: it is bounded by `4 * exp (-(2 * |x|))`. -/
theorem integrable_one_div_cosh_sq : Integrable fun x : ℝ ↦ 1 / Real.cosh x ^ 2 := by
  refine ((integrable_exp_neg_mul_abs two_pos).const_mul 4).mono'
    (continuous_const.div (by fun_prop) fun x ↦
      (pow_pos (Real.cosh_pos x) 2).ne').aestronglyMeasurable
    (.of_forall fun x ↦ ?_)
  have hc : Real.exp |x| / 2 ≤ Real.cosh x := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    linarith [Real.exp_pos (-|x|)]
  have he : 0 < Real.exp |x| / 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  calc 1 / Real.cosh x ^ 2 ≤ 1 / (Real.exp |x| / 2) ^ 2 := by gcongr
    _ = 4 * Real.exp (-(2 * |x|)) := by
      rw [show -(2 * |x|) = -(|x| + |x|) by ring, Real.exp_neg, Real.exp_add]
      field_simp
      ring

/-- `∫ x, 1 / cosh x ^ 2 = 2`: the integrand is the derivative of `Real.tanh`, which increases
from `-1` to `1`. -/
theorem integral_one_div_cosh_sq : ∫ x : ℝ, 1 / Real.cosh x ^ 2 = 2 := by
  rw [integral_of_hasDerivAt_of_tendsto Real.hasDerivAt_tanh integrable_one_div_cosh_sq
    Real.tendsto_tanh_atBot Real.tendsto_tanh_atTop]
  norm_num

/-- `(cosh x)⁻¹` is square integrable on the line: its square `1 / cosh x ^ 2` is integrable. -/
theorem memLp_inv_cosh : MemLp (fun x : ℝ ↦ (Real.cosh x)⁻¹) 2 :=
  (memLp_two_iff_integrable_sq (by fun_prop)).2 <| by
    simpa [inv_pow, one_div] using integrable_one_div_cosh_sq

end TauCeti
