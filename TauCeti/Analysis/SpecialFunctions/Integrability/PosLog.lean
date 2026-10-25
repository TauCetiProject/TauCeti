/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.PosLog
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Circle averages of `log⁺ ‖f‖⁻¹` for meromorphic functions

For `f` meromorphic on a circle, `log⁺ ‖f‖⁻¹ = log⁺ ‖f‖ - log ‖f‖` is circle integrable, and its
circle average is the difference of the circle averages of `log⁺ ‖f‖` and of `log ‖f‖`. This is the
identity `ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage` of Nevanlinna theory, for
a function meromorphic only on the circle and a circle with arbitrary centre. Since the integrand is
nonnegative, the same identity also computes the lower Lebesgue integral of `log⁺ ‖f‖⁻¹` over one
period, the form needed to apply Fatou's lemma.

## Main results

* `MeromorphicOn.circleIntegrable_posLog_inv_norm` — `log⁺ ‖f‖⁻¹` is circle integrable.
* `MeromorphicOn.circleAverage_posLog_inv_norm` — the circle average of `log⁺ ‖f‖⁻¹` is the
  difference of the circle averages of `log⁺ ‖f‖` and of `log ‖f‖`.
* `MeromorphicOn.lintegral_ofReal_posLog_inv_norm_circleMap` — the lower Lebesgue integral of
  `log⁺ ‖f‖⁻¹` over one period of the circle is `2π` times that difference.
-/

public section

open MeasureTheory Metric Set Real

variable {f : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-- `log⁺ ‖f‖⁻¹ = log⁺ ‖f‖ - log ‖f‖`, as functions. -/
private lemma posLog_inv_norm_eq_sub (f : ℂ → ℂ) :
    (fun z ↦ log⁺ ‖f z‖⁻¹) = (fun z ↦ log⁺ ‖f z‖) - fun z ↦ Real.log ‖f z‖ := by
  funext z
  simp only [Pi.sub_apply]
  linarith [posLog_sub_posLog_inv (x := ‖f z‖)]

namespace MeromorphicOn

/-- If `f` is meromorphic on a circle, then `log⁺ ‖f‖⁻¹` is circle integrable there. -/
theorem circleIntegrable_posLog_inv_norm (hf : MeromorphicOn f (sphere c |r|)) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z‖⁻¹) c r := by
  rw [posLog_inv_norm_eq_sub]
  exact hf.circleIntegrable_posLog_norm.sub hf.circleIntegrable_log_norm

/-- If `f` is meromorphic on a circle, then the circle average of `log⁺ ‖f‖⁻¹` is the difference
of the circle averages of `log⁺ ‖f‖` and of `log ‖f‖`. -/
theorem circleAverage_posLog_inv_norm (hf : MeromorphicOn f (sphere c |r|)) :
    circleAverage (fun z ↦ log⁺ ‖f z‖⁻¹) c r =
      circleAverage (fun z ↦ log⁺ ‖f z‖) c r - circleAverage (fun z ↦ Real.log ‖f z‖) c r := by
  rw [posLog_inv_norm_eq_sub,
    circleAverage_sub hf.circleIntegrable_posLog_norm hf.circleIntegrable_log_norm]

/-- If `f` is meromorphic on a circle, then the lower Lebesgue integral of `log⁺ ‖f‖⁻¹` over one
period `(0, 2π]` of the circle is `2π` times the difference of the circle averages of `log⁺ ‖f‖`
and of `log ‖f‖`. -/
theorem lintegral_ofReal_posLog_inv_norm_circleMap (hf : MeromorphicOn f (sphere c |r|)) :
    ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (log⁺ ‖f (circleMap c r θ)‖⁻¹) =
      ENNReal.ofReal (2 * π * (circleAverage (fun z ↦ log⁺ ‖f z‖) c r -
        circleAverage (fun z ↦ Real.log ‖f z‖) c r)) := by
  rw [← hf.circleAverage_posLog_inv_norm, circleAverage_def,
    intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ two_pi_pos.ne', one_mul,
    ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1
        hf.circleIntegrable_posLog_inv_norm)
      (Filter.Eventually.of_forall fun θ ↦ posLog_nonneg)]

end MeromorphicOn
