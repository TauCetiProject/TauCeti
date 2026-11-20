/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.MeasureTheory.Integral.CircleAverage
import TauCeti.Analysis.SpecialFunctions.Log.PosLog

/-!
# The mean of `log⁺` against a probability measure

For a nonnegative integrable function `H` and a probability measure `μ`,
`∫ log⁺ H dμ ≤ log⁺ (∫ H dμ) + exp (-1)`.

Jensen's inequality does not apply directly since `log⁺` is not concave; the additive constant
`exp (-1)` is the price of the region where `H < 1`, and it is sharp: if `H` equals `1 / p` on a
set of measure `p` and vanishes elsewhere, the left side is `p * log (1 / p)`, which equals
`exp (-1)` at `p = exp (-1)`, while the right side is `exp (-1)` for every `p`.

The circle-average form `CircleIntegrable.circleAverage_posLog_le_posLog_circleAverage_add` is the
entropy estimate used to bound the proximity function `m(r, f) = circleAverage (log⁺ ‖f‖) 0 r`
of a logarithmic derivative by the logarithm of its circle mean.

## Main results

* `MeasureTheory.Integrable.integral_posLog_le_posLog_integral_add`: the estimate for
  probability measures.
* `CircleIntegrable.circleAverage_posLog_le_posLog_circleAverage_add`: the estimate for circle
  averages.

## Implementation notes

The estimate follows by integrating the pointwise bound
`log⁺ x ≤ log⁺ M + exp (-1) * (x / max 1 M)` with `M = ∫ H dμ`, a consequence of
`log⁺ (s * y) ≤ log⁺ s + log⁺ y` and of `Real.posLog_le_exp_neg_one_mul`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), 627–702, proof of Lemma 6.1.7.
-/

public section

open MeasureTheory Metric Real Set

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- For a nonnegative integrable function `H` and a probability measure `μ`, the mean of
`log⁺ H` is at most `log⁺` of the mean of `H`, plus `exp (-1)`. -/
theorem Integrable.integral_posLog_le_posLog_integral_add [IsProbabilityMeasure μ] {H : α → ℝ}
    (hH : Integrable H μ) (h0 : 0 ≤ᵐ[μ] H) :
    ∫ x, log⁺ (H x) ∂μ ≤ log⁺ (∫ x, H x ∂μ) + exp (-1) := by
  set M := ∫ x, H x ∂μ
  have hM : 0 ≤ M := integral_nonneg_of_ae h0
  set s := max 1 M
  have hs : 0 < s := lt_max_of_lt_left one_pos
  -- The pointwise bound `log⁺ x ≤ log⁺ M + exp (-1) * (x / s)` on `[0, ∞)`.
  have key : ∀ x : ℝ, 0 ≤ x → log⁺ x ≤ log⁺ M + exp (-1) * (x / s) := fun x hx ↦
    calc log⁺ x = log⁺ (s * (x / s)) := by rw [mul_div_cancel₀ _ hs.ne']
      _ ≤ log⁺ s + log⁺ (x / s) := Real.posLog_mul
      _ ≤ log⁺ M + exp (-1) * (x / s) := by
        rw [Real.posLog_eq_log_max_one hM,
          Real.posLog_eq_log (by rw [abs_of_pos hs]; exact le_max_left 1 M)]
        gcongr
        exact Real.posLog_le_exp_neg_one_mul (div_nonneg hx hs.le)
  have hint : Integrable (fun x ↦ log⁺ M + exp (-1) * (H x / s)) μ :=
    (integrable_const _).add ((hH.div_const s).const_mul _)
  calc ∫ x, log⁺ (H x) ∂μ ≤ ∫ x, (log⁺ M + exp (-1) * (H x / s)) ∂μ :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ Real.posLog_nonneg) hint
          (h0.mono fun x hx ↦ key _ hx)
    _ = log⁺ M + exp (-1) * (M / s) := by
        rw [integral_add (integrable_const _) ((hH.div_const s).const_mul _), integral_const,
          integral_const_mul, integral_div]
        simp [M]
    _ ≤ log⁺ M + exp (-1) := by
        gcongr
        exact mul_le_of_le_one_right (exp_pos _).le
          ((div_le_one hs).2 (le_max_right 1 M))

end MeasureTheory

/-- For a circle-integrable function `H` that is nonnegative on the circle, the circle average of
`log⁺ H` is at most `log⁺` of the circle average of `H`, plus `exp (-1)`. -/
theorem CircleIntegrable.circleAverage_posLog_le_posLog_circleAverage_add
    {H : ℂ → ℝ} {c : ℂ} {R : ℝ} (hH : CircleIntegrable H c R) (h0 : ∀ z ∈ sphere c |R|, 0 ≤ H z) :
    circleAverage (fun z ↦ log⁺ (H z)) c R ≤ log⁺ (circleAverage H c R) + exp (-1) := by
  simp only [circleAverage_eq_intervalAverage, uIoc_of_le two_pi_pos.le, average_eq']
  have hint : IntegrableOn (fun θ ↦ H (circleMap c R θ)) (Ioc 0 (2 * π)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hH
  have hne : NeZero (volume.restrict (Ioc 0 (2 * π))) :=
    ⟨by simp [Measure.restrict_eq_zero, pi_pos]⟩
  exact (hint.smul_measure (ENNReal.inv_ne_top.2 (NeZero.ne _)))
    |>.integral_posLog_le_posLog_integral_add
      (.of_forall fun θ ↦ h0 _ (circleMap_mem_sphere' c R θ))
