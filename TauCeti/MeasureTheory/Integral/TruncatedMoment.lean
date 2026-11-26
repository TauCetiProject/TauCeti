/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Truncated second moments

Multiplying a squared norm by `min (c * ‖f x‖) 1` gives an integrable weight when `f` has a
finite second moment and `c ≥ 0`. Its integral tends to zero as `c` tends to zero from above.
-/

public section

open Filter
open scoped Topology

namespace MeasureTheory.Integrable

variable {α E : Type*} [MeasurableSpace α] [SeminormedAddCommGroup E] {μ : Measure α}
  {f : α → E}

private theorem norm_sq_mul_min_mul_one_le {r c : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) :
    ‖r ^ 2 * min (c * r) 1‖ ≤ r ^ 2 := by
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_right (sq_nonneg _) (min_le_right _ _)

/-- The truncated squared norm is integrable when the squared norm is integrable. -/
theorem norm_sq_mul_min_mul_one (h : Integrable (fun x ↦ ‖f x‖ ^ 2) μ) {c : ℝ} (hc : 0 ≤ c) :
    Integrable (fun x ↦ ‖f x‖ ^ 2 * min (c * ‖f x‖) 1) μ := by
  have hm : AEMeasurable (fun x ↦ ‖f x‖) μ := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm] using h.aemeasurable.sqrt
  exact h.mono' (h.aestronglyMeasurable.mul
    ((aemeasurable_const.mul hm).min aemeasurable_const).aestronglyMeasurable)
    (Eventually.of_forall fun x ↦ norm_sq_mul_min_mul_one_le (norm_nonneg (f x)) hc)

/-- The integral of the truncated squared norm tends to zero as the nonnegative scale tends
to zero. Integrability of the squared norm suffices. -/
theorem tendsto_integral_norm_sq_mul_min_mul_one (h : Integrable (fun x ↦ ‖f x‖ ^ 2) μ) :
    Tendsto (fun c : ℝ ↦ ∫ x, ‖f x‖ ^ 2 * min (c * ‖f x‖) 1 ∂μ)
      (𝓝[Set.Ici 0] 0) (𝓝 0) := by
  have hc : ∀ᶠ c : ℝ in 𝓝[Set.Ici 0] 0, 0 ≤ c := self_mem_nhdsWithin
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := μ) (f := fun _ ↦ (0 : ℝ))
    (fun x ↦ ‖f x‖ ^ 2)
    (hc.mono fun _ hc' ↦ (h.norm_sq_mul_min_mul_one hc').aestronglyMeasurable)
    (hc.mono fun _ hc' ↦ Eventually.of_forall fun x ↦
      norm_sq_mul_min_mul_one_le (norm_nonneg (f x)) hc') h
    (Eventually.of_forall fun x ↦ by
      have ht := (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun c : ℝ ↦ c) (𝓝[Set.Ici 0] 0) (𝓝 0))
      simpa using ((ht.mul_const ‖f x‖).min (tendsto_const_nhds (x := (1 : ℝ)))).const_mul
        (‖f x‖ ^ 2))
  simpa using hlim

end MeasureTheory.Integrable
