/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Integrability of ordinary derivatives

For a `K`-Lipschitz map `f : ℝ → F` vanishing on `[R, ∞)` with `0 ≤ R`, the weighted squared
derivative `r ↦ r ^ k * ‖deriv f r‖ ^ 2` (and `r ↦ r ^ k * (deriv f r) ^ 2` when `F = ℝ`)
is integrable on `(0, ∞)`.

## Main results

* `TauCeti.integrableOn_pow_mul_norm_deriv_sq_of_lipschitzWith`: `Ioi 0`-integrability of
  `r ^ k * ‖deriv f r‖ ^ 2` for a Lipschitz map vanishing on `[R, ∞)`.
* `TauCeti.integrableOn_pow_mul_deriv_sq_of_lipschitzWith`: scalar version for `f : ℝ → ℝ`.
-/

public section

open MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti

/-- For a `K`-Lipschitz map `f : ℝ → F` into a complete space vanishing on `[R, ∞)` with
`0 ≤ R`, the weighted squared derivative `r ↦ r ^ k * ‖deriv f r‖ ^ 2` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_norm_deriv_sq_of_lipschitzWith {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {K : ℝ≥0} {f : ℝ → F} (hf : LipschitzWith K f)
    {R : ℝ} (hR : 0 ≤ R) (hfR : ∀ r ≥ R, f r = 0) :
    IntegrableOn (fun r : ℝ ↦ r ^ k * ‖deriv f r‖ ^ 2) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun r : ℝ ↦ r ^ k * ‖deriv f r‖ ^ 2) volume :=
    (continuous_pow k).aestronglyMeasurable.mul ((aestronglyMeasurable_deriv f volume).norm.pow 2)
  have hIoc : IntegrableOn (fun r : ℝ ↦ r ^ k * ‖deriv f r‖ ^ 2) (Ioc 0 R) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top hmeas.restrict (R ^ k * (K : ℝ) ^ 2) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr ↦ ?_
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr.1.le _) (sq_nonneg _))]
    have hnorm : ‖deriv f r‖ ≤ K := norm_deriv_le_of_lipschitz hf
    exact mul_le_mul (pow_le_pow_left₀ hr.1.le hr.2 _)
      (sq_le_sq.2 (by rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg K.coe_nonneg]))
      (sq_nonneg _) (pow_nonneg hR _)
  have hIoi : IntegrableOn (fun r : ℝ ↦ r ^ k * ‖deriv f r‖ ^ 2) (Ioi R) := by
    refine integrableOn_zero.congr_fun (fun r (hr : R < r) ↦ ?_) measurableSet_Ioi
    have h0 : f =ᶠ[𝓝 r] 0 :=
      Filter.eventually_of_mem (Ioi_mem_nhds hr) fun x hx ↦ hfR x hx.le
    simp [h0.deriv_eq]
  rw [← Ioc_union_Ioi_eq_Ioi hR]
  exact hIoc.union hIoi

/-- For a `K`-Lipschitz real function `f : ℝ → ℝ` vanishing on `[R, ∞)` with `0 ≤ R`, the
weighted squared derivative `r ↦ r ^ k * (deriv f r) ^ 2` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_deriv_sq_of_lipschitzWith {k : ℕ} {K : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith K f) {R : ℝ} (hR : 0 ≤ R) (hfR : ∀ r ≥ R, f r = 0) :
    IntegrableOn (fun r : ℝ ↦ r ^ k * (deriv f r) ^ 2) (Ioi 0) := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    integrableOn_pow_mul_norm_deriv_sq_of_lipschitzWith (k := k) hf hR hfR

end TauCeti
