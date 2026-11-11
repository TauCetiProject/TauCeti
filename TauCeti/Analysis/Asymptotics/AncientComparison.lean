/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-!
# Ancient-time limits of scalar comparisons

Letting a finite time origin tend to negative infinity removes reciprocal-time corrections and
elapsed-time ratios from scalar differential and integrated inequalities. One-sided continuity
extends the resulting integrated comparison to a terminal endpoint. No sign assumption on the
compared scalar quantities is needed.

These are the order and limit steps in the ancient-solution Harnack arguments of Morgan--Tian,
*Ricci Flow and the Poincaré Conjecture*, Theorem 4.37 and Corollary 4.39. The finite-origin
inequalities are hypotheses; geometric Harnack estimates are separate inputs.

Public formalization references:
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace TauCeti

section OrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]

/-- The finite-start reciprocal-time correction vanishes in the ancient limit. -/
theorem tendsto_div_elapsed_time_atBot (t R : 𝕜) :
    Tendsto (fun T : 𝕜 ↦ R / (t - T)) atBot (𝓝 0) := by
  apply Filter.Tendsto.const_div_atTop
  change Tendsto (fun T : 𝕜 ↦ t - T) atBot atTop
  simpa only [sub_eq_add_neg] using
    (tendsto_atTop_add_const_left atBot t tendsto_neg_atBot_atTop)

/-- The two elapsed-time factors have the same time-origin asymptotic. -/
theorem tendsto_elapsed_time_ratio_atBot (a b : 𝕜) :
    Tendsto (fun T : 𝕜 ↦ (a - T) / (b - T)) atBot (𝓝 1) := by
  have hsum : Tendsto (fun T : 𝕜 ↦ 1 + (a - b) / (b - T)) atBot (𝓝 1) := by
    simpa using (tendsto_div_elapsed_time_atBot b (a - b)).const_add 1
  apply hsum.congr'
  filter_upwards [eventually_lt_atBot b] with T hT
  have hne : b - T ≠ 0 := ne_of_gt (sub_pos.mpr hT)
  rw [show a - T = (a - b) + (b - T) from (sub_add_sub_cancel a b T).symm,
    add_div, div_self hne, add_comm]

/-- A differential inequality with a reciprocal-time correction has a nonnegative limit. -/
theorem nonneg_of_eventually_add_div_nonneg {Q R t : 𝕜}
    (hfinite : ∀ᶠ T : 𝕜 in atBot, 0 ≤ Q + R / (t - T)) :
    0 ≤ Q := by
  have hlim : Tendsto (fun T : 𝕜 ↦ Q + R / (t - T)) atBot (𝓝 Q) := by
    simpa using (tendsto_div_elapsed_time_atBot t R).const_add Q
  exact ge_of_tendsto hlim hfinite

/-- The finite-start elapsed-time factor disappears without any sign assumption on curvature. -/
theorem ancient_limit_of_scaled_inequality
    {a b A B E : 𝕜}
    (hfinite : ∀ᶠ T : 𝕜 in atBot,
      A * (a - T) * E ≤ B * (b - T)) :
    A * E ≤ B := by
  let r : 𝕜 → 𝕜 := fun T ↦ (a - T) / (b - T)
  have hr : Tendsto r atBot (𝓝 1) := tendsto_elapsed_time_ratio_atBot a b
  have hleft : Tendsto (fun T ↦ A * r T * E) atBot (𝓝 (A * E)) := by
    simpa [r] using (tendsto_const_nhds.mul hr).mul tendsto_const_nhds
  have hright : Tendsto (fun _ : 𝕜 ↦ B) atBot (𝓝 B) := tendsto_const_nhds
  have hnorm : ∀ᶠ T : 𝕜 in atBot, A * r T * E ≤ B := by
    filter_upwards [hfinite, eventually_lt_atBot b] with T hT hTb
    have hpos : 0 < b - T := sub_pos.mpr hTb
    dsimp only [r]
    rw [← mul_div_assoc, div_mul_eq_mul_div, div_le_iff₀ hpos]
    exact hT
  exact le_of_tendsto_of_tendsto hleft hright hnorm

end OrderedField

/--
Finite-origin integrated estimates on every interior endpoint extend to the
terminal endpoint.  The finite-origin producer remains separate from this
real-analysis consumer.
-/
theorem le_at_right_endpoint_of_finite_origins
    {f q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hqInt : IntervalIntegrable q volume a b)
    (hfinite : ∀ t ∈ Ioo a b, ∀ᶠ T : ℝ in atBot,
      f a * (a - T) * Real.exp (-(∫ s in a..t, q s) / 2) ≤
        f t * (t - T)) :
    f a * Real.exp (-(∫ s in a..b, q s) / 2) ≤ f b := by
  have hprimitive : ContinuousOn (fun t ↦ ∫ s in a..t, q s) (Icc a b) := by
    simpa only [uIcc_of_le (le_of_lt hab)] using
      (intervalIntegral.continuousOn_primitive_interval' hqInt left_mem_uIcc)
  refine ContinuousWithinAt.closure_le
    (by rw [closure_Ioo hab.ne]; exact ⟨hab.le, le_rfl⟩)
    ((continuousWithinAt_const.mul
      (((hprimitive b ⟨hab.le, le_rfl⟩).neg.div_const 2).rexp)).mono Ioo_subset_Icc_self)
    ((hf b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self) ?_
  intro t ht
  exact ancient_limit_of_scaled_inequality (hfinite t ht)

/-- Interior finite-origin differential inequalities reach time zero. -/
theorem nonneg_at_zero_of_finite_origins {q r : ℝ → ℝ}
    (hq : ContinuousWithinAt q (Iic 0) 0)
    (hfinite : ∀ t < 0, ∀ᶠ T : ℝ in atBot,
      0 ≤ q t + r t / (t - T)) :
    0 ≤ q 0 := by
  refine ContinuousWithinAt.closure_le (by simp [closure_Iio])
    continuousWithinAt_const (hq.mono Iio_subset_Iic_self) ?_
  intro t ht
  exact nonneg_of_eventually_add_div_nonneg (hfinite t ht)

end TauCeti
