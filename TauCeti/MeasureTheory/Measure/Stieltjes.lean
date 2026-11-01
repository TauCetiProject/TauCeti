/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Stieltjes functions of measures with finite left tails

A measure on the real line need not be finite to have a real-valued cumulative function:
it suffices that every interval `(-∞, t]` has finite mass. This file bundles that cumulative
function as a `StieltjesFunction` and proves that its Stieltjes measure is the original measure.
In particular this applies to locally finite measures supported on the nonnegative half-line,
without normalizing them to probability measures.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MeasureTheory.Measure

variable (μ : Measure ℝ) (hμ : ∀ t, μ (Iic t) ≠ ∞)

/-- The cumulative function of a measure with finite left tails, bundled as a Stieltjes
function. Unlike a probability cdf, it need not be bounded above. -/
def cumulativeStieltjes : StieltjesFunction ℝ where
  toFun t := μ.real (Iic t)
  mono' _ _ hab := measureReal_mono (Iic_subset_Iic.mpr hab) (hμ _)
  right_continuous' t := by
    have hinter : ⋂ r > t, Iic r = Iic t := by
      ext x
      simpa using forall_gt_imp_ge_iff_le_of_dense (a₁ := x) (a₂ := t)
    have hlim : Tendsto (fun r ↦ μ (Iic r)) (𝓝[>] t) (𝓝 (μ (Iic t))) := by
      rw [← hinter]
      exact tendsto_measure_biInter_gt (fun _ _ ↦ measurableSet_Iic.nullMeasurableSet)
        (fun _ _ _ h ↦ Iic_subset_Iic.mpr h) ⟨t + 1, lt_add_one t, hμ _⟩
    rw [← continuousWithinAt_Ioi_iff_Ici]
    exact (ENNReal.tendsto_toReal (hμ t)).comp hlim

@[simp]
theorem cumulativeStieltjes_apply (t : ℝ) : μ.cumulativeStieltjes hμ t = μ.real (Iic t) :=
  (rfl)

/-- Recover a measure with finite left tails from its cumulative Stieltjes function. -/
@[simp]
theorem measure_cumulativeStieltjes : (μ.cumulativeStieltjes hμ).measure = μ := by
  refine (μ.cumulativeStieltjes hμ).measure.ext_of_Ioc' μ
    (fun _ _ _ ↦ by simp) ?_
  intro a b hab
  rw [StieltjesFunction.measure_Ioc, cumulativeStieltjes_apply, cumulativeStieltjes_apply,
    measureReal_def, measureReal_def, ← ENNReal.toReal_sub_of_le
      (measure_mono (Iic_subset_Iic.mpr hab.le)) (hμ b),
    ENNReal.ofReal_toReal (ENNReal.sub_ne_top (hμ b)), ← Iic_sdiff_Iic,
    measure_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic.nullMeasurableSet (hμ a)]

end MeasureTheory.Measure
