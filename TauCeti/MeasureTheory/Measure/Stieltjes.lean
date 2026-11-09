/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Real
public import TauCeti.MeasureTheory.Measure.Interval

/-!
# Stieltjes measures and cumulative functions

A measure on the real line need not be finite to have a real-valued cumulative function:
it suffices that every interval `(-∞, t]` has finite mass. This file bundles that cumulative
function as a `StieltjesFunction` and proves that its Stieltjes measure is the original measure.
In particular this applies to locally finite measures supported on the nonnegative half-line,
without normalizing them to probability measures.

On the nonnegative half-line, the cumulative mass of a Stieltjes measure is the increment
of its Stieltjes function from zero.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StieltjesFunction

/-- The cumulative mass of a Stieltjes measure on the half-line is its increment from zero. -/
@[simp]
theorem measure_Iic_nnreal (f : StieltjesFunction ℝ≥0) (t : ℝ≥0) :
    f.measure (Iic t) = ENNReal.ofReal (f t - f 0) := by
  apply f.measure_Iic
  rw [atBot_eq_pure_of_isBot (isBot_bot : IsBot (0 : ℝ≥0))]
  exact tendsto_pure_nhds _ _

end StieltjesFunction

namespace MeasureTheory.Measure

variable (μ : Measure ℝ) (hμ : ∀ t, μ (Iic t) ≠ ∞)

/-- The cumulative function of a measure with finite left tails, bundled as a Stieltjes
function. Unlike a probability cdf, it need not be bounded above. -/
def cumulativeStieltjes : StieltjesFunction ℝ where
  toFun t := μ.real (Iic t)
  mono' _ _ hab := measureReal_mono (Iic_subset_Iic.mpr hab) (hμ _)
  right_continuous' t := by
    have hlim := tendsto_measure_Iic_nhdsGT (μ := μ) ⟨t + 1, lt_add_one t, hμ _⟩
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
  have hdiff : μ.real (Ioc a b) = μ.real (Iic b) - μ.real (Iic a) := by
    rw [← Iic_sdiff_Iic,
      measureReal_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic (hμ b)]
  rw [StieltjesFunction.measure_Ioc, cumulativeStieltjes_apply, cumulativeStieltjes_apply,
    ← hdiff, ofReal_measureReal (measure_ne_top_of_subset Ioc_subset_Iic_self (hμ b))]

end MeasureTheory.Measure
