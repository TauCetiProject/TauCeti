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

Since the outer measure of a Stieltjes function is the largest outer measure with its interval
values, an outer measure on `ℝ` bounded on every interval `Ioc a b` by a measure with finite left
tails is bounded by it on every measurable set
(`MeasureTheory.OuterMeasure.le_measure_of_Ioc_le`).
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

namespace MeasureTheory.OuterMeasure

/-- An outer measure on `ℝ` that is bounded on every interval `Ioc a b` by a measure with finite
left tails is bounded by it on every measurable set. The proof compares the outer measure with
that of the cumulative Stieltjes function of the measure, which is the largest outer measure with
these interval values. -/
theorem le_measure_of_Ioc_le (m : OuterMeasure ℝ) (ν : Measure ℝ)
    (hν : ∀ t, ν (Iic t) ≠ ∞) (h : ∀ a b, m (Ioc a b) ≤ ν (Ioc a b)) {s : Set ℝ}
    (hs : MeasurableSet s) : m s ≤ ν s := by
  set F := ν.cumulativeStieltjes hν
  have hF (a b : ℝ) : ν (Ioc a b) = ENNReal.ofReal (F b - F a) := by
    rw [← F.measure_Ioc, Measure.measure_cumulativeStieltjes]
  have hmF : m ≤ F.outer := by
    refine OuterMeasure.le_ofFunction.2 fun t ↦ ?_
    rw [F.length_eq]
    refine le_iInf₂ fun a b ↦ le_iInf fun hab ↦ ?_
    rw [← hF]
    exact (measure_mono fun x hx ↦ hab ⟨hx, notMem_botSet_of_lt (sub_one_lt x)⟩).trans (h a b)
  have hcar : (inferInstance : MeasurableSpace ℝ) ≤ F.outer.caratheodory := by
    rw [BorelSpace.measurable_eq (α := ℝ)]
    exact F.borel_le_measurable
  have hFν : F.outer.toMeasure hcar = ν := by
    refine Measure.ext_of_Ioc' _ _ (fun a b _ ↦ ?_) fun a b _ ↦ ?_ <;>
      rw [toMeasure_apply _ _ measurableSet_Ioc, F.outer_Ioc]
    · exact ENNReal.ofReal_ne_top
    · exact (hF a b).symm
  calc m s ≤ F.outer s := hmF s
    _ = ν s := by rw [← toMeasure_apply _ hcar hs, hFν]

end MeasureTheory.OuterMeasure
