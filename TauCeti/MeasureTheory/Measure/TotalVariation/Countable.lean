/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import TauCeti.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Total variation distance on countable spaces

On a countable measurable space with measurable singletons, every measurable event decomposes into
its singleton masses. For arbitrary measures `μ` and `ν`, the largest excess `μ A - ν A` over
measurable events equals the series `∑' y, (μ {y} - ν {y})` of positive singleton differences (with
truncated subtraction in `ℝ≥0∞`), and the event `{y | ν {y} < μ {y}}` attains that excess whenever
`ν {y | ν {y} < μ {y}} ≠ ⊤`. For a finite measure `μ` and a measure `ν` of the same total mass,
Mathlib's extended total variation distance `etvDist μ ν` is twice that series.

For any two finite measures (without assuming equal total mass), total variation distance is the
sum of the absolute differences of their singleton masses. We give the extended and real formulas,
together with summability of the real series. No probability normalization is required, and the
formulas also cover the empty space.

These identities identify total variation distance between distributions on a countable state
space with the ℓ¹ distance of their point masses. We use Mathlib's normalization: the distance
between probability measures is at most two, not one.

The ℓ¹ proof uses Mathlib's `VectorMeasure.variation_apply_singleton` and the decomposition of a
measure into its singleton masses, rather than constructing a separate discrete distance.

## Main declarations

* `MeasureTheory.etvDist_eq_tsum_enorm_singleton`,
  `MeasureTheory.summable_abs_measureReal_singleton_sub`,
  `MeasureTheory.tvDist_eq_tsum_abs_singleton`: the extended and real ℓ¹ singleton-mass formulas
  for arbitrary finite measures.
* `MeasureTheory.measure_setOf_lt_sub_eq_tsum`: the event `{y | ν {y} < μ {y}}` has excess equal
  to `∑' y, (μ {y} - ν {y})` whenever `ν {y | ν {y} < μ {y}} ≠ ⊤`.
* `MeasureTheory.iSup_measure_sub_eq_tsum`: the largest excess `μ A - ν A` over measurable events
  is `∑' y, (μ {y} - ν {y})`.
* `MeasureTheory.etvDist_eq_two_mul_tsum_sub`: for a finite measure and a measure of the same
  total mass, `etvDist μ ν = 2 * ∑' y, (μ {y} - ν {y})`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {μ ν : Measure α}

section FiniteMeasures

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- On a countable space, extended total variation distance is the sum of the extended norms
of the differences of singleton masses. -/
theorem etvDist_eq_tsum_enorm_singleton :
    etvDist μ ν = ∑' x, ‖μ.real {x} - ν.real {x}‖ₑ := by
  rw [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist]
  rw [← (μ.toSignedMeasure - ν.toSignedMeasure).variation.tsum_indicator_apply_singleton
    Set.univ MeasurableSet.univ]
  simp [VectorMeasure.variation_apply_singleton, Measure.toSignedMeasure_apply]

/-- The absolute differences of singleton masses of two finite measures form a summable family
on a countable space. -/
theorem summable_abs_measureReal_singleton_sub :
    Summable (fun x => |μ.real {x} - ν.real {x}|) := by
  have h := ENNReal.summable_toReal (etvDist_eq_tsum_enorm_singleton (μ := μ) (ν := ν) ▸
    etvDist_ne_top μ ν)
  simpa using h

/-- On a countable space, total variation distance is the ℓ¹ distance of the singleton masses.
In particular, no factor of one half occurs with Mathlib's normalization. -/
theorem tvDist_eq_tsum_abs_singleton :
    tvDist μ ν = ∑' x, |μ.real {x} - ν.real {x}| := by
  rw [tvDist, etvDist_eq_tsum_enorm_singleton, ENNReal.tsum_toReal_eq (by simp)]
  simp

end FiniteMeasures

/-- On a countable measurable space with measurable singletons, the event `{y | ν {y} < μ {y}}` has
excess equal to the series of positive singleton differences `μ {y} - ν {y}`, with truncated
subtraction in `ℝ≥0∞`, provided its `ν`-mass is finite. -/
theorem measure_setOf_lt_sub_eq_tsum (hν : ν {y | ν {y} < μ {y}} ≠ ⊤) :
    μ {y | ν {y} < μ {y}} - ν {y | ν {y} < μ {y}} = ∑' y, (μ {y} - ν {y}) := by
  let s : Set α := {y | ν {y} < μ {y}}
  have hs : MeasurableSet s := (Set.to_countable s).measurableSet
  have htsum : ∑' y, (μ {y} - ν {y}) = ∑' y, s.indicator (fun y => μ {y} - ν {y}) y := by
    refine tsum_congr fun y => ?_
    by_cases hy : y ∈ s
    · simp [Set.indicator_of_mem hy]
    · have hle : μ {y} ≤ ν {y} := not_lt.1 hy
      simp [Set.indicator_of_notMem hy, tsub_eq_zero_of_le hle]
  have hadd : (∑' y, (μ {y} - ν {y})) + ν s = μ s := by
    rw [htsum, ← ν.tsum_indicator_apply_singleton s hs, ← μ.tsum_indicator_apply_singleton s hs,
      ← tsum_add]
    refine tsum_congr fun y => ?_
    by_cases hy : y ∈ s
    · simpa [Set.indicator_of_mem hy] using tsub_add_cancel_of_le hy.le
    · simp [Set.indicator_of_notMem hy]
  rw [← hadd, ENNReal.add_sub_cancel_right hν]

/-- On a countable measurable space with measurable singletons, the largest excess `μ A - ν A` over
measurable events equals the series of positive singleton differences `μ {y} - ν {y}`. No
finiteness assumption on `μ` or `ν` is needed. -/
theorem iSup_measure_sub_eq_tsum :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑' y, (μ {y} - ν {y}) := by
  classical
  refine le_antisymm (iSup₂_le fun A hA => ?_) ?_
  · rw [tsub_le_iff_right, ← μ.tsum_indicator_apply_singleton A hA,
      ← ν.tsum_indicator_apply_singleton A hA]
    calc
      ∑' y, A.indicator (fun y => μ {y}) y
        ≤ ∑' y, (A.indicator (fun y => μ {y} - ν {y}) y + A.indicator (fun y => ν {y}) y) :=
          tsum_le_tsum fun y => by
            by_cases hy : y ∈ A
            · simpa [Set.indicator_of_mem hy] using le_tsub_add
            · simp [Set.indicator_of_notMem hy]
      _ = (∑' y, A.indicator (fun y => μ {y} - ν {y}) y) +
            ∑' y, A.indicator (fun y => ν {y}) y := tsum_add
      _ ≤ (∑' y, (μ {y} - ν {y})) + ∑' y, A.indicator (fun y => ν {y}) y := by
          gcongr
          exact Set.indicator_le_self' (fun _ _ => zero_le) _
  · rw [tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    let t : Finset α := s.filter fun y => ν {y} < μ {y}
    have hsum : ∑ y ∈ s, (μ {y} - ν {y}) = ∑ y ∈ t, (μ {y} - ν {y}) := by
      rw [← Finset.sum_subset (Finset.filter_subset (fun y => ν {y} < μ {y}) s)]
      intro y hy hyt
      simp only [Finset.mem_filter, hy, true_and, not_lt] at hyt
      exact tsub_eq_zero_of_le hyt
    have hν_ne_top : ν ↑t ≠ ⊤ := by
      rw [← sum_measure_singleton]
      exact ENNReal.sum_ne_top.2 fun y hy => ((Finset.mem_filter.1 hy).2.trans_le le_top).ne
    have hadd : (∑ y ∈ t, (μ {y} - ν {y})) + ν ↑t = μ ↑t := by
      rw [← sum_measure_singleton, ← sum_measure_singleton, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun y hy => tsub_add_cancel_of_le (Finset.mem_filter.1 hy).2.le
    have hsub : ∑ y ∈ t, (μ {y} - ν {y}) = μ ↑t - ν ↑t := by
      rw [← hadd, ENNReal.add_sub_cancel_right hν_ne_top]
    rw [hsum, hsub]
    exact le_iSup₂_of_le (t : Set α) t.measurableSet le_rfl

/-- For a finite measure and a measure of the same total mass on a countable measurable space with
measurable singletons, Mathlib's extended total variation distance is twice the series of the
positive singleton differences `μ {y} - ν {y}`. -/
theorem etvDist_eq_two_mul_tsum_sub [IsFiniteMeasure μ] (h : μ Set.univ = ν Set.univ) :
    etvDist μ ν = 2 * ∑' y, (μ {y} - ν {y}) := by
  rw [etvDist_eq_two_mul_iSup_sub h, iSup_measure_sub_eq_tsum]

end MeasureTheory
