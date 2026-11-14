/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation distance and eventwise excess on countable spaces

For two finite measures on a countable space with measurable singletons, total variation
distance is the sum of the absolute differences of their singleton masses. We give the extended
and real formulas, together with summability of the real series. No probability normalization
is required, and the formulas also cover the empty space.

These identities identify total variation distance between distributions on a countable state
space with the ℓ¹ distance of their point masses. We use Mathlib's normalization: the distance
between probability measures is at most two, not one. The proof uses Mathlib's
`VectorMeasure.variation_apply_singleton` and the decomposition of a measure into its singleton
masses, rather than constructing a separate discrete distance.

We also compute the one-sided largest excess `⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A` in
`ℝ≥0∞` as the sum of the truncated singleton differences `μ {x} - ν {x}` (`iSup_measure_sub_eq_tsum`
on a countable space, `iSup_measure_sub_eq_sum` on a finite type). Neither formula requires the
measures to be finite. When `{x | ν {x} < μ {x}}` has finite `ν`-mass — in particular whenever `ν`
is finite or `α` is finite, since every point `x` with `ν {x} < μ {x}` already satisfies
`ν {x} < ∞` — that set attains the supremum (`measure_setOf_lt_sub_eq_tsum`,
`measure_setOf_lt_sub_eq_sum`).

## Main declarations

* `MeasureTheory.etvDist_eq_tsum_enorm_singleton`, `MeasureTheory.tvDist_eq_tsum_abs_singleton`:
  extended and real total variation distance as sums over singletons;
* `MeasureTheory.measure_setOf_lt_sub_eq_tsum_of_ne_top`,
  `MeasureTheory.measure_setOf_lt_sub_eq_tsum`, `MeasureTheory.measure_setOf_lt_sub_eq_sum`:
  attainment of the singleton-excess sum at `{x | ν {x} < μ {x}}`;
* `MeasureTheory.iSup_measure_sub_eq_tsum`, `MeasureTheory.iSup_measure_sub_eq_sum`:
  largest measurable-event excess as a series or finite sum of truncated singleton differences.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, Proposition 4.2 and Remark 4.3, p. 48.
-/

public section

open scoped ENNReal

namespace MeasureTheory

section Countable

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {μ ν : Measure α}

section Finite

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

end Finite

/-- On a countable space with measurable singletons, the excess of `μ` over `ν` on
`{x | ν {x} < μ {x}}` equals `∑' x, (μ {x} - ν {x})` whenever `ν` gives that set finite mass. -/
theorem measure_setOf_lt_sub_eq_tsum_of_ne_top (hν : ν {x | ν {x} < μ {x}} ≠ ∞) :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑' x, (μ {x} - ν {x}) := by
  set A : Set α := {x | ν {x} < μ {x}}
  have hadd : μ A = (∑' x, (μ {x} - ν {x})) + ν A := by
    rw [← μ.tsum_indicator_apply_singleton A .of_discrete,
      ← ν.tsum_indicator_apply_singleton A .of_discrete, ← tsum_add]
    refine tsum_congr fun x => ?_
    by_cases hx : ν {x} < μ {x}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, tsub_add_cancel_of_le hx.le]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
        tsub_eq_zero_of_le (not_lt.1 hx), add_zero]
  rw [hadd, ENNReal.add_sub_cancel_right hν]

/-- On a countable space with measurable singletons, when `ν` is finite, the excess of `μ` over
`ν` on `{x | ν {x} < μ {x}}` is the series of truncated singleton differences. -/
theorem measure_setOf_lt_sub_eq_tsum [IsFiniteMeasure ν] :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑' x, (μ {x} - ν {x}) :=
  measure_setOf_lt_sub_eq_tsum_of_ne_top (measure_ne_top _ _)

/-- On a countable space with measurable singletons, the largest excess `μ A - ν A` over
measurable events equals `∑' x, (μ {x} - ν {x})`. Neither measure need be finite. -/
theorem iSup_measure_sub_eq_tsum :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑' x, (μ {x} - ν {x}) := by
  classical
  refine le_antisymm (iSup₂_le fun A hA => tsub_le_iff_right.2 ?_) ?_
  · rw [← μ.tsum_indicator_apply_singleton A hA, ← ν.tsum_indicator_apply_singleton A hA,
      ← tsum_add]
    refine tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, le_tsub_add]
    · simp [hx]
  · rw [tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    set t : Finset α := s.filter fun x => ν {x} < μ {x}
    have htν : ν (t : Set α) ≠ ∞ := by
      rw [← sum_measure_singleton]
      exact (ENNReal.sum_lt_top.2 fun x hx => (Finset.mem_filter.1 hx).2.trans_le le_top).ne
    have htsub : μ (t : Set α) - ν (t : Set α) = ∑ x ∈ s, (μ {x} - ν {x}) := by
      have hadd : μ (t : Set α) = (∑ x ∈ s, (μ {x} - ν {x})) + ν (t : Set α) := by
        rw [← sum_measure_singleton, ← sum_measure_singleton,
          Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs with hx
        · exact (tsub_add_cancel_of_le hx.le).symm
        · simp [tsub_eq_zero_of_le (not_lt.1 hx)]
      rw [hadd, ENNReal.add_sub_cancel_right htν]
    exact htsub ▸ le_iSup₂ (f := fun (A : Set α) (_ : MeasurableSet A) => μ A - ν A)
      (t : Set α) t.measurableSet

end Countable

section Fintype

variable {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
  {μ ν : Measure α}

/-- On a finite type with measurable singletons, the excess of `μ` over `ν` on
`{x | ν {x} < μ {x}}` equals `∑ x, (μ {x} - ν {x})`. Neither measure need be finite: every point
of `{x | ν {x} < μ {x}}` automatically has finite `ν`-mass. -/
theorem measure_setOf_lt_sub_eq_sum :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑ x, (μ {x} - ν {x}) := by
  classical
  have hν : ν {x | ν {x} < μ {x}} ≠ ∞ := by
    have hset : {x : α | ν {x} < μ {x}} = ↑(Finset.univ.filter fun x => ν {x} < μ {x}) := by simp
    rw [hset, ← sum_measure_singleton]
    exact (ENNReal.sum_lt_top.2 fun x hx => (Finset.mem_filter.1 hx).2.trans_le le_top).ne
  rw [measure_setOf_lt_sub_eq_tsum_of_ne_top hν, tsum_fintype]

/-- On a finite type with measurable singletons, the largest excess `μ A - ν A` over measurable
events is `∑ x, (μ {x} - ν {x})`, attained at `{x | ν {x} < μ {x}}`
(`measure_setOf_lt_sub_eq_sum`). Neither measure need be finite. -/
theorem iSup_measure_sub_eq_sum :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑ x, (μ {x} - ν {x}) := by
  rw [iSup_measure_sub_eq_tsum, tsum_fintype]

end Fintype

end MeasureTheory
