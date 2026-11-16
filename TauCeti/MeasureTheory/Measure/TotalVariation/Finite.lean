/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Countable

/-!
# Eventwise excess and total variation on finite spaces

On a finite measurable space with measurable singletons, this file specializes the countable-space
series identities in `TauCeti.MeasureTheory.Measure.TotalVariation.Countable` to finite sums. The
largest excess `μ A - ν A` over measurable events reduces to the finite sum of the positive
singleton differences `μ {y} - ν {y}` (with truncated subtraction in `ℝ≥0∞`), and the event
`{y | ν {y} < μ {y}}` where `μ` strictly exceeds `ν` attains that supremum. Neither identity
requires finiteness of `μ` or `ν`: the set `{y | ν {y} < μ {y}}` is finite and each of its points
has finite `ν`-mass.

When `μ` is finite and `μ` and `ν` have equal total mass (in particular, for two probability
measures), Mathlib's extended total variation distance `etvDist μ ν` is twice the finite sum of
the positive singleton differences. This evaluates exact sampling and mixing discrepancies whenever
singleton masses are given by combinatorial fibre counts.

## Main declarations

* `MeasureTheory.measure_setOf_lt_sub_eq_sum`: the event `{y | ν {y} < μ {y}}` has excess equal to
  `∑ y, (μ {y} - ν {y})`.
* `MeasureTheory.iSup_measure_sub_eq_sum`: the largest excess `μ A - ν A` over measurable events is
  `∑ y, (μ {y} - ν {y})`.
* `MeasureTheory.etvDist_eq_two_mul_sum_sub`: for a finite measure and a measure of the same total
  mass, `etvDist μ ν = 2 * ∑ y, (μ {y} - ν {y})`.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, Proposition 4.2 and Remark 4.3, equation
  (4.5), p. 48.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ ν : Measure α}

/-- On a finite measurable space with measurable singletons, the event `{y | ν {y} < μ {y}}` has
excess equal to the sum of the positive singleton differences `μ {y} - ν {y}`, with truncated
subtraction in `ℝ≥0∞`. No finiteness assumption on `μ` or `ν` is needed. -/
theorem measure_setOf_lt_sub_eq_sum :
    μ {y | ν {y} < μ {y}} - ν {y | ν {y} < μ {y}} = ∑ y, (μ {y} - ν {y}) := by
  have hν : ν {y | ν {y} < μ {y}} ≠ ⊤ := by
    rw [← (Set.toFinite {y | ν {y} < μ {y}}).coe_toFinset, ← sum_measure_singleton]
    exact ENNReal.sum_ne_top.2 fun y hy =>
      (((Set.toFinite _).mem_toFinset.1 hy).trans_le le_top).ne
  rw [measure_setOf_lt_sub_eq_tsum hν, tsum_fintype]

/-- On a finite measurable space with measurable singletons, the largest excess `μ A - ν A` over
measurable events equals the sum of the positive singleton differences `μ {y} - ν {y}`, attained at
`{y | ν {y} < μ {y}}`. -/
theorem iSup_measure_sub_eq_sum :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑ y, (μ {y} - ν {y}) := by
  rw [iSup_measure_sub_eq_tsum, tsum_fintype]

/-- For a finite measure and a measure of the same total mass on a finite measurable space with
measurable singletons, Mathlib's extended total variation distance is twice the sum of the positive
singleton differences `μ {y} - ν {y}`. -/
theorem etvDist_eq_two_mul_sum_sub [IsFiniteMeasure μ] (h : μ Set.univ = ν Set.univ) :
    etvDist μ ν = 2 * ∑ y, (μ {y} - ν {y}) := by
  rw [etvDist_eq_two_mul_tsum_sub h, tsum_fintype]

end MeasureTheory
