/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Eventwise excess and total variation on finite spaces

On a finite measurable space with measurable singletons, every event is a finite union of
singletons, so the largest excess `μ A - ν A` over measurable events reduces to the finite sum of
the positive singleton differences `μ {y} - ν {y}` (with truncated subtraction in `ℝ≥0∞`). The
event `{y | ν {y} < μ {y}}` where `μ` strictly exceeds `ν` attains that supremum. Neither identity
requires finiteness of `μ` or `ν`: at each point of `{y | ν {y} < μ {y}}`, the smaller singleton
mass `ν {y}` is automatically finite.

When `μ` is finite and `μ` and `ν` have equal total mass (in particular, for two probability
measures), combining this identity with `MeasureTheory.etvDist_eq_two_mul_iSup_sub` expresses
Mathlib's extended total variation distance `etvDist μ ν` as twice the sum of the positive
singleton differences. This evaluates exact sampling and mixing discrepancies whenever singleton
masses are given by combinatorial fibre counts.

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
  classical
  let s : Finset α := Finset.univ.filter fun y => ν {y} < μ {y}
  have hs : ({y : α | ν {y} < μ {y}} : Set α) = ↑s := by
    ext y
    simp [s]
  have hsum : ∑ y, (μ {y} - ν {y}) = ∑ y ∈ s, (μ {y} - ν {y}) := by
    rw [← Finset.sum_subset (Finset.subset_univ s)]
    intro y _ hy
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hy
    exact tsub_eq_zero_of_le hy
  have hν_ne_top : ν ↑s ≠ ⊤ := by
    rw [← sum_measure_singleton]
    exact ENNReal.sum_ne_top.2 fun y hy =>
      ((Finset.mem_filter.1 hy).2.trans_le le_top).ne
  have hadd : (∑ y ∈ s, (μ {y} - ν {y})) + ν ↑s = μ ↑s := by
    rw [← sum_measure_singleton, ← sum_measure_singleton, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y hy => tsub_add_cancel_of_le (Finset.mem_filter.1 hy).2.le
  rw [hs, hsum, ← hadd, ENNReal.add_sub_cancel_right hν_ne_top]

/-- On a finite measurable space with measurable singletons, the largest excess `μ A - ν A` over
measurable events equals the sum of the positive singleton differences `μ {y} - ν {y}`, attained at
`{y | ν {y} < μ {y}}`. -/
theorem iSup_measure_sub_eq_sum :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑ y, (μ {y} - ν {y}) := by
  classical
  refine le_antisymm (iSup₂_le fun A _ => ?_) ?_
  · rw [tsub_le_iff_right]
    let t : Finset α := A.toFinite.toFinset
    have ht : (t : Set α) = A := A.toFinite.coe_toFinset
    rw [← ht, ← sum_measure_singleton, ← sum_measure_singleton]
    calc
      ∑ y ∈ t, μ {y} ≤ ∑ y ∈ t, (μ {y} - ν {y} + ν {y}) :=
        Finset.sum_le_sum fun _ _ => le_tsub_add
      _ = (∑ y ∈ t, (μ {y} - ν {y})) + ∑ y ∈ t, ν {y} := Finset.sum_add_distrib
      _ ≤ (∑ y, (μ {y} - ν {y})) + ∑ y ∈ t, ν {y} :=
        add_le_add_left (Finset.sum_le_univ_sum_of_nonneg fun _ => zero_le) _
  · rw [← measure_setOf_lt_sub_eq_sum]
    exact le_iSup₂_of_le {y | ν {y} < μ {y}} (Set.toFinite _).measurableSet le_rfl

/-- For a finite measure and a measure of the same total mass on a finite measurable space with
measurable singletons, Mathlib's extended total variation distance is twice the sum of the positive
singleton differences `μ {y} - ν {y}`. -/
theorem etvDist_eq_two_mul_sum_sub [IsFiniteMeasure μ] (h : μ Set.univ = ν Set.univ) :
    etvDist μ ν = 2 * ∑ y, (μ {y} - ν {y}) := by
  rw [etvDist_eq_two_mul_iSup_sub h, iSup_measure_sub_eq_sum]

end MeasureTheory
