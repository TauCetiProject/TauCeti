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
# Total variation distance and event excess on countable spaces

For two finite measures on a countable space with measurable singletons, total variation
distance is the sum of the absolute differences of their singleton masses. We give the extended
and real formulas, together with summability of the real series. No probability normalization
is required, and the formulas also cover the empty space.

Without any finiteness assumption on either measure, the supremum of measurable-event excesses
`⨆ A, μ A - ν A` on a countable space with measurable singletons equals the sum of the truncated
singleton differences `∑' x, (μ {x} - ν {x})`, and the positive set `{x | ν {x} < μ {x}}` attains
it whenever `ν` gives that set finite mass — in particular unconditionally on any `Fintype`.

These identities identify total variation distance between distributions on a countable state
space with the ℓ¹ distance of their point masses, and event excess with the sum of positive parts
of singleton differences. We use Mathlib's normalization: the total variation distance between
probability measures is at most two, not one.

## Main statements

* `MeasureTheory.etvDist_eq_tsum_enorm_singleton`, `MeasureTheory.tvDist_eq_tsum_abs_singleton`:
  extended and real total variation distances as singleton series;
* `MeasureTheory.iSup_measure_sub_eq_tsum_singleton`,
  `MeasureTheory.measure_setOf_lt_sub_eq_tsum_singleton`: event excess on countable spaces and
  its attainment on `{x | ν {x} < μ {x}}`;
* `MeasureTheory.iSup_measure_sub_eq_sum_singleton`,
  `MeasureTheory.measure_setOf_lt_sub_eq_sum_singleton`: the corresponding finite sums on finite
  types;
* `MeasureTheory.etvDist_eq_two_mul_tsum_singleton`,
  `MeasureTheory.etvDist_eq_two_mul_sum_singleton`: for a finite measure and a measure of the same
  total mass, extended total variation distance is twice the sum of the truncated singleton
  differences.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, Proposition 4.2 and Remark 4.3, p. 48.
-/

public section

open scoped ENNReal

namespace MeasureTheory

section TotalVariation

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

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

end TotalVariation

section Excess

variable {α : Type*} [MeasurableSpace α]

/-- A finite set of points where `ν {x} < μ {x}` has finite `ν`-mass. -/
private theorem measure_coe_finset_ne_top_of_forall_lt [MeasurableSingletonClass α]
    {μ ν : Measure α} {s : Finset α} (hs : ∀ x ∈ s, ν {x} < μ {x}) : ν (s : Set α) ≠ ∞ := by
  rw [← sum_measure_singleton]
  exact (ENNReal.sum_lt_top.2 fun x hx => (hs x hx).trans_le le_top).ne

section Countable

variable [Countable α] [MeasurableSingletonClass α] {μ ν : Measure α}

/-- On a countable space with measurable singletons, if `ν {x} ≤ μ {x}` on `S` and `ν S ≠ ∞`,
then `μ S - ν S` equals the sum of `μ {x} - ν {x}` over `S`. -/
private theorem measure_sub_eq_tsum_indicator_singleton {S : Set α}
    (hν : ν S ≠ ∞) (hle : ∀ x ∈ S, ν {x} ≤ μ {x}) :
    μ S - ν S = ∑' x, S.indicator (fun y => μ {y} - ν {y}) x := by
  have hsum : μ S = ν S + ∑' x, S.indicator (fun y => μ {y} - ν {y}) x := by
    rw [← μ.tsum_indicator_apply_singleton S .of_discrete,
      ← ν.tsum_indicator_apply_singleton S .of_discrete, ← tsum_add]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
      exact (add_tsub_cancel_of_le (hle x hx)).symm
    · simp [Set.indicator_of_notMem hx]
  rw [hsum, ENNReal.add_sub_cancel_left hν]

/-- On a countable space with measurable singletons, the positive set `{x | ν {x} < μ {x}}`
attains the sum of the truncated singleton differences `μ {x} - ν {x}` whenever `ν` gives that
set finite mass (for instance when `ν` is finite or `α` is finite). Without `hν` the left-hand
side can vanish as `∞ - ∞` while the right-hand side is `∞` (e.g. `μ = 2 • .count` and
`ν = .count` on `ℕ`). -/
theorem measure_setOf_lt_sub_eq_tsum_singleton (hν : ν {x | ν {x} < μ {x}} ≠ ∞) :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑' x, (μ {x} - ν {x}) := by
  rw [measure_sub_eq_tsum_indicator_singleton hν fun _ hx => hx.le]
  refine tsum_congr fun x => ?_
  by_cases hx : ν {x} < μ {x}
  · exact Set.indicator_of_mem hx _
  · rw [Set.indicator_of_notMem hx, tsub_eq_zero_of_le (not_lt.1 hx)]

/-- On a countable space with measurable singletons, the supremum of `μ A - ν A` over
measurable events is the sum of the truncated singleton differences `μ {x} - ν {x}`. No
finiteness hypothesis on `μ` or `ν` is required. -/
theorem iSup_measure_sub_eq_tsum_singleton :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑' x, (μ {x} - ν {x}) := by
  classical
  refine le_antisymm (iSup₂_le fun A hA => tsub_le_iff_left.2 ?_) ?_
  · rw [← μ.tsum_indicator_apply_singleton A hA, ← ν.tsum_indicator_apply_singleton A hA,
      ← tsum_add]
    refine tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx, le_add_tsub]
    · simp [Set.indicator_of_notMem hx]
  · rw [tsum_eq_iSup_sum]
    refine iSup_le fun t => ?_
    let B : Finset α := t.filter fun x => ν {x} < μ {x}
    have hB : ∀ x ∈ B, ν {x} < μ {x} := fun _ hx => (Finset.mem_filter.1 hx).2
    have hsum : ∑ x ∈ t, (μ {x} - ν {x}) = μ (B : Set α) - ν (B : Set α) := by
      rw [← Finset.sum_filter_of_ne (p := fun x => ν {x} < μ {x}) fun x _ hne =>
          not_le.1 fun hle => hne (tsub_eq_zero_of_le hle),
        sum_eq_tsum_indicator,
        measure_sub_eq_tsum_indicator_singleton (measure_coe_finset_ne_top_of_forall_lt hB)
          fun x hx => (hB x hx).le]
    rw [hsum]
    exact le_iSup₂ (f := fun (A : Set α) (_ : MeasurableSet A) => μ A - ν A)
      (B : Set α) .of_discrete

/-- On a countable space with measurable singletons, for a finite measure `μ` and a measure `ν` of
the same total mass (e.g. two probability measures), extended total variation distance is twice the
sum of the truncated singleton differences `μ {x} - ν {x}`. -/
theorem etvDist_eq_two_mul_tsum_singleton [IsFiniteMeasure μ] (h : μ Set.univ = ν Set.univ) :
    etvDist μ ν = 2 * ∑' x, (μ {x} - ν {x}) := by
  rw [etvDist_eq_two_mul_iSup_sub h, iSup_measure_sub_eq_tsum_singleton]

end Countable

section Fintype

variable [Fintype α] [MeasurableSingletonClass α] {μ ν : Measure α}

/-- On a finite type with measurable singletons, the positive set `{x | ν {x} < μ {x}}` attains
the sum of the truncated singleton differences `μ {x} - ν {x}`. No finiteness hypothesis on `μ`
or `ν` is required, since `ν` is finite at every point where `ν {x} < μ {x}`. -/
theorem measure_setOf_lt_sub_eq_sum_singleton :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑ x, (μ {x} - ν {x}) := by
  classical
  have hν : ν {x | ν {x} < μ {x}} ≠ ∞ := by
    rw [← Finset.coe_filter_univ]
    exact measure_coe_finset_ne_top_of_forall_lt fun _ hx => (Finset.mem_filter.1 hx).2
  rw [measure_setOf_lt_sub_eq_tsum_singleton hν, tsum_fintype]

/-- On a finite type with measurable singletons, the largest excess `μ A - ν A` over measurable
events is `∑ x, (μ {x} - ν {x})`. For probability measures this is the finite-space excess
identity of Levin–Peres–Wilmer, Proposition 4.2 and Remark 4.3; here no finiteness or
normalization hypothesis is needed. -/
theorem iSup_measure_sub_eq_sum_singleton :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑ x, (μ {x} - ν {x}) := by
  rw [iSup_measure_sub_eq_tsum_singleton, tsum_fintype]

/-- On a finite type with measurable singletons, for a finite measure `μ` and a measure `ν` of the
same total mass (e.g. two probability measures), extended total variation distance is twice the
sum of the truncated singleton differences `μ {x} - ν {x}`; see Levin–Peres–Wilmer,
Proposition 4.2 and Remark 4.3. -/
theorem etvDist_eq_two_mul_sum_singleton [IsFiniteMeasure μ] (h : μ Set.univ = ν Set.univ) :
    etvDist μ ν = 2 * ∑ x, (μ {x} - ν {x}) := by
  rw [etvDist_eq_two_mul_tsum_singleton h, tsum_fintype]

end Fintype

end Excess

end MeasureTheory
