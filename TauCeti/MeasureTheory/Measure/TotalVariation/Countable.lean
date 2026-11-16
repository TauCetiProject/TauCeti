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
# Total variation distance and excess on countable spaces

For two finite measures on a countable space with measurable singletons, total variation
distance is the sum of the absolute differences of their singleton masses. We give the extended
and real formulas, together with summability of the real series. No probability normalization
is required, and the formulas also cover the empty space.

We also express the largest eventwise excess `⨆ (A) (_ : MeasurableSet A), μ A - ν A` as the sum
`∑' x, (μ {x} - ν {x})` of truncated singleton differences in `ℝ≥0∞` (with no finiteness
assumption), its finite-type sum form, and its attainment at `{x | ν {x} < μ {x}}` whenever `ν` is
finite.

These identities identify total variation distance between distributions on a countable state
space with the ℓ¹ distance of their point masses. We use Mathlib's normalization: the distance
between probability measures is at most two, not one.

## Main declarations

* `MeasureTheory.etvDist_eq_tsum_enorm_singleton`, `MeasureTheory.tvDist_eq_tsum_abs_singleton`:
  total variation distance as the ℓ¹ distance of singleton masses;
* `MeasureTheory.summable_abs_measureReal_singleton_sub`: summability of singleton mass
  differences;
* `MeasureTheory.iSup_measure_sub_eq_tsum_singleton`,
  `MeasureTheory.iSup_measure_sub_eq_sum_singleton`: largest eventwise excess as the sum of
  truncated singleton differences;
* `MeasureTheory.iSup_measure_sub_eq_sub_setOf_lt`: attainment of the largest excess on
  `{x | ν {x} < μ {x}}` for finite `ν`.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  2nd ed., American Mathematical Society, 2017, Proposition 4.2 and Remark 4.3, p. 48.
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

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- On a countable space with measurable singletons, the largest eventwise excess `μ A - ν A`
equals the sum of the truncated singleton differences `μ {x} - ν {x}`. No finiteness assumption
is required. -/
theorem iSup_measure_sub_eq_tsum_singleton [Countable α] (μ ν : Measure α) :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑' x, (μ {x} - ν {x}) := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA => tsub_le_iff_left.2 ?_
    calc
      μ A = ∑' x, A.indicator (fun x => μ {x}) x :=
        (μ.tsum_indicator_apply_singleton A hA).symm
      _ ≤ ∑' x, A.indicator (fun x => ν {x} + (μ {x} - ν {x})) x := by
        refine tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ A <;> simp [hx, le_add_tsub]
      _ = (∑' x, A.indicator (fun x => ν {x}) x) +
            ∑' x, A.indicator (fun x => μ {x} - ν {x}) x := by
        rw [← tsum_add]
        congr 1 with x
        by_cases hx : x ∈ A <;> simp [hx]
      _ ≤ ν A + ∑' x, (μ {x} - ν {x}) := by
        rw [ν.tsum_indicator_apply_singleton A hA]
        gcongr with x
        by_cases hx : x ∈ A <;> simp [hx]
  · rw [tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    classical
    let t : Finset α := s.filter fun x => ν {x} < μ {x}
    have hsum : ∑ x ∈ s, (μ {x} - ν {x}) = ∑ x ∈ t, (μ {x} - ν {x}) := by
      refine (Finset.sum_subset (Finset.filter_subset _ s) fun x hx hxt => ?_).symm
      have hle : μ {x} ≤ ν {x} := not_lt.1 fun hlt => hxt (Finset.mem_filter.2 ⟨hx, hlt⟩)
      exact tsub_eq_zero_of_le hle
    have hν : ν (t : Set α) ≠ ∞ := by
      rw [← sum_measure_singleton]
      exact ENNReal.sum_ne_top.2 fun x hx => ne_top_of_lt (Finset.mem_filter.1 hx).2
    have hadd : ν (t : Set α) + ∑ x ∈ t, (μ {x} - ν {x}) = μ (t : Set α) := by
      rw [← sum_measure_singleton, ← sum_measure_singleton, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x hx =>
        add_tsub_cancel_of_le (Finset.mem_filter.1 hx).2.le
    rw [hsum, ← ENNReal.add_sub_cancel_left (b := ∑ x ∈ t, (μ {x} - ν {x})) hν, hadd]
    exact le_iSup₂ (f := fun (A : Set α) (_ : MeasurableSet A) => μ A - ν A)
      (t : Set α) t.measurableSet

/-- On a finite type with measurable singletons, the largest eventwise excess `μ A - ν A`
equals the finite sum of the truncated singleton differences `μ {x} - ν {x}`. -/
theorem iSup_measure_sub_eq_sum_singleton [Fintype α] (μ ν : Measure α) :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑ x, (μ {x} - ν {x}) := by
  rw [iSup_measure_sub_eq_tsum_singleton, tsum_fintype]

/-- On a countable space with measurable singletons, when `ν` is finite the largest eventwise
excess of `μ` over `ν` is attained on `{x | ν {x} < μ {x}}`. -/
theorem iSup_measure_sub_eq_sub_setOf_lt [Countable α] (μ ν : Measure α) [IsFiniteMeasure ν] :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) =
      μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} := by
  let P : Set α := {x | ν {x} < μ {x}}
  have hP : MeasurableSet P := (Set.to_countable P).measurableSet
  have hadd : ν P + ∑' x, (μ {x} - ν {x}) = μ P := by
    rw [← ν.tsum_indicator_apply_singleton P hP, ← μ.tsum_indicator_apply_singleton P hP,
      ← tsum_add]
    congr 1 with x
    by_cases hx : ν {x} < μ {x}
    · simp [P, hx, add_tsub_cancel_of_le hx.le]
    · simp [P, hx, tsub_eq_zero_of_le (not_lt.1 hx)]
  rw [iSup_measure_sub_eq_tsum_singleton, ← hadd, ENNReal.add_sub_cancel_left (measure_ne_top ν P)]

end Excess

end MeasureTheory
