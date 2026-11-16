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
# Total variation distance and eventwise excess on countable and finite spaces

For two finite measures on a countable space with measurable singletons, total variation
distance is the sum of the absolute differences of their singleton masses. We give the extended
and real formulas, together with summability of the real series. No probability normalization
is required, and the formulas also cover the empty space.

We also express the largest one-sided eventwise excess `⨆ (A) (_ : MeasurableSet A), μ A - ν A`
as the sum of the truncated singleton differences `μ {x} - ν {x}` in `ℝ≥0∞`, over countable and
finite types without finiteness assumptions on either measure, and show that the event
`{x | ν {x} < μ {x}}` attains that sum whenever `ν` is finite (and unconditionally on a finite
type).

These identities identify total variation distance between distributions on a countable state
space with the ℓ¹ distance of their point masses, and one-sided excess with the positive-part
sum. For total variation distance we use Mathlib's normalization, under which the distance between
probability measures is at most two, whereas the one-sided excess between probability measures is
at most one.

## Main statements

* `MeasureTheory.measure_setOf_lt_sub_eq_tsum_singleton`: on any space with measurable singletons
  and finite `ν`, the excess on `{x | ν {x} < μ {x}}` equals `∑' x, (μ {x} - ν {x})`;
* `MeasureTheory.iSup_measure_sub_eq_tsum_singleton`: on a countable space with measurable
  singletons, the largest measurable-event excess equals `∑' x, (μ {x} - ν {x})`;
* `MeasureTheory.etvDist_eq_tsum_enorm_singleton`,
  `MeasureTheory.tvDist_eq_tsum_abs_singleton`: extended and real total variation distance as the
  ℓ¹ sum of singleton differences;
* `MeasureTheory.iSup_measure_sub_eq_sum_singleton`,
  `MeasureTheory.measure_setOf_lt_sub_eq_sum_singleton`: finite-type forms of the singleton-sum
  excess identity and its attainment at `{x | ν {x} < μ {x}}`.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, Proposition 4.2 and Remark 4.3, equation
  (4.5), p. 48.
-/

public section

open scoped ENNReal

namespace MeasureTheory

section SingletonClass

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

private theorem measure_coe_filter_lt_sub_eq_sum_singleton (μ ν : Measure α) (s : Finset α)
    [DecidablePred fun x => ν {x} < μ {x}] :
    μ (s.filter fun x => ν {x} < μ {x}) - ν (s.filter fun x => ν {x} < μ {x}) =
      ∑ x ∈ s, (μ {x} - ν {x}) := by
  rw [← sum_measure_singleton, ← sum_measure_singleton]
  have hne : ∑ x ∈ s with ν {x} < μ {x}, ν {x} ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun x hx => ((Finset.mem_filter.1 hx).2.trans_le le_top).ne
  have hsub : ∑ x ∈ s with ν {x} < μ {x}, (μ {x} - ν {x}) =
      (∑ x ∈ s with ν {x} < μ {x}, μ {x}) - ∑ x ∈ s with ν {x} < μ {x}, ν {x} :=
    ENNReal.eq_sub_of_add_eq hne <| by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x hx => tsub_add_cancel_of_le (Finset.mem_filter.1 hx).2.le
  rw [← hsub, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · rfl
  · exact (tsub_eq_zero_of_le (not_lt.1 h)).symm

/-- On a measurable space with measurable singletons, if `ν` is finite, the excess of `μ` over `ν`
on `{x | ν {x} < μ {x}}` equals the sum of the truncated singleton differences `μ {x} - ν {x}`. -/
theorem measure_setOf_lt_sub_eq_tsum_singleton (μ ν : Measure α) [IsFiniteMeasure ν] :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑' x, (μ {x} - ν {x}) := by
  set S : Set α := {x | ν {x} < μ {x}}
  have hsupp : Function.support (fun x => μ {x} - ν {x}) = S := by
    ext x
    simp [S, tsub_eq_zero_iff_le]
  by_cases hS : S.Countable
  · have hμS := tsum_measure_preimage_singleton (μ := μ) hS (f := id)
      fun x _ => measurableSet_singleton x
    have hνS := tsum_measure_preimage_singleton (μ := ν) hS (f := id)
      fun x _ => measurableSet_singleton x
    simp only [Set.preimage_id] at hμS hνS
    have hνtop : ∑' x : S, ν {x.1} ≠ ∞ := hνS.trans_lt (measure_lt_top ν S) |>.ne
    have htsum : ∑' x : S, (μ {x.1} - ν {x.1}) = ∑' x, (μ {x} - ν {x}) := by
      rw [tsum_subtype S fun x => μ {x} - ν {x}, ← hsupp, Set.indicator_support]
    rw [← hμS, ← hνS, ← htsum]
    symm
    refine ENNReal.eq_sub_of_add_eq hνtop ?_
    rw [← tsum_add]
    exact tsum_congr fun x => tsub_add_cancel_of_le x.2.le
  · have htsum : ∑' x, (μ {x} - ν {x}) = ∞ :=
      not_ne_iff.1 fun h => hS (hsupp ▸ Summable.countable_support_ennreal h)
    have hS' : ¬ (Set.univ : Set S).Countable := fun hc =>
      hS ((Set.countable_univ_iff.1 hc).to_set)
    have hsuppμ : Function.support (fun x : S => μ {x.1}) = Set.univ :=
      Set.eq_univ_of_forall fun x => by
        have hx : ν {x.1} < μ {x.1} := x.2
        exact (zero_le.trans_lt hx).ne'
    have hμtop' : ∑' x : S, μ {x.1} = ∞ :=
      not_ne_iff.1 fun h => hS' (hsuppμ ▸ Summable.countable_support_ennreal h)
    have hμS : μ S = ∞ := top_unique <| by
      rw [← hμtop', tsum_eq_iSup_sum]
      refine iSup_le fun t => ?_
      have ht : ∑ x ∈ t, μ {x.1} = μ (t.map ⟨Subtype.val, Subtype.val_injective⟩) := by
        rw [← sum_measure_singleton, Finset.sum_map]
        rfl
      exact ht.trans_le (measure_mono fun y hy => by
        obtain ⟨x, _, rfl⟩ := Finset.mem_map.1 hy
        exact x.2)
    rw [hμS, htsum, ENNReal.top_sub (measure_ne_top ν S)]

end SingletonClass

section Countable

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- On a countable space with measurable singletons, the largest excess `μ A - ν A` over measurable
events equals the sum of the truncated singleton differences `μ {x} - ν {x}`. No finiteness
assumption on either measure is required. -/
theorem iSup_measure_sub_eq_tsum_singleton (μ ν : Measure α) :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑' x, (μ {x} - ν {x}) := by
  classical
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    rw [← μ.tsum_indicator_apply_singleton A hA, ← ν.tsum_indicator_apply_singleton A hA,
      tsub_le_iff_right, ← tsum_add]
    refine tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, le_tsub_add]
    · simp [Set.indicator_of_notMem hx]
  · rw [tsum_eq_iSup_sum]
    exact iSup_le fun s => (measure_coe_filter_lt_sub_eq_sum_singleton μ ν s).symm.trans_le <|
      le_iSup₂ (f := fun (A : Set α) (_ : MeasurableSet A) => μ A - ν A)
        (s.filter fun x => ν {x} < μ {x}) (Finset.measurableSet _)

variable {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

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

end Countable

section Fintype

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- On a finite type with measurable singletons, the largest excess `μ A - ν A` over measurable
events is the finite sum of the truncated singleton differences `μ {x} - ν {x}`. -/
theorem iSup_measure_sub_eq_sum_singleton (μ ν : Measure α) :
    (⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A) = ∑ x, (μ {x} - ν {x}) := by
  rw [iSup_measure_sub_eq_tsum_singleton, tsum_fintype]

/-- On a finite type with measurable singletons, the event `{x | ν {x} < μ {x}}` attains the sum of
the truncated singleton differences `μ {x} - ν {x}` (and hence, by
`iSup_measure_sub_eq_sum_singleton`, the largest measurable-event excess), without finiteness
assumptions on either measure. -/
theorem measure_setOf_lt_sub_eq_sum_singleton (μ ν : Measure α) :
    μ {x | ν {x} < μ {x}} - ν {x | ν {x} < μ {x}} = ∑ x, (μ {x} - ν {x}) := by
  classical
  have hset : ((Finset.univ.filter fun x : α => ν {x} < μ {x} : Finset α) : Set α) =
      {x | ν {x} < μ {x}} := by
    ext x
    simp
  rw [← hset, measure_coe_filter_lt_sub_eq_sum_singleton]

end Fintype

end MeasureTheory
