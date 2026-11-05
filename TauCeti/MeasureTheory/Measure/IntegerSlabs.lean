/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Measures of integer slabs and level strips

The measure of a null-measurable set is the sum of its measures in the integer slabs of
a measurable real-valued function (`TauCeti.measure_eq_tsum_inter_preimage_Ico`), and the strips
between consecutive levels of a monotone sequence have total measure at most the total mass
(`TauCeti.sum_measureReal_lt_lt_le_measureReal_univ`).
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- The measure of `T` is the sum of the measures of its slices `m ≤ f x < m + 1`, for
`m ∈ ℤ`. -/
theorem measure_eq_tsum_inter_preimage_Ico {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Measurable f) {T : Set α} (hT : NullMeasurableSet T μ) :
    μ T = ∑' m : ℤ, μ (T ∩ f ⁻¹' Ico (m : ℝ) (m + 1)) := by
  rw [← measure_iUnion₀, ← inter_iUnion, ← preimage_iUnion, iUnion_Ico_intCast ℝ, preimage_univ,
    inter_univ]
  · exact fun m m' h ↦ ((pairwise_disjoint_Ico_intCast ℝ h).preimage f).aedisjoint.mono
      inter_subset_right inter_subset_right
  · exact fun m ↦ hT.inter ((hf measurableSet_Ico).nullMeasurableSet)

/-- The strips `{lev j < f < lev (j + 1)}` of a monotone sequence of levels of a measurable
function are pairwise disjoint, so their measures sum to at most the total mass. -/
theorem sum_measureReal_lt_lt_le_measureReal_univ {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f) {lev : ℕ → ℝ} (hlev : Monotone lev)
    (J : ℕ) :
    ∑ j ∈ Finset.range J, μ.real {x | lev j < f x ∧ f x < lev (j + 1)} ≤ μ.real univ := by
  refine sum_measureReal_le_measureReal_univ (fun j _ =>
    (measurableSet_lt measurable_const hf).inter (measurableSet_lt hf measurable_const)) ?_
  intro i _ j _ hij
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · linarith [hlev (by omega : i + 1 ≤ j)]
  · linarith [hlev (by omega : j + 1 ≤ i)]

end TauCeti
