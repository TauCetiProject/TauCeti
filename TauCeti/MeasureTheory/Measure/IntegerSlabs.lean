/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Measures of integer slabs

The measure of a null-measurable set is the sum of its measures in the integer slabs of
a measurable real-valued function (`TauCeti.measure_eq_tsum_inter_preimage_Ico`).
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

end TauCeti
