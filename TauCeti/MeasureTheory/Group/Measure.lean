/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure

/-!
# Measures invariant under addition

This file records measure formulas for finite families of disjoint additive translates.

## Main results

* `TauCeti.measure_sub_mem`: a right-invariant measure is unchanged by translation.
* `TauCeti.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure equal to
  the number of translates times the measure of the original set.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- A translate of a set has the same measure under a right-invariant measure. -/
theorem measure_sub_mem (mu : Measure E) [mu.IsAddRightInvariant] (w : E) (F : Set E) :
    mu {y : E | y - w ∈ F} = mu F := by
  have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
  rw [h, measure_preimage_add_right]

/-- The union of finitely many pairwise disjoint translates of a measurable set has measure equal
to the number of translates times the measure of the set. -/
theorem measure_biUnion_sub_mem (mu : Measure E) [mu.IsAddRightInvariant]
    {G F : Set E} (hFm : MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by
  rw [measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
    fun w _ ↦ by
      have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
      rw [h]
      exact measurableSet_preimage (measurable_id.add_const (-w)) hFm]
  simp [measure_sub_mem]

end TauCeti
