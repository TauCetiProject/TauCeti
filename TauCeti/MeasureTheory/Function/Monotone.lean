/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of partially monotone functions

This file gives a measurability criterion for real functions that are monotone on an open
interval and constant away from its endpoints.
-/

public section

open Set

namespace TauCeti

/-- A real function that is monotone on an open interval and equal to a fixed constant strictly
outside the closed interval is measurable. No relation between the endpoints is required. -/
theorem measurable_of_monotoneOn_Ioo_of_eq_const {f : ℝ → ℝ} {a b c : ℝ}
    (hf : MonotoneOn f (Ioo a b)) (hconst : ∀ x : ℝ, x < a ∨ b < x → f x = c) :
    Measurable f := by
  refine measurable_of_Iic fun x ↦ ?_
  have hcover : f ⁻¹' Iic x = (f ⁻¹' Iic x ∩ Ioo a b) ∪ (f ⁻¹' Iic x ∩ {a, b}) ∪
      (f ⁻¹' Iic x ∩ (Iio a ∪ Ioi b)) := by
    rw [← inter_union_distrib_left, ← inter_union_distrib_left, left_eq_inter]
    intro y _
    simp only [mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff, mem_Iio, mem_Ioi]
    grind
  have hconn : (f ⁻¹' Iic x ∩ Ioo a b).OrdConnected := by
    refine ⟨fun y hy z hz w hw ↦ ?_⟩
    have hw' : w ∈ Ioo a b := ⟨hy.2.1.trans_le hw.1, hw.2.trans_lt hz.2.2⟩
    exact ⟨(hf hw' hz.2 hw.2).trans hz.1, hw'⟩
  have hjunk : MeasurableSet (f ⁻¹' Iic x ∩ (Iio a ∪ Ioi b)) := by
    by_cases hx : c ≤ x
    · rw [inter_eq_right.mpr fun y hy ↦ by simpa [hconst y hy] using hx]
      exact measurableSet_Iio.union measurableSet_Ioi
    · rw [eq_empty_of_forall_notMem (s := f ⁻¹' Iic x ∩ (Iio a ∪ Ioi b)) fun y hy ↦
        hx (by simpa [hconst y hy.2] using hy.1)]
      exact MeasurableSet.empty
  rw [hcover]
  exact (hconn.measurableSet.union ((toFinite _).subset inter_subset_right).measurableSet).union
    hjunk

end TauCeti
