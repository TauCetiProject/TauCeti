/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of partially monotone functions

This file gives a measurability criterion for functions between linearly ordered spaces that are
monotone on an open interval and constant away from its endpoints, such as quantile functions.
-/

public section

open Set

variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [LinearOrder α]
  [OrderTopology α] [SecondCountableTopology α] [TopologicalSpace β] [MeasurableSpace β]
  [OpensMeasurableSpace β] [LinearOrder β] [OrderClosedTopology β]

/-- A function that is monotone on an open interval and equal to a fixed constant strictly
outside the closed interval is measurable. No relation between the endpoints is required, and
the values at the endpoints are arbitrary. -/
theorem MonotoneOn.measurable_of_eq_const {f : β → α} {a b : β} {c : α}
    (hf : MonotoneOn f (Ioo a b)) (hconst : ∀ x, x < a ∨ b < x → f x = c) :
    Measurable f := by
  refine measurable_of_Iic fun x ↦ ?_
  obtain ⟨u, hu, hIoo⟩ := ordConnected_Iic.preimage_monotoneOn (s := Iic x) hf
  have hcover : f ⁻¹' Iic x = (Ioo a b ∩ u) ∪ (f ⁻¹' Iic x ∩ {a, b}) ∪
      ({_y | c ≤ x} ∩ (Iio a ∪ Ioi b)) := by
    rw [← hIoo]
    ext y
    grind [not_lt]
  rw [hcover]
  exact ((ordConnected_Ioo.inter hu).measurableSet.union
    ((toFinite _).subset inter_subset_right).measurableSet).union
    ((MeasurableSet.const _).inter (measurableSet_Iio.union measurableSet_Ioi))
