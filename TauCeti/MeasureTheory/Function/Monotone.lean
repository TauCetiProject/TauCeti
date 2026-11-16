/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of partially monotone functions

This file gives measurability criteria for partially monotone functions between linearly ordered
spaces: functions that are monotone on an open interval and constant away from its endpoints (such
as quantile functions), and compositions `x ↦ g (f x)` where `g` is monotone on a set containing the
values of a measurable map `f`.
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

/-- Composing a function that is monotone on `t` with a measurable function taking values in `t`
produces a measurable function. No measurability or order-connectedness assumption on `t` is
needed. -/
theorem MonotoneOn.measurable_comp {γ : Type*} [MeasurableSpace γ] {g : β → α} {t : Set β}
    (hg : MonotoneOn g t) {f : γ → β} (hf : Measurable f) (hft : ∀ x, f x ∈ t) :
    Measurable fun x ↦ g (f x) := by
  refine measurable_of_Iic fun a ↦ ?_
  obtain ⟨u, hu, htu⟩ := ordConnected_Iic.preimage_monotoneOn (s := Iic a) hg
  have hpre : (fun x ↦ g (f x)) ⁻¹' Iic a = f ⁻¹' u := by
    ext x
    have hmem : f x ∈ t ∩ g ⁻¹' Iic a ↔ f x ∈ t ∩ u := by rw [htu]
    simpa [hft x] using hmem
  exact hpre ▸ hf hu.measurableSet
