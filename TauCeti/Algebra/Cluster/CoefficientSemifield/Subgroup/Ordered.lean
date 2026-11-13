/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.CoefficientSemifield.Subgroup.Basic
public import Mathlib.Algebra.Ring.Subring.Units
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Positive units as a coefficient semifield

In a linearly ordered semifield, positive units are closed under addition. They
therefore form a coefficient semifield with the ambient addition, and their
zero-adjoined realization consists exactly of the nonnegative elements.
-/

public section

namespace Units

variable {F : Type*} [Semifield F] [LinearOrder F] [IsStrictOrderedRing F]

/-- Positive units are closed under addition in a linearly ordered semifield. -/
instance isAddClosed_posSubgroup : (posSubgroup F).IsAddClosed where
  exists_add a b := by
    have h : 0 < ((a : Fˣ) : F) + ((b : Fˣ) : F) := add_pos a.property b.property
    exact ⟨⟨Units.mk0 _ h.ne', h⟩, rfl⟩

/-- Adjoining zero to the positive units gives precisely the nonnegative elements. -/
@[simp↓]
theorem mem_withZeroSubsemiring_posSubgroup (a : F) :
    a ∈ (posSubgroup F).withZeroSubsemiring ↔ 0 ≤ a := by
  rw [Subgroup.mem_withZeroSubsemiring]
  constructor
  · rintro (rfl | ⟨b, rfl⟩)
    · exact le_rfl
    · exact le_of_lt b.property
  · intro ha
    obtain rfl | h := eq_or_lt_of_le ha
    · exact Or.inl rfl
    · exact Or.inr ⟨⟨Units.mk0 a h.ne', h⟩, rfl⟩

end Units
