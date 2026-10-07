/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Restrict

/-!
# Fibers of a map restricted to a preimage

The fiber of `Set.restrictPreimage` over a point has the same cardinality as the corresponding
fiber of the original map. Dually, removing the preimage of a set from the domain does not change
the fibers over points outside that set.
-/

public section

namespace TauCeti

open Set

variable {α β : Type*} (f : α → β) (t : Set β)

/-- Restricting a map to the preimage of a set does not change the cardinality of a fiber
over a point of that set. -/
@[simp] theorem ncard_fiber_restrictPreimage (w : t) :
    ((t.restrictPreimage f) ⁻¹' {w}).ncard = (f ⁻¹' {w.val}).ncard := by
  calc
    _ = ((Subtype.val : (f ⁻¹' t) → α) '' ((t.restrictPreimage f) ⁻¹' {w})).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = _ := by rw [image_val_preimage_restrictPreimage, image_singleton]

/-- Removing the preimage of a set `Z` from a set `T` does not change the cardinality of the part
of `T` in a fiber over a point outside `Z`. -/
theorem natCard_fiber_sdiff_preimage {T : Set α} {Z : Set β} {y : β} (hy : y ∉ Z) :
    Nat.card {x // f x = y ∧ x ∈ T \ f ⁻¹' Z} = Nat.card {x // f x = y ∧ x ∈ T} :=
  Nat.card_congr <| Equiv.subtypeEquivRight fun x ↦ by
    simp only [mem_sdiff, mem_preimage]
    exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, h.1 ▸ hy⟩⟩

end TauCeti
