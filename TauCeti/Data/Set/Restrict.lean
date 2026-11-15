/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Restrict

/-!
# Preimages under a map restricted to a preimage

The preimage of a set `u ⊆ t` under `Set.restrictPreimage t f` has the same cardinality as the
preimage of `u` under `f`, and is finite exactly when that preimage is; in particular this holds
for the fibres over points of `t`. Dually, removing the preimage of a set from the domain does not
change the fibres over points outside that set.
-/

public section

namespace Set

variable {α β : Type*} (t : Set β) {f : α → β}

/-- Restricting a map to the preimage of `t` does not change the cardinality of the preimage of
a subset of `t`. -/
@[simp] theorem ncard_preimage_restrictPreimage {u : Set t} :
    (t.restrictPreimage f ⁻¹' u).ncard = (f ⁻¹' (Subtype.val '' u)).ncard := by
  rw [← image_val_preimage_restrictPreimage, ncard_image_of_injective _ Subtype.val_injective]

/-- Restricting a map to the preimage of `t` does not change whether the preimage of a subset of
`t` is finite. -/
@[simp] theorem finite_preimage_restrictPreimage_iff {u : Set t} :
    (t.restrictPreimage f ⁻¹' u).Finite ↔ (f ⁻¹' (Subtype.val '' u)).Finite := by
  rw [← image_val_preimage_restrictPreimage, finite_image_iff Subtype.val_injective.injOn]

variable (f) in
/-- Removing the preimage of a set `Z` from a set `T` does not change the cardinality of the part
of `T` in a fiber over a point outside `Z`. -/
theorem natCard_fiber_sdiff_preimage {T : Set α} {Z : Set β} {y : β} (hy : y ∉ Z) :
    Nat.card {x // f x = y ∧ x ∈ T \ f ⁻¹' Z} = Nat.card {x // f x = y ∧ x ∈ T} :=
  Nat.card_congr <| Equiv.subtypeEquivRight fun x ↦ by grind

end Set
