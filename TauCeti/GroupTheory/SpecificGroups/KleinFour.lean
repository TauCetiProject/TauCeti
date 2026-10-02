/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Transporting the Klein four property along isomorphisms

Being a Klein four-group, that is having order four and exponent two, is invariant under group
isomorphism.

## Main results

* `TauCeti.IsKleinFour.of_mulEquiv`: a group isomorphic to a Klein four-group is a Klein
  four-group.
* `MulEquiv.isKleinFour_iff`: isomorphic groups are Klein four-groups together.
-/

public section

namespace TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- A group isomorphic to a Klein four-group is a Klein four-group. -/
@[to_additive IsAddKleinFour.of_addEquiv
  /-- An additive group isomorphic to a Klein four-group is a Klein four-group. -/]
theorem IsKleinFour.of_mulEquiv [IsKleinFour G] (e : G ≃* H) : IsKleinFour H :=
  ⟨by rw [← Nat.card_congr e.toEquiv, IsKleinFour.card_four],
    by rw [← Monoid.exponent_eq_of_mulEquiv e, IsKleinFour.exponent_two]⟩

end TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- Isomorphic groups are Klein four-groups together. -/
@[to_additive AddEquiv.isAddKleinFour_iff
  /-- Isomorphic additive groups are Klein four-groups together. -/]
theorem MulEquiv.isKleinFour_iff (e : G ≃* H) : IsKleinFour G ↔ IsKleinFour H :=
  ⟨fun _ ↦ TauCeti.IsKleinFour.of_mulEquiv e, fun _ ↦ TauCeti.IsKleinFour.of_mulEquiv e.symm⟩
