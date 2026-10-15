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

* `MulEquiv.isKleinFour`: a group isomorphic to a Klein four-group is a Klein four-group.
-/

public section

namespace TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- A group isomorphic to a Klein four-group is a Klein four-group. -/
@[to_additive _root_.AddEquiv.isAddKleinFour
  /-- An additive group isomorphic to a Klein four-group is a Klein four-group. -/]
theorem _root_.MulEquiv.isKleinFour [IsKleinFour G] (e : G ≃* H) : IsKleinFour H :=
  ⟨by rw [← Nat.card_congr e.toEquiv, IsKleinFour.card_four],
    by rw [← Monoid.exponent_eq_of_mulEquiv e, IsKleinFour.exponent_two]⟩

end TauCeti
