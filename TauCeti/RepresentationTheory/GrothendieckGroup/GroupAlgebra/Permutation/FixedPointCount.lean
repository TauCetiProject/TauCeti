/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FixedPointCount
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Permutation.Basic

/-!
# Permutation classes from fixed-point counts

Over a field of characteristic zero, finite sets acted on by a finite group have the same
permutation class when every group element fixes equally many points in both sets
(`TauCeti.permK0_eq_of_natCard_fixedBy_eq`). This transfers the representation equivalence supplied
by `TauCeti.nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq` to the exact Grothendieck
group, allowing identities between fixed-point counts to yield identities between module classes.
-/

public section

open MulAction

namespace TauCeti

universe u

variable (k : Type u) [Field k] [CharZero k] {G : Type u} [Group G] [Finite G]

/-- **Fixed-point counts determine permutation classes in characteristic zero.** Over a field of
characteristic zero, two finite `G`-sets on which every element has the same number of fixed
points have the same permutation class: their permutation representations are equivalent. -/
theorem permK0_eq_of_natCard_fixedBy_eq {X Y : Type u} [MulAction G X] [MulAction G Y]
    [Finite X] [Finite Y] (h : ∀ g : G, Nat.card (fixedBy X g) = Nat.card (fixedBy Y g)) :
    permK0 k G X = permK0 k G Y := by
  obtain ⟨e⟩ := (nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq k).mpr h
  rw [permK0_eq_of_equiv k X _ e, permK0_def]

end TauCeti
