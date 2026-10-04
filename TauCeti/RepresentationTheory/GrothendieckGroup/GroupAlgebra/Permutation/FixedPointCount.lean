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

This file connects the fixed-point classification of permutation representations to the exact
Grothendieck group of a group algebra.  An equivalence between the permutation representations on
two finite `G`-sets identifies their classes in `G₀(k[G])`.  Over a characteristic-zero field,
equality of all fixed-point counts supplies such an equivalence, so it also supplies equality of
permutation classes.

The converse is not stated here.  Over a general coefficient ring, equality in the exact
Grothendieck group is weaker than equivalence of representations, and therefore need not recover
the fixed-point counts.  For a finite group over a characteristic-zero field the converse does
hold: representations are then semisimple, so equal classes recover equivalent representations
and hence equal fixed-point counts.

## Main results

* `TauCeti.permK0_eq_of_nonempty_equiv_ofMulAction`: equivalent permutation representations have
  equal exact Grothendieck classes.
* `TauCeti.permK0_eq_of_forall_natCard_fixedBy_eq`: over a characteristic-zero field, equal
  fixed-point counts give equal permutation classes.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part I, §§2.3 and 3.3.
-/

public section

open MulAction
open scoped MonoidAlgebra

namespace TauCeti

universe u

section CommRing

variable (k : Type u) [CommRing k] {G X Y : Type u} [Monoid G]
  [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]

/-- Equivalent permutation representations have equal classes in the exact Grothendieck group of
the group algebra. -/
theorem permK0_eq_of_nonempty_equiv_ofMulAction
    (h : Nonempty ((Representation.ofMulAction k G X).Equiv
      (Representation.ofMulAction k G Y))) :
    permK0 k G X = permK0 k G Y := by
  obtain ⟨e⟩ := h
  rw [permK0_eq_of_equiv k X (Representation.ofMulAction k G Y) e, permK0_def]

end CommRing

section Field

variable (k : Type u) [Field k] [CharZero k] {G X Y : Type u} [Group G] [Finite G]
  [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]

/-- **Over a characteristic-zero field, equal fixed-point counts give equal permutation
classes.** -/
theorem permK0_eq_of_forall_natCard_fixedBy_eq
    (h : ∀ g : G, Nat.card (fixedBy X g) = Nat.card (fixedBy Y g)) :
    permK0 k G X = permK0 k G Y :=
  permK0_eq_of_nonempty_equiv_ofMulAction k
    ((nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq k).2 h)

end Field

end TauCeti
