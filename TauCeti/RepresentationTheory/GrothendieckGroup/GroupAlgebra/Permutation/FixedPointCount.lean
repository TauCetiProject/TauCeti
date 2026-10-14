/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.FixedPointCount
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Lattice

/-!
# Permutation classes from fixed-point counts

This file connects the fixed-point classification of permutation representations to the exact
Grothendieck group of a group algebra. An equivalence between the permutation representations on
two finite `G`-sets identifies their classes in `G₀(k[G])`. Equality of all fixed-point counts
gives equality of permutation classes over every field: the corresponding integral permutation
lattices have isomorphic rationalizations, hence equal reduction classes.

The converse is not stated here.  Over a general coefficient ring, equality in the exact
Grothendieck group is weaker than equivalence of representations, and therefore need not recover
the fixed-point counts.  For a finite group over a characteristic-zero field the converse does
hold: representations are then semisimple, so equal classes recover equivalent representations
and hence equal fixed-point counts.

## Main results

* `TauCeti.permK0_eq_of_nonempty_equiv_ofMulAction`: equivalent permutation representations have
  equal exact Grothendieck classes.
* `TauCeti.permK0_eq_of_forall_natCard_fixedBy_eq`: over every field, equal fixed-point counts give
  equal permutation classes.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part I, §§2.3 and 3.3.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  §VII.3, (7.3.3).
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, Chapter I, Lemma 2.12.
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

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction
  Finsupp.comapDistribMulAction comapSMulCommClass

variable (k : Type u) [Field k] {G X Y : Type u} [Group G] [Finite G]
  [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]

/-- **Over every field, equal fixed-point counts give equal permutation classes.** -/
theorem permK0_eq_of_forall_natCard_fixedBy_eq
    (h : ∀ g : G, Nat.card (fixedBy X g) = Nat.card (fixedBy Y g)) :
    permK0 k G X = permK0 k G Y := by
  have hℚ : Nonempty ((Representation.baseChange ℚ
      (Representation.ofDistribMulAction ℤ G (X →₀ ℤ))).Equiv
      (Representation.baseChange ℚ
        (Representation.ofDistribMulAction ℤ G (Y →₀ ℤ)))) := by
    obtain ⟨e⟩ := (nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq ℚ).2 h
    exact ⟨((baseChangeComapEquiv ℤ ℚ G X).trans e).trans
      (baseChangeComapEquiv ℤ ℚ G Y).symm⟩
  rw [← reductionK0_finsupp_int, ← reductionK0_finsupp_int]
  exact reductionK0_eq_of_nonempty_equiv_baseChange_rat k G _ _ hℚ

end Field

end TauCeti
