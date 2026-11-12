/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Basic
public import TauCeti.Algebra.Category.ModuleCat.RepresentationFinite

/-!
# Morita invariance of the indecomposable modules

A ring `A` is representation-finite (`TauCeti.IsRepresentationFinite`) when it has finitely many
isomorphism classes of finitely generated indecomposable modules. This number is an invariant of
the module category: it does not depend on the universe of the modules, and an equivalence of
module categories preserves it (`CategoryTheory.Equivalence.card_skeleton_indecomposable_eq`).
Hence **Morita equivalent algebras** (`IsMoritaEquivalent R A B`) have the same number of
isomorphism classes of finitely generated indecomposable modules, and one is representation-finite
exactly when the other is.

Over a commutative semisimple ring the number is the number of maximal ideals
(`TauCeti.card_skeleton_indecomposable_eq_card_maximalSpectrum`). For a field `k` this gives one
class and for `k × k` two, so `k` and `k × k` are not Morita equivalent.

## Main results

* `IsMoritaEquivalent.isRepresentationFinite_iff` and
  `IsMoritaEquivalent.card_skeleton_indecomposable_eq`: Morita equivalent algebras are
  representation-finite together and have equally many finitely generated indecomposable modules.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation theory of Artin algebras*, Cambridge
  Studies in Advanced Mathematics 36 (1995), Section II.2.
-/

public section

universe v u₁ u₂

open CategoryTheory

namespace TauCeti

section Morita

variable {R : Type*} [CommSemiring R] {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B]
  [Algebra R B] [Small.{v} A] [Small.{v} B]

/-- **Morita equivalent algebras have equally many finitely generated indecomposable modules** up
to isomorphism, counted with modules in any universe in which both algebras are small. -/
theorem _root_.IsMoritaEquivalent.card_skeleton_indecomposable_eq (h : IsMoritaEquivalent R A B) :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M)) =
      Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v} B ↦ Module.Finite B N ∧ Indecomposable N)) := by
  obtain ⟨e⟩ := h.cond
  rw [card_skeleton_indecomposable_eq_card_skeleton_indecomposable.{u₁, v, max u₁ u₂} A,
    card_skeleton_indecomposable_eq_card_skeleton_indecomposable.{u₂, v, max u₁ u₂} B]
  exact e.eqv.card_skeleton_indecomposable_eq

/-- **Representation-finiteness is a Morita invariant**, with modules in any universe in which both
algebras are small. -/
theorem _root_.IsMoritaEquivalent.isRepresentationFinite_iff (h : IsMoritaEquivalent R A B) :
    IsRepresentationFinite.{v} A ↔ IsRepresentationFinite.{v} B := by
  obtain ⟨e⟩ := h.cond
  rw [isRepresentationFinite_iff_isRepresentationFinite.{u₁, v, max u₁ u₂} A,
    isRepresentationFinite_iff_isRepresentationFinite.{u₂, v, max u₁ u₂} B]
  exact e.eqv.isRepresentationFinite_iff

end Morita

end TauCeti
