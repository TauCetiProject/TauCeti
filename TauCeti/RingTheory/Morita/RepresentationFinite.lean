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
module categories preserves it
(`CategoryTheory.Equivalence.card_skeleton_finite_indecomposable_modules_eq`). Hence **Morita
equivalent algebras** (`IsMoritaEquivalent R A B`) have the same number of isomorphism classes of
finitely generated indecomposable modules, and one is representation-finite exactly when the other
is.

Over a commutative semisimple ring the number is the number of maximal ideals
(`TauCeti.card_skeleton_finite_indecomposable_eq_card_maximalSpectrum`). For a field `k` this gives
one class and for `k × k` two, so `k` and `k × k` are not Morita equivalent.

## Main results

* `IsMoritaEquivalent.nonempty_skeletonFiniteIndecomposableModulesEquiv`: the isomorphism classes
  of finitely generated indecomposable modules over Morita equivalent algebras are in bijection.
* `IsMoritaEquivalent.isRepresentationFinite_iff` and
  `IsMoritaEquivalent.card_skeleton_finite_indecomposable_modules_eq`: Morita equivalent algebras
  are representation-finite together and have equally many finitely generated indecomposable
  modules.

## References

* M. Auslander, I. Reiten and S. O. Smalø, *Representation theory of Artin algebras*, Cambridge
  Studies in Advanced Mathematics 36 (1995), Section II.2.
-/

public section

universe v v' u₁ u₂

open CategoryTheory

namespace TauCeti

section Morita

variable {R : Type*} [CommSemiring R] {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B]
  [Algebra R B] [Small.{v} A] [Small.{v'} B]

/-- **Morita equivalent algebras have corresponding finitely generated indecomposable modules**:
their isomorphism classes are in bijection, with the modules over each algebra taken in any universe
in which that algebra is small. -/
theorem _root_.IsMoritaEquivalent.nonempty_skeletonFiniteIndecomposableModulesEquiv
    (h : IsMoritaEquivalent R A B) :
    Nonempty (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M) ≃
      Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} B ↦ Module.Finite B N ∧ Indecomposable N)) := by
  obtain ⟨e⟩ := h.cond
  exact ⟨(skeletonFiniteIndecomposableEquivSkeletonFiniteIndecomposable.{v, max u₁ u₂, u₁} A).trans
    (e.eqv.skeletonFiniteIndecomposableModulesEquiv.trans
      (skeletonFiniteIndecomposableEquivSkeletonFiniteIndecomposable.{max u₁ u₂, v', u₂} B))⟩

/-- **Morita equivalent algebras have equally many finitely generated indecomposable modules** up
to isomorphism, counted with the modules over each algebra in any universe in which that algebra is
small. -/
theorem _root_.IsMoritaEquivalent.card_skeleton_finite_indecomposable_modules_eq
    (h : IsMoritaEquivalent R A B) :
    Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun M : ModuleCat.{v} A ↦ Module.Finite A M ∧ Indecomposable M)) =
      Nat.card (Skeleton (ObjectProperty.FullSubcategory
        fun N : ModuleCat.{v'} B ↦ Module.Finite B N ∧ Indecomposable N)) :=
  Nat.card_congr h.nonempty_skeletonFiniteIndecomposableModulesEquiv.some

/-- **Representation-finiteness is a Morita invariant**, with the modules over each algebra taken in
any universe in which that algebra is small. -/
theorem _root_.IsMoritaEquivalent.isRepresentationFinite_iff (h : IsMoritaEquivalent R A B) :
    IsRepresentationFinite.{v} A ↔ IsRepresentationFinite.{v'} B := by
  rw [TauCeti.isRepresentationFinite_iff, TauCeti.isRepresentationFinite_iff,
    h.nonempty_skeletonFiniteIndecomposableModulesEquiv.some.finite_iff]

end Morita

end TauCeti
