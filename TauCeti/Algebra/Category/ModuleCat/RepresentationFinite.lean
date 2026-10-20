/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Representation-finite rings

A ring `A` is **representation-finite** (`TauCeti.IsRepresentationFinite`) if it has only finitely
many isomorphism classes of finitely generated indecomposable modules. As for quivers
(`TauCeti.IsFiniteRepType`), this is stated as the finiteness of the skeleton of the full
subcategory these modules span, so that "isomorphism class" is Mathlib's. The modules are taken in
a universe `w`, which is a parameter of the predicate.

The predicate is used for the module category of a finite-dimensional algebra, where it says that
the quiver of irreducible morphisms has finitely many vertices
(`TauCeti.IrreducibleMorphismQuiver.finite_iff_isRepresentationFinite`), and for path algebras,
where it agrees with finite representation type of the quiver
(`TauCeti.isFiniteRepType_iff_isRepresentationFinite_pathAlgebra`).

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. I (2006).
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995).
-/

public section

namespace TauCeti

open CategoryTheory

universe w v

variable (A : Type v) [Ring A]

/-- **Representation-finite rings**: `A` has only finitely many isomorphism classes of finitely
generated indecomposable modules (in the universe `w`). It is stated as the finiteness of the
skeleton of the full subcategory they span. -/
def IsRepresentationFinite : Prop :=
  Finite (Skeleton (ObjectProperty.FullSubcategory
    fun M : ModuleCat.{w} A ↦ Module.Finite A M ∧ Indecomposable M))

/-- Unfolding `TauCeti.IsRepresentationFinite` in modules where its body is not exposed. -/
@[simp]
theorem isRepresentationFinite_iff :
    IsRepresentationFinite.{w} A ↔ Finite (Skeleton (ObjectProperty.FullSubcategory
      fun M : ModuleCat.{w} A ↦ Module.Finite A M ∧ Indecomposable M)) :=
  Iff.rfl

end TauCeti
