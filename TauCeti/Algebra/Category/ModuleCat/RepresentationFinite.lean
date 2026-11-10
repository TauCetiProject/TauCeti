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

variable {A} in
/-- A ring is representation-finite as soon as every finitely generated indecomposable module is
isomorphic to a member of a fixed finite set of modules. -/
theorem isRepresentationFinite_of_forall_exists_iso {S : Set (ModuleCat.{w} A)} (hS : S.Finite)
    (h : ∀ M : ModuleCat.{w} A, Module.Finite A M → Indecomposable M →
      ∃ Q ∈ S, Nonempty (M ≅ Q)) :
    IsRepresentationFinite.{w} A := by
  rw [isRepresentationFinite_iff]
  let P : ObjectProperty (ModuleCat.{w} A) := fun M ↦ Module.Finite A M ∧ Indecomposable M
  have := hS.to_subtype
  have hrep (x : Skeleton P.FullSubcategory) :=
    h ((fromSkeleton P.FullSubcategory).obj x).obj ((fromSkeleton _).obj x).property.1
      ((fromSkeleton _).obj x).property.2
  choose q hq he using hrep
  refine Finite.of_injective (fun x ↦ (⟨q x, hq x⟩ : S)) fun x y hxy ↦ ?_
  have hxy' : q x = q y := congrArg Subtype.val hxy
  obtain ⟨ex⟩ := he x
  obtain ⟨ey⟩ := he y
  let e : ((fromSkeleton P.FullSubcategory).obj x).obj ≅ ((fromSkeleton _).obj y).obj :=
    ex ≪≫ eqToIso hxy' ≪≫ ey.symm
  exact skeleton_skeletal _ ⟨(fromSkeleton _).preimageIso (P.fullyFaithfulι.preimageIso e)⟩

end TauCeti
