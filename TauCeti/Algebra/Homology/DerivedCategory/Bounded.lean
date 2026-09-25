/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Shift.SingleFunctorsLift

/-!
# Single objects and short exact triangles in the bounded derived category

The single functors into the derived category lift to its bounded subcategory in every degree.
A short exact sequence then gives a distinguished triangle of bounded single objects.
-/

@[expose] public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory.Bounded

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The functor sending an object to a complex concentrated in degree `n`. -/
noncomputable abbrev singleFunctor (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (n : ℤ) : A ⥤ DerivedCategory.Bounded A :=
  (DerivedCategory.TStructure.t (C := A)).bounded.lift (DerivedCategory.singleFunctor A n)
    (fun _ ↦ ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩)

/-- The single functors into the bounded derived category, with their shift compatibilities. -/
noncomputable def singleFunctors (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : SingleFunctors A (DerivedCategory.Bounded A) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors A) DerivedCategory.Bounded.ι
    (singleFunctor A) (fun _ ↦ Iso.refl _)

/-- The `n`th bounded single functor is `singleFunctor A n`. -/
@[simp] lemma singleFunctors_functor (n : ℤ) :
    (singleFunctors A).functor n = singleFunctor A n :=
  rfl

/-- Inclusion of a bounded single object recovers the corresponding derived single object. -/
@[simp] lemma singleFunctor_obj_obj (n : ℤ) (X : A) :
    ((singleFunctor A n).obj X).obj =
      (DerivedCategory.singleFunctor A n).obj X :=
  rfl

/-- Inclusion of a map of bounded single objects recovers the derived single map. -/
@[simp] lemma singleFunctor_map_hom (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    ((singleFunctor A n).map f).hom =
      (DerivedCategory.singleFunctor A n).map f :=
  rfl

/-- The bounded single functor followed by inclusion is the derived single functor. -/
@[simps!]
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor A n ⋙ DerivedCategory.Bounded.ι ≅ DerivedCategory.singleFunctor A n :=
  Iso.refl _

instance (n : ℤ) : (singleFunctor A n).Additive where

end DerivedCategory.Bounded

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {S : ShortComplex A}

/-- The triangle of bounded single objects associated with a short exact sequence. -/
@[implicit_reducible, simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
noncomputable def _root_.CategoryTheory.ShortComplex.ShortExact.boundedSingleTriangle
    (hS : S.ShortExact) : Triangle (DerivedCategory.Bounded A) :=
  Triangle.mk ((DerivedCategory.Bounded.singleFunctor A 0).map S.f)
    ((DerivedCategory.Bounded.singleFunctor A 0).map S.g)
    ((DerivedCategory.TStructure.t (C := A)).bounded.fullyFaithfulι.preimage
      (hS.singleδ ≫ (DerivedCategory.Bounded.ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₁)))

/-- The bounded single triangle of a short exact sequence is distinguished. -/
lemma _root_.CategoryTheory.ShortComplex.ShortExact.boundedSingleTriangle_distinguished
    (hS : S.ShortExact) :
    hS.boundedSingleTriangle ∈ distTriang (DerivedCategory.Bounded A) := by
  rw [← DerivedCategory.Bounded.ι.map_distinguished_iff, Functor.mapTriangle_obj]
  exact isomorphic_distinguished _ hS.singleTriangle_distinguished _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp))

end TauCeti
