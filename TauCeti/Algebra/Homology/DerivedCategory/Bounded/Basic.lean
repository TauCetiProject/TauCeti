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

## References

* Mathlib's `Mathlib/Algebra/Homology/DerivedCategory/Plus.lean`, whose lift of the single
  functors to the bounded-below derived category supplies the pattern used here.
-/

@[expose] public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory.Bounded

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The functor sending an object to a complex concentrated in degree `n`. -/
noncomputable abbrev singleFunctor (n : ℤ) : A ⥤ DerivedCategory.Bounded A :=
  (DerivedCategory.TStructure.t (C := A)).bounded.lift (DerivedCategory.singleFunctor A n)
    (fun _ ↦ ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩)

/-- The single functors into the bounded derived category, with their shift compatibilities. -/
noncomputable def singleFunctors : SingleFunctors A (DerivedCategory.Bounded A) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors A) DerivedCategory.Bounded.ι
    (singleFunctor A) (fun _ ↦ Iso.refl _)

variable {A}

/-- The `n`th bounded single functor is `singleFunctor A n`. -/
@[simp] lemma singleFunctors_functor (n : ℤ) :
    (singleFunctors A).functor n = singleFunctor A n :=
  rfl

/-- The bounded single functors are additive, as the derived single functors are. -/
instance (n : ℤ) : (singleFunctor A n).Additive where
  map_add {_ _ f g} :=
    ObjectProperty.hom_ext _ ((DerivedCategory.singleFunctor A n).map_add (f := f) (g := g))

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

/-- Inclusion identifies the bounded single triangle with the derived single triangle. -/
@[simps!]
noncomputable def _root_.CategoryTheory.ShortComplex.ShortExact.boundedSingleTriangleιIso
    (hS : S.ShortExact) :
    DerivedCategory.Bounded.ι.mapTriangle.obj hS.boundedSingleTriangle ≅ hS.singleTriangle := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ <;>
    simp [DerivedCategory.Bounded.singleFunctor, ObjectProperty.lift]

/-- The bounded single triangle of a short exact sequence is distinguished. -/
lemma _root_.CategoryTheory.ShortComplex.ShortExact.boundedSingleTriangle_distinguished
    (hS : S.ShortExact) :
    hS.boundedSingleTriangle ∈ distTriang (DerivedCategory.Bounded A) :=
  (DerivedCategory.Bounded.ι.map_distinguished_iff _).1 <|
    isomorphic_distinguished _ hS.singleTriangle_distinguished _ hS.boundedSingleTriangleιIso

/-- **The connecting morphism of the bounded single triangle is natural** in morphisms of short
exact sequences. -/
@[reassoc]
lemma _root_.CategoryTheory.ShortComplex.ShortExact.boundedSingleTriangle_mor₃_naturality
    {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) :
    (DerivedCategory.Bounded.singleFunctor A 0).map φ.τ₃ ≫ h₂.boundedSingleTriangle.mor₃ =
      h₁.boundedSingleTriangle.mor₃ ≫
        ((DerivedCategory.Bounded.singleFunctor A 0).map φ.τ₁)⟦(1 : ℤ)⟧' := by
  apply DerivedCategory.Bounded.ι.map_injective
  have h := (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ).comm₃
  simp only [ShortComplex.ShortExact.singleTriangle_mor₃,
    ShortComplex.ShortExact.singleTriangle.map_hom₁,
    ShortComplex.ShortExact.singleTriangle.map_hom₃] at h
  have k := (DerivedCategory.Bounded.ι.commShiftIso (1 : ℤ)).inv.naturality
    ((DerivedCategory.Bounded.singleFunctor A 0).map φ.τ₁)
  simp only [Functor.comp_map] at k
  simp only [Functor.map_comp, ShortComplex.ShortExact.boundedSingleTriangle_mor₃]
  -- Both sides are composites in `D(A)`, where they agree by the naturality of `singleδ`.
  calc _ = (DerivedCategory.singleFunctor A 0).map φ.τ₃ ≫ h₂.singleδ ≫
        (DerivedCategory.Bounded.ι.commShiftIso (1 : ℤ)).inv.app
          ((DerivedCategory.Bounded.singleFunctor A 0).obj S₂.X₁) := rfl
    _ = h₁.singleδ ≫ ((DerivedCategory.Bounded.singleFunctor A 0).map φ.τ₁).hom⟦(1 : ℤ)⟧' ≫
        (DerivedCategory.Bounded.ι.commShiftIso (1 : ℤ)).inv.app
          ((DerivedCategory.Bounded.singleFunctor A 0).obj S₂.X₁) := ((reassoc_of% h) _).symm
    _ = _ := (congrArg (h₁.singleδ ≫ ·) k).trans (Category.assoc _ _ _).symm

end TauCeti
