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

/-- The single functors into the bounded derived category, with their shift compatibilities. -/
noncomputable def singleFunctors (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] : SingleFunctors A (DerivedCategory.Bounded A) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors A) DerivedCategory.Bounded.ι
    (fun n ↦ (DerivedCategory.TStructure.t (C := A)).bounded.lift
      (DerivedCategory.singleFunctor A n)
      (fun _ ↦ ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩⟩))
    (fun _ ↦ Iso.refl _)

/-- The functor sending an object to a complex concentrated in degree `n`. -/
noncomputable abbrev singleFunctor (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (n : ℤ) : A ⥤ DerivedCategory.Bounded A :=
  (singleFunctors A).functor n

/-- Inclusion of a bounded single object recovers the corresponding derived single object. -/
@[simp] lemma ι_obj_singleFunctor_obj (n : ℤ) (X : A) :
    DerivedCategory.Bounded.ι.obj ((singleFunctor A n).obj X) =
      (DerivedCategory.singleFunctor A n).obj X :=
  rfl

/-- Inclusion of a map of bounded single objects recovers the derived single map. -/
@[simp] lemma ι_map_singleFunctor_map (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    DerivedCategory.Bounded.ι.map ((singleFunctor A n).map f) =
      (DerivedCategory.singleFunctor A n).map f :=
  rfl

/-- The bounded single functor followed by inclusion is the derived single functor. -/
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor A n ⋙ DerivedCategory.Bounded.ι ≅ DerivedCategory.singleFunctor A n :=
  Iso.refl _

instance (n : ℤ) : (singleFunctor A n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

variable {S : ShortComplex A}

/-- The triangle of bounded single objects associated with a short exact sequence. -/
noncomputable def singleTriangleBounded (hS : S.ShortExact) :
    Triangle (DerivedCategory.Bounded A) :=
  let P := (DerivedCategory.TStructure.t (C := A)).bounded
  let F := singleFunctor A 0
  Triangle.mk (F.map S.f) (F.map S.g)
    (P.fullyFaithfulι.preimage
      (hS.singleδ ≫ (P.ι.commShiftIso (1 : ℤ)).inv.app (F.obj S.X₁)))

/-- The bounded single triangle of a short exact sequence is distinguished. -/
lemma singleTriangleBounded_distinguished (hS : S.ShortExact) :
    singleTriangleBounded hS ∈ distTriang (DerivedCategory.Bounded A) := by
  let P := (DerivedCategory.TStructure.t (C := A)).bounded
  rw [← P.ι.map_distinguished_iff]
  dsimp only [P]
  simpa [singleTriangleBounded, Functor.mapTriangle, singleFunctor, singleFunctors,
    SingleFunctors.lift, ObjectProperty.lift, ShortComplex.ShortExact.singleTriangle,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Category.assoc,
    DerivedCategory.Bounded.ι_obj_singleFunctor_obj,
    DerivedCategory.Bounded.ι_map_singleFunctor_map] using
      (CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished hS)

end DerivedCategory.Bounded

end TauCeti
