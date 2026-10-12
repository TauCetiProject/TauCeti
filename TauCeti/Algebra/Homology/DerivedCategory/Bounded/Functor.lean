/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Basic
public import TauCeti.Algebra.Homology.DerivedCategory.Equivalence

/-!
# Exact functors on bounded derived categories

An exact functor between abelian categories acts termwise on complexes and hence on bounded
derived categories. This restriction is triangulated and commutes with suspension. An additive
equivalence induces an equivalence of bounded derived categories with these same actual functors.
The single-object comparison characterizes their action on objects in any fixed degree.

The construction uses Mathlib's `Functor.mapDerivedCategory`, its factorization through termwise
mapping, and `Localization.equivalence`; no additional localization is constructed.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Termwise exact functors preserve cohomological boundedness. -/
lemma bounded_mapDerivedCategory (X : DerivedCategory A)
    (hX : (DerivedCategory.TStructure.t (C := A)).bounded X) :
    (DerivedCategory.TStructure.t (C := B)).bounded (F.mapDerivedCategory.obj X) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hX
  obtain ⟨K, _, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE_of_isLE a b
  let L : CochainComplex B ℤ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have : L.IsGE a := by
    rw [CochainComplex.isGE_iff]
    exact fun i hi ↦ (K.exactAt_of_isGE a i hi).map F
  have : L.IsLE b := by
    rw [CochainComplex.isLE_iff]
    exact fun i hi ↦ (K.exactAt_of_isLE b i hi).map F
  exact (DerivedCategory.TStructure.t (C := B)).bounded.prop_of_iso
    (F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K).symm
    ⟨⟨a, by simpa only [Functor.comp_obj] using
      (DerivedCategory.isGE_Q_obj_iff L a).2 ‹L.IsGE a›⟩,
      ⟨b, by simpa only [Functor.comp_obj] using
        (DerivedCategory.isLE_Q_obj_iff L b).2 ‹L.IsLE b›⟩⟩

/-- The termwise action of an exact functor restricted to bounded derived categories. -/
noncomputable def mapBoundedDerivedCategory :
    DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded B :=
  (DerivedCategory.TStructure.t (C := B)).bounded.lift
    (DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory)
    (fun X ↦ F.bounded_mapDerivedCategory X.obj X.property)

/-- Inclusion identifies the bounded action with Mathlib's derived action. -/
noncomputable def mapBoundedDerivedCategoryCompιIso :
    F.mapBoundedDerivedCategory ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory :=
  (DerivedCategory.TStructure.t (C := B)).bounded.liftCompιIso _ _

noncomputable instance : F.mapBoundedDerivedCategory.CommShift ℤ := by
  exact Functor.CommShift.ofComp F.mapBoundedDerivedCategoryCompιIso ℤ

noncomputable instance : NatTrans.CommShift F.mapBoundedDerivedCategoryCompιIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance : F.mapBoundedDerivedCategory.IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right F.mapBoundedDerivedCategoryCompιIso]
  infer_instance

/-- The bounded action commutes with the single-object embedding in every degree. -/
noncomputable def mapBoundedDerivedCategorySingleFunctor (n : ℤ) :
    TauCeti.DerivedCategory.Bounded.singleFunctor A n ⋙ F.mapBoundedDerivedCategory ≅
      F ⋙ TauCeti.DerivedCategory.Bounded.singleFunctor B n :=
  ((DerivedCategory.TStructure.t (C := B)).bounded.fullyFaithfulι.whiskeringRight _).preimageIso
    (F.mapDerivedCategorySingleFunctor n)

end CategoryTheory.Functor

namespace CategoryTheory.Equivalence

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (e : A ≌ B) [e.functor.Additive]

/-- An additive equivalence restricts to the cohomologically bounded objects. -/
noncomputable def mapBoundedDerivedCategory :
    DerivedCategory.Bounded A ≌ DerivedCategory.Bounded B :=
  Equivalence.mk e.functor.mapBoundedDerivedCategory e.inverse.mapBoundedDerivedCategory
    (((DerivedCategory.TStructure.t (C := A)).bounded.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.leftUnitor _ ≪≫
        (Functor.rightUnitor _).symm ≪≫
        (by simpa only [mapDerivedCategory_functor, mapDerivedCategory_inverse] using
          isoWhiskerLeft DerivedCategory.Bounded.ι e.mapDerivedCategory.unitIso) ≪≫
        (Functor.associator ..).symm ≪≫
        isoWhiskerRight e.functor.mapBoundedDerivedCategoryCompιIso.symm _ ≪≫
        Functor.associator .. ≪≫
        isoWhiskerLeft _ e.inverse.mapBoundedDerivedCategoryCompιIso.symm ≪≫
        (Functor.associator ..).symm))
    (((DerivedCategory.TStructure.t (C := B)).bounded.fullyFaithfulι.whiskeringRight _).preimageIso
      (Functor.associator .. ≪≫
        isoWhiskerLeft _ e.functor.mapBoundedDerivedCategoryCompιIso ≪≫
        (Functor.associator ..).symm ≪≫
        isoWhiskerRight e.inverse.mapBoundedDerivedCategoryCompιIso _ ≪≫
        Functor.associator .. ≪≫
        (by simpa only [mapDerivedCategory_functor, mapDerivedCategory_inverse] using
          isoWhiskerLeft DerivedCategory.Bounded.ι e.mapDerivedCategory.counitIso) ≪≫
        Functor.rightUnitor _ ≪≫
        (Functor.leftUnitor _).symm))

/-- The functor of the bounded equivalence is the actual termwise exact-functor action. -/
@[simp]
lemma mapBoundedDerivedCategory_functor :
    e.mapBoundedDerivedCategory.functor = e.functor.mapBoundedDerivedCategory :=
  (rfl)

/-- The inverse of the bounded equivalence is the termwise action of the original inverse. -/
@[simp]
lemma mapBoundedDerivedCategory_inverse :
    e.mapBoundedDerivedCategory.inverse = e.inverse.mapBoundedDerivedCategory :=
  (rfl)

noncomputable instance : e.mapBoundedDerivedCategory.functor.CommShift ℤ :=
  inferInstanceAs (e.functor.mapBoundedDerivedCategory.CommShift ℤ)

instance : e.mapBoundedDerivedCategory.functor.IsTriangulated :=
  inferInstanceAs (e.functor.mapBoundedDerivedCategory.IsTriangulated)

end CategoryTheory.Equivalence
