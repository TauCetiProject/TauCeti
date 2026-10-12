/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Basic
public import TauCeti.Algebra.Homology.DerivedCategory.Equivalence
public import TauCeti.CategoryTheory.ObjectProperty

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

/-- The bounded derived action of the identity functor is the identity. -/
noncomputable def mapBoundedDerivedCategoryIdIso :
    (𝟭 A).mapBoundedDerivedCategory ≅ 𝟭 (DerivedCategory.Bounded A) :=
  ((DerivedCategory.TStructure.t (C := A)).bounded.fullyFaithfulι.whiskeringRight _).preimageIso
    ((𝟭 A).mapBoundedDerivedCategoryCompιIso ≪≫
      isoWhiskerLeft DerivedCategory.Bounded.ι (mapDerivedCategoryIdIso A) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

/-- The bounded derived action preserves composition of exact functors. -/
noncomputable def mapBoundedDerivedCategoryCompIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    F.mapBoundedDerivedCategory ⋙ G.mapBoundedDerivedCategory ≅
      (F ⋙ G).mapBoundedDerivedCategory :=
  ((DerivedCategory.TStructure.t (C := C)).bounded.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator .. ≪≫
      isoWhiskerLeft _ G.mapBoundedDerivedCategoryCompιIso ≪≫
      (Functor.associator ..).symm ≪≫
      isoWhiskerRight F.mapBoundedDerivedCategoryCompιIso _ ≪≫
      Functor.associator .. ≪≫
      isoWhiskerLeft DerivedCategory.Bounded.ι (mapDerivedCategoryCompIso F G) ≪≫
      (F ⋙ G).mapBoundedDerivedCategoryCompιIso.symm)

end CategoryTheory.Functor

namespace CategoryTheory.Equivalence

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (e : A ≌ B) [e.functor.Additive]

/-- Boundedness is the inverse image of boundedness under an additive derived equivalence. -/
lemma bounded_inverseImage_mapDerivedCategory :
    (DerivedCategory.TStructure.t (C := B)).bounded.inverseImage
        e.mapDerivedCategory.functor = (DerivedCategory.TStructure.t (C := A)).bounded := by
  ext X
  simp only [ObjectProperty.prop_inverseImage_iff, mapDerivedCategory_functor]
  constructor
  · intro hX
    have unit : X ≅ e.inverse.mapDerivedCategory.obj (e.functor.mapDerivedCategory.obj X) := by
      simpa only [mapDerivedCategory_functor, mapDerivedCategory_inverse,
        Functor.comp_obj, Functor.id_obj] using e.mapDerivedCategory.unitIso.app X
    exact (DerivedCategory.TStructure.t (C := A)).bounded.prop_of_iso unit.symm
      (e.inverse.bounded_mapDerivedCategory _ hX)
  · exact e.functor.bounded_mapDerivedCategory X

/-- An additive equivalence restricts to the cohomologically bounded objects. -/
noncomputable def mapBoundedDerivedCategory :
    DerivedCategory.Bounded A ≌ DerivedCategory.Bounded B :=
  e.mapDerivedCategory.congrFullSubcategory e.bounded_inverseImage_mapDerivedCategory

/-- The functor of the bounded equivalence is the actual termwise exact-functor action. -/
@[simp]
lemma mapBoundedDerivedCategory_functor :
    e.mapBoundedDerivedCategory.functor = e.functor.mapBoundedDerivedCategory := by
  simp only [mapBoundedDerivedCategory, congrFullSubcategory_functor_eq_lift,
    mapDerivedCategory_functor]
  rfl

/-- The inverse of the bounded equivalence is the termwise action of the original inverse. -/
@[simp]
lemma mapBoundedDerivedCategory_inverse :
    e.mapBoundedDerivedCategory.inverse = e.inverse.mapBoundedDerivedCategory := by
  simp only [mapBoundedDerivedCategory, congrFullSubcategory_inverse_eq_lift,
    mapDerivedCategory_inverse]
  rfl

/-- Inclusion identifies the bounded equivalence functor with its termwise derived action. -/
noncomputable def mapBoundedDerivedCategoryFunctorCompιIso :
    e.mapBoundedDerivedCategory.functor ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ e.functor.mapDerivedCategory :=
  isoWhiskerRight (eqToIso e.mapBoundedDerivedCategory_functor) _ ≪≫
    e.functor.mapBoundedDerivedCategoryCompιIso

noncomputable instance : e.mapBoundedDerivedCategory.functor.CommShift ℤ :=
  Functor.CommShift.ofComp (e.mapBoundedDerivedCategoryFunctorCompιIso) ℤ

noncomputable instance : NatTrans.CommShift (e.mapBoundedDerivedCategoryFunctorCompιIso).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

instance : e.mapBoundedDerivedCategory.functor.IsTriangulated := by
  rw [Functor.isTriangulated_iff_comp_right (e.mapBoundedDerivedCategoryFunctorCompιIso)]
  infer_instance

end CategoryTheory.Equivalence
