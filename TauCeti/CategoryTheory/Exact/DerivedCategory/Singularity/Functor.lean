/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Functor.Conflation
public import TauCeti.CategoryTheory.Exact.DerivedCategory.Singularity.Stable.Basic

/-!
# Conflation-exact functors on singularity categories

Let `F : C ⥤ D` be a conflation-exact functor between exact categories `E` and `E'` which sends
`E`-projective objects to `E'`-projective objects. The induced triangle functor
`Dᵇ(E) ⥤ Dᵇ(E')` sends bounded complexes of projectives to bounded complexes of projectives, so it
descends to a triangle functor `D_sg(E) ⥤ D_sg(E')` between the singularity categories. It
commutes with placing an object in degree zero.

## Main definitions

* `TauCeti.ExactStructure.IsConflationExact.singularityLocalizerMorphism`: the functor
  `Dᵇ(E) ⥤ Dᵇ(E')` as a morphism of localizers for the bounded complexes of projectives.
* `TauCeti.ExactStructure.IsConflationExact.mapSingularityCategory`: the induced triangle functor
  `D_sg(E) ⥤ D_sg(E')`.
* `TauCeti.ExactStructure.IsConflationExact.mapSingularityCategoryFactors`: its composite with the
  quotient functor `Dᵇ(E) ⥤ D_sg(E)` is `Dᵇ(E) ⥤ Dᵇ(E')` followed by the quotient functor,
  compatibly with shifts.
* `TauCeti.ExactStructure.IsConflationExact.singleToSingularityCompMapSingularityCategoryIso`: it
  commutes with the functors `C ⥤ D_sg(E)` and `D ⥤ D_sg(E')` placing an object in degree zero.

## Main results

* `TauCeti.ExactStructure.IsConflationExact.boundedProjective_le_inverseImage`: the functor
  `Dᵇ(E) ⥤ Dᵇ(E')` preserves the classes of bounded complexes of projectives.
* `TauCeti.ExactStructure.IsConflationExact.mapSingularityCategory_map_conflationδ`: the functor
  `D_sg(E) ⥤ D_sg(E')` preserves connecting morphisms of conflations.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 1.2.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

namespace IsConflationExact

variable (hF : E.IsConflationExact E' F)
  (hP : ∀ {X : C}, E.isProjective X → E'.isProjective (F.obj X))
include hF hP

/-- The functor `Dᵇ(E) ⥤ Dᵇ(E')` sends the classes of bounded complexes of `E`-projectives to
classes of bounded complexes of `E'`-projectives. -/
theorem boundedProjective_le_inverseImage :
    E.boundedProjective ≤ E'.boundedProjective.inverseImage hF.mapBoundedDerivedCategory := by
  intro X hX
  obtain ⟨K, hK, ⟨e⟩⟩ := (E.boundedProjective_iff X).1 hX
  exact (E'.boundedProjective_iff _).2 ⟨⟨_, F.bounded_mapHomologicalComplex K.property⟩,
    fun n ↦ hP (hK n), ⟨hF.mapBoundedDerivedCategory.mapIso e ≪≫
      hF.mapBoundedDerivedCategoryFactors.app _ ≪≫
      (BoundedDerivedCategory.Q E').mapIso (F.mapHomotopyCategoryBoundedQuotientObjIso K)⟩⟩

/-- The functor `Dᵇ(E) ⥤ Dᵇ(E')` induced by a conflation-exact functor preserving projectives, as
a morphism of localizers for the bounded complexes of projectives. -/
noncomputable def singularityLocalizerMorphism :
    LocalizerMorphism E.boundedProjective.trW E'.boundedProjective.trW where
  functor := hF.mapBoundedDerivedCategory
  map _ _ f hf := (ObjectProperty.inverseImage_trW_iff _ _ f).1
    (ObjectProperty.trW_monotone (hF.boundedProjective_le_inverseImage hP) _ hf)

@[simp]
theorem singularityLocalizerMorphism_functor :
    (hF.singularityLocalizerMorphism hP).functor = hF.mapBoundedDerivedCategory :=
  (rfl)

noncomputable instance : (hF.singularityLocalizerMorphism hP).functor.CommShift ℤ :=
  inferInstanceAs (hF.mapBoundedDerivedCategory.CommShift ℤ)

instance : (hF.singularityLocalizerMorphism hP).functor.IsTriangulated :=
  inferInstanceAs hF.mapBoundedDerivedCategory.IsTriangulated

/-- **The triangle functor `D_sg(E) ⥤ D_sg(E')` induced by a conflation-exact functor preserving
projectives.** -/
noncomputable def mapSingularityCategory : E.SingularityCategory ⥤ E'.SingularityCategory :=
  (hF.singularityLocalizerMorphism hP).localizedFunctor (SingularityCategory.Q E)
    (SingularityCategory.Q E')

noncomputable instance : (hF.mapSingularityCategory hP).CommShift ℤ :=
  inferInstanceAs (((hF.singularityLocalizerMorphism hP).localizedFunctor
    (SingularityCategory.Q E) (SingularityCategory.Q E')).CommShift ℤ)

instance : (hF.mapSingularityCategory hP).IsTriangulated :=
  LocalizerMorphism.isTriangulated_localizedFunctor _ (SingularityCategory.Q E)
    (SingularityCategory.Q E')

/-- The functor `hF.mapSingularityCategory hP` is induced by the functor `Dᵇ(E) ⥤ Dᵇ(E')`. -/
noncomputable def mapSingularityCategoryFactors :
    SingularityCategory.Q E ⋙ hF.mapSingularityCategory hP ≅
      hF.mapBoundedDerivedCategory ⋙ SingularityCategory.Q E' :=
  (CatCommSq.iso (hF.singularityLocalizerMorphism hP).functor (SingularityCategory.Q E)
    (SingularityCategory.Q E') ((hF.singularityLocalizerMorphism hP).localizedFunctor
      (SingularityCategory.Q E) (SingularityCategory.Q E'))).symm

instance : NatTrans.CommShift (hF.mapSingularityCategoryFactors hP).hom ℤ :=
  have := (hF.singularityLocalizerMorphism hP).natTransCommShift_hom (M := ℤ)
    (SingularityCategory.Q E) (SingularityCategory.Q E')
    ((hF.singularityLocalizerMorphism hP).localizedFunctor (SingularityCategory.Q E)
      (SingularityCategory.Q E')) (CatCommSq.iso ..)
  inferInstanceAs (NatTrans.CommShift (CatCommSq.iso (hF.singularityLocalizerMorphism hP).functor
    (SingularityCategory.Q E) (SingularityCategory.Q E')
    ((hF.singularityLocalizerMorphism hP).localizedFunctor (SingularityCategory.Q E)
      (SingularityCategory.Q E'))).inv ℤ)

@[reassoc]
theorem mapSingularityCategoryFactors_hom_naturality {X Y : E.BoundedDerivedCategory}
    (f : X ⟶ Y) :
    (hF.mapSingularityCategory hP).map ((SingularityCategory.Q E).map f) ≫
        (hF.mapSingularityCategoryFactors hP).hom.app Y =
      (hF.mapSingularityCategoryFactors hP).hom.app X ≫
        (SingularityCategory.Q E').map (hF.mapBoundedDerivedCategory.map f) :=
  (hF.mapSingularityCategoryFactors hP).hom.naturality f

/-- The functor `D_sg(E) ⥤ D_sg(E')` preserves connecting morphisms of conflations. -/
@[reassoc]
theorem mapSingularityCategory_map_conflationδ {S : ShortComplex C} (hS : E.Conflation S) :
    (hF.mapSingularityCategory hP).map ((SingularityCategory.Q E).map
        (BoundedDerivedCategory.conflationδ hS)) ≫
      (hF.mapSingularityCategory hP).map
        (((SingularityCategory.Q E).commShiftIso (1 : ℤ)).hom.app _) ≫
      ((hF.mapSingularityCategory hP).commShiftIso (1 : ℤ)).hom.app _ ≫
      ((hF.mapSingularityCategoryFactors hP).hom.app _)⟦(1 : ℤ)⟧' ≫
      ((SingularityCategory.Q E').map
        ((hF.mapBoundedDerivedCategorySingleFunctorIso 0).hom.app S.X₁))⟦(1 : ℤ)⟧' =
    (hF.mapSingularityCategoryFactors hP).hom.app _ ≫ (SingularityCategory.Q E').map
      ((hF.mapBoundedDerivedCategorySingleFunctorIso 0).hom.app S.X₃) ≫
      (SingularityCategory.Q E').map (BoundedDerivedCategory.conflationδ (hF.map_conflation hS)) ≫
      ((SingularityCategory.Q E').commShiftIso (1 : ℤ)).hom.app _ := by
  have h := NatTrans.shift_app_comm (hF.mapSingularityCategoryFactors hP).hom (1 : ℤ)
    ((BoundedDerivedCategory.Q E).obj ((HomotopyCategory.Bounded.singleFunctor C 0).obj S.X₁))
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at h
  simp only [Functor.comp_obj, Category.assoc] at h
  rw [← Functor.map_comp_assoc (SingularityCategory.Q E'),
    ← hF.mapBoundedDerivedCategory_map_conflationδ hS]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% h,
    mapSingularityCategoryFactors_hom_naturality_assoc, ← Functor.commShiftIso_hom_naturality,
    Functor.comp_obj, ShortComplex.map_X₁]

/-- The functor `hF.mapSingularityCategory hP` commutes with placing an object in degree zero. -/
noncomputable def singleToSingularityCompMapSingularityCategoryIso :
    E.singleToSingularity ⋙ hF.mapSingularityCategory hP ≅ F ⋙ E'.singleToSingularity :=
  Functor.isoWhiskerRight (eqToIso E.singleToSingularity_eq) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (hF.mapSingularityCategoryFactors hP) ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Functor.associator _ _ _).symm ≪≫
      hF.mapBoundedDerivedCategorySingleFunctorIso 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (Functor.associator _ _ _ ≪≫ eqToIso E'.singleToSingularity_eq.symm)

theorem singleToSingularityCompMapSingularityCategoryIso_hom_app (X : C) :
    (hF.singleToSingularityCompMapSingularityCategoryIso hP).hom.app X =
      (hF.mapSingularityCategory hP).map (eqToHom (E.singleToSingularity_obj X)) ≫
        (hF.mapSingularityCategoryFactors hP).hom.app _ ≫
        (SingularityCategory.Q E').map
          ((hF.mapBoundedDerivedCategorySingleFunctorIso 0).hom.app X) ≫
        eqToHom (E'.singleToSingularity_obj (F.obj X)).symm := by
  simp [singleToSingularityCompMapSingularityCategoryIso, eqToHom_map]

end IsConflationExact

end TauCeti.ExactStructure
