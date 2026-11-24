/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.DerivedCategory.Basic
public import TauCeti.CategoryTheory.Exact.Functor
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import TauCeti.CategoryTheory.Localization.Triangulated

/-!
# Conflation-exact functors on bounded derived categories

Let `F : C ⥤ D` be a conflation-exact functor between exact categories `E` and `E'`. Applied
termwise, `F` sends acyclic complexes to acyclic complexes
(`TauCeti.ExactStructure.IsConflationExact.map_acyclic`), so the induced triangle functor
`Kᵇ(C) ⥤ Kᵇ(D)` sends `E`-acyclic bounded complexes to `E'`-acyclic ones. It therefore descends
to a triangle functor `Dᵇ(E) ⥤ Dᵇ(E')` between the bounded derived categories.

## Main definitions

* `TauCeti.ExactStructure.IsConflationExact.boundedDerivedLocalizerMorphism`: the functor
  `Kᵇ(C) ⥤ Kᵇ(D)` as a morphism of localizers for the bounded acyclic complexes.
* `TauCeti.ExactStructure.IsConflationExact.mapBoundedDerivedCategory`: the induced triangle
  functor `Dᵇ(E) ⥤ Dᵇ(E')`.
* `TauCeti.ExactStructure.IsConflationExact.mapBoundedDerivedCategoryFactors`: its composite with
  the quotient functor `Kᵇ(C) ⥤ Dᵇ(E)` is the image of `F` on bounded homotopy categories
  followed by the quotient functor, compatibly with shifts.
* `TauCeti.ExactStructure.IsConflationExact.mapBoundedDerivedCategorySingleFunctorIso`: it
  commutes with placing an object in a given degree.

## Main results

* `TauCeti.ExactStructure.IsConflationExact.acyclicBounded_le_inverseImage`: a conflation-exact
  functor preserves bounded acyclic complexes in the bounded homotopy category.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Section 10.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

namespace IsConflationExact

variable (hF : E.IsConflationExact E' F)
include hF

/-- A conflation-exact functor sends bounded acyclic complexes of `Kᵇ(C)` to bounded acyclic
complexes of `Kᵇ(D)`. -/
theorem acyclicBounded_le_inverseImage :
    E.acyclicBounded ≤ E'.acyclicBounded.inverseImage F.mapHomotopyCategoryBounded := by
  intro X hX
  obtain ⟨K, hb, ha, ⟨e⟩⟩ := (E.boundedAcyclic_iff _).1 ((E.acyclicBounded_iff X).1 hX)
  exact (E'.acyclicBounded_iff _).2 ((E'.boundedAcyclic_iff _).2
    ⟨_, F.bounded_mapHomologicalComplex hb, hF.map_acyclic ha,
      ⟨F.mapHomotopyCategoryBoundedCompι.app X ≪≫ (F.mapHomotopyCategory (.up ℤ)).mapIso e ≪≫
        (F.mapHomotopyCategoryFactors (.up ℤ)).app K⟩⟩)

/-- The functor `Kᵇ(C) ⥤ Kᵇ(D)` induced by a conflation-exact functor, as a morphism of localizers
for the bounded acyclic complexes. -/
def boundedDerivedLocalizerMorphism :
    LocalizerMorphism E.acyclicBounded.trW E'.acyclicBounded.trW where
  functor := F.mapHomotopyCategoryBounded
  map _ _ f hf := (ObjectProperty.inverseImage_trW_iff _ _ f).1
    (ObjectProperty.trW_monotone hF.acyclicBounded_le_inverseImage _ hf)

@[simp]
theorem boundedDerivedLocalizerMorphism_functor :
    hF.boundedDerivedLocalizerMorphism.functor = F.mapHomotopyCategoryBounded :=
  (rfl)

noncomputable instance : hF.boundedDerivedLocalizerMorphism.functor.CommShift ℤ :=
  inferInstanceAs (F.mapHomotopyCategoryBounded.CommShift ℤ)

instance : hF.boundedDerivedLocalizerMorphism.functor.IsTriangulated :=
  inferInstanceAs F.mapHomotopyCategoryBounded.IsTriangulated

/-- **The triangle functor `Dᵇ(E) ⥤ Dᵇ(E')` induced by a conflation-exact functor.** -/
noncomputable def mapBoundedDerivedCategory :
    E.BoundedDerivedCategory ⥤ E'.BoundedDerivedCategory :=
  hF.boundedDerivedLocalizerMorphism.localizedFunctor (BoundedDerivedCategory.Q E)
    (BoundedDerivedCategory.Q E')

noncomputable instance : hF.mapBoundedDerivedCategory.CommShift ℤ :=
  inferInstanceAs ((hF.boundedDerivedLocalizerMorphism.localizedFunctor
    (BoundedDerivedCategory.Q E) (BoundedDerivedCategory.Q E')).CommShift ℤ)

instance : hF.mapBoundedDerivedCategory.IsTriangulated :=
  LocalizerMorphism.isTriangulated_localizedFunctor _ (BoundedDerivedCategory.Q E)
    (BoundedDerivedCategory.Q E')

/-- The functor `hF.mapBoundedDerivedCategory` is induced by the functor `Kᵇ(C) ⥤ Kᵇ(D)`. -/
noncomputable def mapBoundedDerivedCategoryFactors :
    BoundedDerivedCategory.Q E ⋙ hF.mapBoundedDerivedCategory ≅
      F.mapHomotopyCategoryBounded ⋙ BoundedDerivedCategory.Q E' :=
  (CatCommSq.iso hF.boundedDerivedLocalizerMorphism.functor (BoundedDerivedCategory.Q E)
    (BoundedDerivedCategory.Q E') (hF.boundedDerivedLocalizerMorphism.localizedFunctor
      (BoundedDerivedCategory.Q E) (BoundedDerivedCategory.Q E'))).symm

instance : NatTrans.CommShift hF.mapBoundedDerivedCategoryFactors.hom ℤ :=
  have := hF.boundedDerivedLocalizerMorphism.natTransCommShift_hom (M := ℤ)
    (BoundedDerivedCategory.Q E) (BoundedDerivedCategory.Q E')
    (hF.boundedDerivedLocalizerMorphism.localizedFunctor (BoundedDerivedCategory.Q E)
      (BoundedDerivedCategory.Q E')) (CatCommSq.iso ..)
  inferInstanceAs (NatTrans.CommShift (CatCommSq.iso hF.boundedDerivedLocalizerMorphism.functor
    (BoundedDerivedCategory.Q E) (BoundedDerivedCategory.Q E')
    (hF.boundedDerivedLocalizerMorphism.localizedFunctor (BoundedDerivedCategory.Q E)
      (BoundedDerivedCategory.Q E'))).inv ℤ)

@[reassoc]
theorem mapBoundedDerivedCategoryFactors_hom_naturality {X Y : HomotopyCategory.Bounded C}
    (f : X ⟶ Y) :
    hF.mapBoundedDerivedCategory.map ((BoundedDerivedCategory.Q E).map f) ≫
        hF.mapBoundedDerivedCategoryFactors.hom.app Y =
      hF.mapBoundedDerivedCategoryFactors.hom.app X ≫
        (BoundedDerivedCategory.Q E').map (F.mapHomotopyCategoryBounded.map f) :=
  hF.mapBoundedDerivedCategoryFactors.hom.naturality f

/-- The functor `hF.mapBoundedDerivedCategory` commutes with placing an object in degree `n`. -/
noncomputable def mapBoundedDerivedCategorySingleFunctorIso (n : ℤ) :
    (HomotopyCategory.Bounded.singleFunctor C n ⋙ BoundedDerivedCategory.Q E) ⋙
        hF.mapBoundedDerivedCategory ≅
      F ⋙ HomotopyCategory.Bounded.singleFunctor D n ⋙ BoundedDerivedCategory.Q E' :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ hF.mapBoundedDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapHomotopyCategoryBoundedSingleFunctorIso n) _ ≪≫
    Functor.associator _ _ _

theorem mapBoundedDerivedCategorySingleFunctorIso_hom_app (n : ℤ) (X : C) :
    (hF.mapBoundedDerivedCategorySingleFunctorIso n).hom.app X =
      hF.mapBoundedDerivedCategoryFactors.hom.app _ ≫
        (BoundedDerivedCategory.Q E').map
          ((F.mapHomotopyCategoryBoundedSingleFunctorIso n).hom.app X) := by
  simp [mapBoundedDerivedCategorySingleFunctorIso]

end IsConflationExact

end TauCeti.ExactStructure
