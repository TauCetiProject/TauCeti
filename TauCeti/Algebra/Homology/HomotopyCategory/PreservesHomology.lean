/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology commutes with functors preserving homology

Let `F : C ⥤ D` be an additive functor which preserves homology, for instance an exact functor
between abelian categories. Applying `F` to a homological complex and then taking homology in
degree `i` is naturally isomorphic to taking homology first and then applying `F`
(`CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`). The same holds on the
homotopy category (`CategoryTheory.Functor.mapHomotopyCategoryCompHomologyFunctorIso`), where both
functors are induced from the homological-complex level.

These are the complex-level forms of Mathlib's `CategoryTheory.Functor.homologyFunctorIso` for
short complexes.
-/

public section

open CategoryTheory Limits

universe v v' u u'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [Preadditive C] [Preadditive D] [CategoryWithHomology C] [CategoryWithHomology D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι) (i : ι)

/-- Homology of homological complexes commutes with a functor preserving homology. -/
noncomputable def mapHomologicalComplexCompHomologyFunctorIso :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c i ≅
      HomologicalComplex.homologyFunctor C c i ⋙ F :=
  -- the short complex of `F` applied to `K` in degree `i` is `F` applied to that of `K`
  isoWhiskerLeft (HomologicalComplex.shortComplexFunctor C c i) (ShortComplex.homologyFunctorIso F)

@[simp]
lemma mapHomologicalComplexCompHomologyFunctorIso_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexCompHomologyFunctorIso c i).hom.app K =
      ((K.sc i).mapHomologyIso F).hom :=
  (rfl)

/-- Homology on the homotopy category commutes with a functor preserving homology. -/
noncomputable def mapHomotopyCategoryCompHomologyFunctorIso :
    F.mapHomotopyCategory c ⋙ HomotopyCategory.homologyFunctor D c i ≅
      HomotopyCategory.homologyFunctor C c i ⋙ F :=
  Quotient.natIsoLift _ <|
    (associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors c) _ ≪≫
      associator _ _ _ ≪≫
      isoWhiskerLeft _ (HomotopyCategory.homologyFunctorFactors D c i) ≪≫
      F.mapHomologicalComplexCompHomologyFunctorIso c i ≪≫
      isoWhiskerRight (HomotopyCategory.homologyFunctorFactors C c i).symm F ≪≫
      associator _ _ _

/-- On a complex, the comparison of `mapHomotopyCategoryCompHomologyFunctorIso` is the
homological-complex comparison, up to the identifications of homology on the homotopy category
with homology of complexes. -/
lemma mapHomotopyCategoryCompHomologyFunctorIso_hom_app (K : HomologicalComplex C c) :
    (F.mapHomotopyCategoryCompHomologyFunctorIso c i).hom.app
        ((HomotopyCategory.quotient C c).obj K) =
      (HomotopyCategory.homologyFunctorFactors D c i).hom.app
          ((F.mapHomologicalComplex c).obj K) ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso c i).hom.app K ≫
        F.map ((HomotopyCategory.homologyFunctorFactors C c i).inv.app K) := by
  -- `HomotopyCategory.quotient` is `Quotient.functor`, so `natTransLift_app` applies
  refine (Quotient.natTransLift_app _ _ _ _ K).trans ?_
  -- the associators and `mapHomotopyCategoryFactors` have identity components; the objects of
  -- these identities mix `Quotient.functor` with `HomotopyCategory.quotient`, so `simp` does not
  -- cancel them and `erw` matches them up to unfolding
  dsimp [Functor.associator, mapHomotopyCategoryFactors_hom_app]
  erw [Functor.map_id, Category.id_comp, Category.id_comp, Category.comp_id, Category.id_comp]

end CategoryTheory.Functor
