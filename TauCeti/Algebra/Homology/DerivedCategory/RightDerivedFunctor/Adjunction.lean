/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Localization.Adjunction
public import TauCeti.Algebra.Homology.Adjunction
public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Basic

/-!
# The derived adjunction of an exact left adjoint

Let `F : D ⥤ C` be an exact functor between abelian categories with a right adjoint `G`, where
every complex in `C` has a K-injective replacement. This file shows that the functor
`F.mapDerivedCategory` induced by `F` on unbounded derived categories is left adjoint to the
unbounded right derived functor `G.rightDerivedFunctor`
(`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedFunctor`). On a complex `K` its unit is
the composite of the unit `K ⟶ G(F(K))` of the adjunction and the comparison
`G(F(K)) ⟶ RG(F(K))` (`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedFunctor_unit_app`).
For instance, `M ↦ M~` from `A`-modules to `𝒪_{Spec A}`-modules is exact and left adjoint to global
sections, so `D(A) ⥤ D(𝒪_{Spec A})` is left adjoint to derived global sections.

The adjunction of complexes induced by `F ⊣ G` descends to the homotopy categories
(`CategoryTheory.Adjunction.mapHomotopyCategory`), and Mathlib's `Adjunction.derived` derives it:
`F.mapDerivedCategory` is the localization of `F` on homotopy categories, as `F` is exact, and
`G.rightDerivedFunctor`, computed from K-injective replacements, is an absolute right derived
functor.

## References

* G. Maltsiniotis, *Le théorème de Quillen, d'adjonction des foncteurs dérivés, revisité*,
  C. R. Math. Acad. Sci. Paris 344 (2007), 549–552.
* [Stacks: Lemma 13.30.1](https://stacks.math.columbia.edu/tag/0FNC).
-/

public section

noncomputable section

open CategoryTheory DerivedCategory Limits TauCeti

universe w w' v v' u u'

namespace CategoryTheory.Adjunction

section HomotopyCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C] {D : Type u'}
  [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D] {F : D ⥤ C} {G : C ⥤ D} [F.Additive]
  [G.Additive] (adj : F ⊣ G)

/-- An additive functor induces a functor on homotopy categories compatibly with the quotient
functors. -/
private instance catCommSqMapHomotopyCategory {V W : Type*} [Category* V] [Preadditive V]
    [Category* W] [Preadditive W] (H : V ⥤ W) [H.Additive] {ι : Type*} (c : ComplexShape ι) :
    CatCommSq (H.mapHomologicalComplex c) (HomotopyCategory.quotient V c)
      (HomotopyCategory.quotient W c) (H.mapHomotopyCategory c) :=
  ⟨(H.mapHomotopyCategoryFactors c).symm⟩

/-- An adjunction between additive functors induces an adjunction between the functors they
induce on homotopy categories of cochain complexes. -/
def mapHomotopyCategory : F.mapHomotopyCategory (.up ℤ) ⊣ G.mapHomotopyCategory (.up ℤ) :=
  (adj.mapHomologicalComplex (.up ℤ)).localization (HomotopyCategory.quotient D (.up ℤ))
    (HomologicalComplex.homotopyEquivalences D (.up ℤ)) (HomotopyCategory.quotient C (.up ℤ))
    (HomologicalComplex.homotopyEquivalences C (.up ℤ)) _ _

/-- On a complex, the unit of the adjunction on homotopy categories is the class of the unit of
the adjunction on complexes, which is the unit of `F ⊣ G` in each degree. -/
lemma mapHomotopyCategory_unit_app (K : CochainComplex D ℤ) :
    adj.mapHomotopyCategory.unit.app ((HomotopyCategory.quotient D (.up ℤ)).obj K) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  simp only [mapHomotopyCategory, Adjunction.localization_unit_app, CatCommSq.iso, Iso.symm_hom]
  -- the comparisons of `quotient ⋙ mapHomotopyCategory` with `mapHomologicalComplex ⋙ quotient`
  -- are identities
  rw [show (G.mapHomotopyCategoryFactors (.up ℤ)).inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K)
      = 𝟙 _ from rfl, show (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ from rfl]
  -- the identities live over composite functors, so they are removed up to unfolding
  erw [Functor.map_id, Category.id_comp, Category.comp_id]

end HomotopyCategory

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasKInjectiveResolutions C]
  {F : D ⥤ C} {G : C ⥤ D} [F.Additive] [G.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] (adj : F ⊣ G)

omit [HasKInjectiveResolutions C] in
private lemma isLeftDerivedFunctor_mapDerivedCategory :
    F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso D (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.quasiIso D (.up ℤ)) _
    F.mapDerivedCategoryFactorsh

private lemma isLeftDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor :
    (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctor)
      (HomotopyCategory.quasiIso D (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.quasiIso D (.up ℤ)) _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactorsh G.rightDerivedFunctor)

private lemma isRightDerivedFunctor_rightDerivedFunctor_comp_mapDerivedCategory :
    (G.rightDerivedFunctor ⋙ F.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight G.rightDerivedFunctorUnith F.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso C (.up ℤ)) := by
  -- the right derived functor is computed by K-injective replacements, which is an absolute
  -- right derived functor
  let H := G.mapHomotopyCategory (.up ℤ) ⋙ Qh ⋙ F.mapDerivedCategory
  have := (kInjectiveReplacementAdjunction C).isRightDerivedFunctor_whiskerRightUnit H
    (HomotopyCategory.quasiIso C (.up ℤ))
  refine (Functor.isRightDerivedFunctor_iff_of_iso _ _ _
    (Functor.isoWhiskerRight G.rightDerivedFunctorIsoKInjectiveReplacement.symm
      F.mapDerivedCategory) ?_).1 this
  ext X
  simp [H, Functor.rightDerivedFunctorUnith_app]

/-- **The derived adjunction of an exact left adjoint.** If `F : D ⥤ C` is exact and left adjoint
to `G`, then the functor `F.mapDerivedCategory` induced by `F` on unbounded derived categories is
left adjoint to the right derived functor `G.rightDerivedFunctor`. -/
def mapDerivedCategoryRightDerivedFunctor : F.mapDerivedCategory ⊣ G.rightDerivedFunctor :=
  have := isLeftDerivedFunctor_mapDerivedCategory (F := F)
  have := isLeftDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor (F := F) (G := G)
  have := isRightDerivedFunctor_rightDerivedFunctor_comp_mapDerivedCategory (F := F) (G := G)
  adj.mapHomotopyCategory.derived (HomotopyCategory.quasiIso D (.up ℤ))
    (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnith

/-- On the class of a complex `K`, the unit of the derived adjunction, followed by the
identification of `F.mapDerivedCategory` with `F` on homotopy categories, is the unit of the
adjunction on homotopy categories followed by the comparison `G(F(K)) ⟶ RG(F(K))`. -/
@[reassoc]
lemma mapDerivedCategoryRightDerivedFunctor_unit_app (K : HomotopyCategory D (.up ℤ)) :
    adj.mapDerivedCategoryRightDerivedFunctor.unit.app (Qh.obj K) ≫
      G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app K) =
      Qh.map (adj.mapHomotopyCategory.unit.app K) ≫
        G.rightDerivedFunctorUnith.app ((F.mapHomotopyCategory (.up ℤ)).obj K) := by
  have := isLeftDerivedFunctor_mapDerivedCategory (F := F)
  have := isLeftDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor (F := F) (G := G)
  have := isRightDerivedFunctor_rightDerivedFunctor_comp_mapDerivedCategory (F := F) (G := G)
  exact adj.mapHomotopyCategory.derivedη_fac_app (HomotopyCategory.quasiIso D (.up ℤ))
    F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctorUnith K

end Derived

end CategoryTheory.Adjunction
