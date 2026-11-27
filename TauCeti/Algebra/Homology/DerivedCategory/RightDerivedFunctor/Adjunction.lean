/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import TauCeti.Algebra.Homology.DerivedCategory.ExactFunctor
public import TauCeti.Algebra.Homology.HomotopyCategory.Adjunction
public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Basic

/-!
# The derived adjunction of an exact left adjoint

Let `F : D ⥤ C` be an exact functor between abelian categories with a right adjoint `G`, where
every complex in `C` has a K-injective replacement. This file shows that the functor
`F.mapDerivedCategory` induced by `F` on unbounded derived categories is left adjoint to the
unbounded right derived functor `G.rightDerivedFunctor`
(`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedFunctor`). On a complex `K` its unit is
the composite of the unit `K ⟶ G(F(K))` of the adjunction and the comparison
`G(F(K)) ⟶ RG(F(K))` (`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedFunctor_unit_app`),
and on a complex `L` its counit, precomposed with the comparison `F(G(L)) ⟶ F(RG(L))`, is the counit
`F(G(L)) ⟶ L` of the adjunction
(`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedFunctor_counit_app`).
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

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasKInjectiveResolutions C]
  {F : D ⥤ C} {G : C ⥤ D} [F.Additive] [G.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] (adj : F ⊣ G)

private lemma isLeftDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor :
    (F.mapDerivedCategory ⋙ G.rightDerivedFunctor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctor)
      (HomotopyCategory.quasiIso D (.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.quasiIso D (.up ℤ)) _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactorsh G.rightDerivedFunctor)

/-- **The derived adjunction of an exact left adjoint.** If `F : D ⥤ C` is exact and left adjoint
to `G`, then the functor `F.mapDerivedCategory` induced by `F` on unbounded derived categories is
left adjoint to the right derived functor `G.rightDerivedFunctor`. -/
def mapDerivedCategoryRightDerivedFunctor : F.mapDerivedCategory ⊣ G.rightDerivedFunctor :=
  have := F.isLeftDerivedFunctor_mapDerivedCategory
  have := isLeftDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor (F := F) (G := G)
  have := G.isRightDerivedFunctor_rightDerivedFunctor_comp F.mapDerivedCategory
  (adj.mapHomotopyCategory (.up ℤ)).derived (HomotopyCategory.quasiIso D (.up ℤ))
    (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnith

/-- On the class of a complex `K`, the unit of the derived adjunction, followed by the
identification of `F.mapDerivedCategory` with `F` on homotopy categories, is the unit of the
adjunction on homotopy categories followed by the comparison `G(F(K)) ⟶ RG(F(K))`. -/
@[reassoc]
lemma mapDerivedCategoryRightDerivedFunctor_unit_app (K : HomotopyCategory D (.up ℤ)) :
    adj.mapDerivedCategoryRightDerivedFunctor.unit.app (Qh.obj K) ≫
      G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app K) =
      Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        G.rightDerivedFunctorUnith.app ((F.mapHomotopyCategory (.up ℤ)).obj K) := by
  have := F.isLeftDerivedFunctor_mapDerivedCategory
  have := isLeftDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor (F := F) (G := G)
  have := G.isRightDerivedFunctor_rightDerivedFunctor_comp F.mapDerivedCategory
  exact (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app (HomotopyCategory.quasiIso D (.up ℤ))
    F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctorUnith K

/-- On the class of a complex `L`, the comparison `G(L) ⟶ RG(L)` mapped by `F.mapDerivedCategory`,
followed by the counit of the derived adjunction, is the identification of `F.mapDerivedCategory`
with `F` on homotopy categories followed by the counit of the adjunction on homotopy categories. -/
@[reassoc]
lemma mapDerivedCategoryRightDerivedFunctor_counit_app (L : HomotopyCategory C (.up ℤ)) :
    F.mapDerivedCategory.map (G.rightDerivedFunctorUnith.app L) ≫
      adj.mapDerivedCategoryRightDerivedFunctor.counit.app (Qh.obj L) =
      F.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj L) ≫
        Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app L) := by
  have := F.isLeftDerivedFunctor_mapDerivedCategory
  have := isLeftDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor (F := F) (G := G)
  have := G.isRightDerivedFunctor_rightDerivedFunctor_comp F.mapDerivedCategory
  exact (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app (HomotopyCategory.quasiIso C (.up ℤ))
    F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctorUnith L

end Derived

end CategoryTheory.Adjunction
