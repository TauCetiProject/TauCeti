/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Exact functors and homology on unbounded derived categories

An exact functor `F : C₁ ⥤ C₂` between abelian categories commutes naturally with
`DerivedCategory.homologyFunctor` in every degree
(`CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`), characterized on
`DerivedCategory.Q.obj K` by `mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q_obj`.

## References

* Mathlib's `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`.
* `TauCeti/Algebra/Homology/HomotopyCategory/PreservesHomology.lean`, the homotopy-category
  counterpart whose lifting pattern is followed here.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor commutes with `DerivedCategory.homologyFunctor` in every degree. -/
def mapDerivedCategoryCompHomologyFunctorIso (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n ≅
      DerivedCategory.homologyFunctor C₁ n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n)
    (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C₁ n ⋙ F)
    (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor C₂ n)
    (DerivedCategory.homologyFunctor C₁ n ⋙ F)
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryFactors (DerivedCategory.homologyFunctor C₂ n) ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (F.mapHomologicalComplex _)
        (DerivedCategory.homologyFunctorFactors C₂ n) ≪≫
      F.mapHomologicalComplexCompHomologyFunctorIso (ComplexShape.up ℤ) n ≪≫
      isoWhiskerRight (DerivedCategory.homologyFunctorFactors C₁ n).symm F ≪≫
      Functor.associator _ _ _)

/-- On a cochain complex `K`, the comparison `mapDerivedCategoryCompHomologyFunctorIso` is given by
`F.mapDerivedCategoryFactors`, `DerivedCategory.homologyFunctorFactors`, and
`F.mapHomologicalComplexCompHomologyFunctorIso`. -/
@[reassoc]
lemma mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q_obj
    (K : CochainComplex C₁ ℤ) (n : ℤ) :
    (F.mapDerivedCategoryCompHomologyFunctorIso n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex _).obj K) ≫
        (F.mapHomologicalComplexCompHomologyFunctorIso (ComplexShape.up ℤ) n).hom.app K ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K) := by
  simp [mapDerivedCategoryCompHomologyFunctorIso]

end CategoryTheory.Functor
