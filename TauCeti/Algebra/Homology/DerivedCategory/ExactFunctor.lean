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
# Homology of the functor induced by an exact functor on derived categories

An exact functor `F : C₁ ⥤ C₂` between abelian categories induces a functor
`F.mapDerivedCategory : D(C₁) ⥤ D(C₂)`. Taking homology commutes with it: the homology in degree
`n` of `F.mapDerivedCategory.obj K` is `F` applied to the homology of `K`
(`CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`). This is the derived-category
form of `CategoryTheory.Functor.mapHomologicalComplexCompHomologyFunctorIso`; it shows for instance
that derived restriction of module sheaves to an open subscheme preserves quasi-coherence of
homology sheaves.
-/

public section

open CategoryTheory Limits DerivedCategory

universe w₁ w₂

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

namespace CategoryTheory.Functor

variable (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The homology of the functor induced by an exact functor `F` on derived categories is `F`
applied to homology. -/
noncomputable def mapDerivedCategoryCompHomologyFunctorIso (n : ℤ) :
    F.mapDerivedCategory ⋙ homologyFunctor C₂ n ≅ homologyFunctor C₁ n ⋙ F :=
  Localization.liftNatIso Q (HomologicalComplex.quasiIso C₁ (.up ℤ))
    (Q ⋙ F.mapDerivedCategory ⋙ homologyFunctor C₂ n) (Q ⋙ homologyFunctor C₁ n ⋙ F) _ _
    ((associator _ _ _).symm ≪≫ isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      associator _ _ _ ≪≫ isoWhiskerLeft _ (homologyFunctorFactors C₂ n) ≪≫
      F.mapHomologicalComplexCompHomologyFunctorIso _ n ≪≫
      isoWhiskerRight (homologyFunctorFactors C₁ n).symm F ≪≫ associator _ _ _)

/-- On a complex, `mapDerivedCategoryCompHomologyFunctorIso` is the comparison of homology of
complexes `CategoryTheory.ShortComplex.mapHomologyIso`, up to the identifications of homology in
the derived category with homology of complexes. -/
@[simp]
lemma mapDerivedCategoryCompHomologyFunctorIso_hom_app_Q_obj (n : ℤ) (K : CochainComplex C₁ ℤ) :
    (F.mapDerivedCategoryCompHomologyFunctorIso n).hom.app (Q.obj K) =
      (homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (homologyFunctorFactors C₂ n).hom.app _ ≫ ((K.sc n).mapHomologyIso F).hom ≫
          F.map ((homologyFunctorFactors C₁ n).inv.app K) := by
  simp [mapDerivedCategoryCompHomologyFunctorIso, Localization.liftNatTrans_app]

end CategoryTheory.Functor
