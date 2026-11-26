/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Homology

/-!
# Cohomology of bounded below right derived functors on objects

On an object placed in degree zero, the cohomology of the bounded below right derived functor
agrees with the ordinary right derived functors. The comparison uses the same injective
resolution on both sides, extending it by zero to negative degrees on the bounded below side.
-/

public section

noncomputable section

open CategoryTheory DerivedCategory Functor

namespace CategoryTheory

variable (C : Type*) [Category* C] [Abelian C] [EnoughInjectives C]

local notation "e" => ComplexShape.embeddingUpNat

/-- The chosen injective resolutions, viewed in the bounded below homotopy category. -/
private def injectiveResolutionsPlus : C ⥤ HomotopyCategory.Plus C :=
  (HomotopyCategory.plus C).lift (injectiveResolutions C ⋙ (e).extendHomotopyFunctor C) fun X ↦
    (HomotopyCategory.plus_quotient_obj_iff _).2 ⟨0,
      inferInstanceAs ((injectiveResolution X).cochainComplex.IsStrictlyGE 0)⟩

variable [HasDerivedCategory C]

/-- The augmentations exhibit the chosen resolutions as the degree-zero embeddings. -/
private def singleFunctorIsoInjectiveResolutionsPlus :
    Plus.singleFunctor C 0 ≅ injectiveResolutionsPlus C ⋙ Plus.Qh :=
  ((DerivedCategory.TStructure.t (C := C)).plus.fullyFaithfulι.whiskeringRight C).preimageIso
    (Plus.singleFunctorιIso C 0 ≪≫ singleFunctorIsoCompQ C 0 ≪≫
      isoWhiskerLeft _ (quotientCompQhIso C).symm ≪≫
      asIso (whiskerRight TauCeti.singleToInjectiveResolutions Qh) ≪≫
      Functor.associator (injectiveResolutionsPlus C) (HomotopyCategory.Plus.ι C) Qh ≪≫
      isoWhiskerLeft _ (Plus.QhCompιIsoιCompQh C).symm ≪≫
      (Functor.associator _ _ _).symm)

variable {C} {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

private lemma isIso_rightDerivedFunctorPlusUnith_app_injectiveResolutionsPlus (X : C) :
    IsIso (F.rightDerivedFunctorPlusUnith.app ((injectiveResolutionsPlus C).obj X)) := by
  let I := (injectiveResolution X).cochainComplex
  let K : CochainComplex.Plus (InjectiveObject C) :=
    ⟨HomologicalComplex.liftObjectProperty _ I (fun _ ↦ inferInstanceAs (Injective (I.X _))),
      0, (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
        _ (InjectiveObject.ι C) _).1 (inferInstanceAs (I.IsStrictlyGE 0))⟩
  exact inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.quotient C).obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj K))))

/-- The cohomology of the bounded below derived functor on an object in degree zero is
the classical right derived functor, naturally in that object. -/
def Functor.rightDerivedFunctorPlusHomologyIso (n : ℕ) :
    Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙ Plus.homologyFunctor D n ≅
      F.rightDerived n := by
  have (X : C) : IsIso ((whiskerLeft (injectiveResolutionsPlus C)
      F.rightDerivedFunctorPlusUnith).app X) :=
    isIso_rightDerivedFunctorPlusUnith_app_injectiveResolutionsPlus F X
  have : IsIso (whiskerLeft (injectiveResolutionsPlus C) F.rightDerivedFunctorPlusUnith) :=
    NatIso.isIso_of_isIso_app _
  calc
    _ ≅ ((injectiveResolutionsPlus C ⋙ Plus.Qh) ⋙ F.rightDerivedFunctorPlus) ⋙
        Plus.homologyFunctor D n :=
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (isoWhiskerRight (singleFunctorIsoInjectiveResolutionsPlus C) _) _
    _ ≅ (injectiveResolutionsPlus C ⋙ F.mapHomotopyCategoryPlus ⋙ Plus.Qh) ⋙
        Plus.homologyFunctor D n :=
      isoWhiskerRight (Functor.associator _ _ _ ≪≫
        (asIso (whiskerLeft (injectiveResolutionsPlus C) F.rightDerivedFunctorPlusUnith)).symm) _
    _ ≅ injectiveResolutions C ⋙ (e).extendHomotopyFunctor C ⋙ F.mapHomotopyCategory _ ⋙
        HomotopyCategory.homologyFunctor D _ (n : ℤ) :=
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (
          (Functor.associator _ _ _).symm ≪≫
          isoWhiskerRight (Plus.QhCompιIsoιCompQh D) _ ≪≫ Functor.associator _ _ _ ≪≫
          isoWhiskerLeft _ (homologyFunctorFactorsh D n)) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight F.mapHomotopyCategoryPlusCompι _ ≪≫ Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.associator _ _ _
    _ ≅ _ := isoWhiskerLeft (injectiveResolutions C)
      (isoWhiskerRight (F.mapHomotopyCategoryExtendIso e) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ ((e).extendHomotopyFunctorCompHomologyFunctorIso D (j := n) rfl)) ≪≫
      (Functor.associator _ _ _).symm

end CategoryTheory
