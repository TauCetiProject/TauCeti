/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import TauCeti.Algebra.Homology.DerivedCategory.Plus.Homology
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Basic
public import TauCeti.Algebra.Homology.Functor.Extend
import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Homology
import TauCeti.Algebra.Homology.HomotopyCategory.Plus

/-!
# Cohomology of bounded below right derived functors on objects

On an object placed in degree zero, the cohomology of the bounded below right derived functor
agrees with the ordinary right derived functors. The comparison uses the same injective
resolution on both sides, extending it by zero to negative degrees on the bounded below side.
-/

public section

noncomputable section

open CategoryTheory DerivedCategory Functor

local notation "upNat" => ComplexShape.embeddingUpNat

namespace TauCeti

variable (C : Type*) [Category* C] [Abelian C] [EnoughInjectives C]

private def injectiveResolutionPlus (X : C) : CochainComplex.Plus (InjectiveObject C) :=
  let I := (injectiveResolution X).cochainComplex
  ⟨HomologicalComplex.liftObjectProperty _ I (fun _ ↦ inferInstanceAs (Injective (I.X _))),
    0, (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
      _ (InjectiveObject.ι C) _).1 (inferInstanceAs (I.IsStrictlyGE 0))⟩

/-- The chosen injective resolutions, viewed in the bounded below homotopy category. -/
def injectiveResolutionsPlus : C ⥤ HomotopyCategory.Plus C :=
  (HomotopyCategory.plus C).lift (injectiveResolutions C ⋙ (upNat).extendHomotopyFunctor C) fun X ↦
    (HomotopyCategory.plus_quotient_obj_iff _).2 ⟨0,
      inferInstanceAs ((injectiveResolution X).cochainComplex.IsStrictlyGE 0)⟩

/-- Forgetting termwise injectivity and taking the homotopy class gives the chosen resolution. -/
private lemma injectiveResolutionsPlus_obj (X : C) :
    (HomotopyCategory.Plus.quotient C).obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj (injectiveResolutionPlus C X)) =
    (injectiveResolutionsPlus C).obj X :=
  (rfl)

/-- Forgetting the bound on the chosen injective resolutions gives extension by zero. -/
def injectiveResolutionsPlusCompιIso :
    injectiveResolutionsPlus C ⋙ HomotopyCategory.Plus.ι C ≅
      injectiveResolutions C ⋙ (upNat).extendHomotopyFunctor C :=
  Iso.refl _

variable [HasDerivedCategory C]

/-- The augmentations exhibit the chosen resolutions as the degree-zero embeddings. -/
def singleFunctorIsoInjectiveResolutionsPlus :
    Plus.singleFunctor C 0 ≅ injectiveResolutionsPlus C ⋙ Plus.Qh :=
  ((DerivedCategory.TStructure.t (C := C)).plus.fullyFaithfulι.whiskeringRight C).preimageIso
    (Plus.singleFunctorιIso C 0 ≪≫ singleFunctorIsoCompQ C 0 ≪≫
      isoWhiskerLeft _ (quotientCompQhIso C).symm ≪≫
      asIso (whiskerRight TauCeti.singleToInjectiveResolutions Qh) ≪≫
      Functor.associator (injectiveResolutionsPlus C) (HomotopyCategory.Plus.ι C) Qh ≪≫
      isoWhiskerLeft _ (Plus.QhCompιIsoιCompQh C).symm ≪≫
      (Functor.associator _ _ _).symm)

end TauCeti

namespace CategoryTheory

open TauCeti

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C] [HasDerivedCategory C]
  {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

/-- The bounded below derived unit is invertible on each chosen injective resolution. -/
instance isIso_rightDerivedFunctorPlusUnith_app_injectiveResolutionsPlus (X : C) :
    IsIso (F.rightDerivedFunctorPlusUnith.app ((injectiveResolutionsPlus C).obj X)) := by
  rw [← injectiveResolutionsPlus_obj]
  infer_instance

private instance : IsIso (whiskerLeft (injectiveResolutionsPlus C)
    F.rightDerivedFunctorPlusUnith) :=
  have (X : C) : IsIso ((whiskerLeft (injectiveResolutionsPlus C)
      F.rightDerivedFunctorPlusUnith).app X) :=
    isIso_rightDerivedFunctorPlusUnith_app_injectiveResolutionsPlus F X
  NatIso.isIso_of_isIso_app _

/-- The cohomology of the bounded below derived functor on an object in degree zero is
the classical right derived functor, naturally in that object. -/
def Functor.rightDerivedFunctorPlusHomologyIso (n : ℕ) :
    Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙ Plus.homologyFunctor D n ≅
      F.rightDerived n :=
  calc
    _ ≅ ((injectiveResolutionsPlus C ⋙ Plus.Qh) ⋙ F.rightDerivedFunctorPlus) ⋙
        Plus.homologyFunctor D n :=
      (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (isoWhiskerRight (singleFunctorIsoInjectiveResolutionsPlus C) _) _
    _ ≅ (injectiveResolutionsPlus C ⋙ F.mapHomotopyCategoryPlus ⋙ Plus.Qh) ⋙
        Plus.homologyFunctor D n :=
      isoWhiskerRight (Functor.associator _ _ _ ≪≫
        (asIso (whiskerLeft (injectiveResolutionsPlus C) F.rightDerivedFunctorPlusUnith)).symm) _
    _ ≅ injectiveResolutions C ⋙ (upNat).extendHomotopyFunctor C ⋙ F.mapHomotopyCategory _ ⋙
        HomotopyCategory.homologyFunctor D _ (n : ℤ) :=
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (
        Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Plus.homologyFunctorFactorsh D n) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight F.mapHomotopyCategoryPlusCompι _ ≪≫ Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (injectiveResolutionsPlusCompιIso C) _ ≪≫ Functor.associator _ _ _
    _ ≅ _ := isoWhiskerLeft (injectiveResolutions C)
      (isoWhiskerRight (F.mapHomotopyCategoryExtendIso upNat) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ ((upNat).extendHomotopyFunctorCompHomologyFunctorIso D (j := n) rfl)) ≪≫
      (Functor.associator _ _ _).symm

/-- The comparison is induced by the augmentation into the chosen injective resolution,
the inverse of the derived unit, and the homology comparison for extension by zero. -/
@[reassoc]
lemma Functor.rightDerivedFunctorPlusHomologyIso_hom_app (n : ℕ) (X : C) :
    let K := (injectiveResolutionsPlus C).obj X
    let I := (injectiveResolutions C).obj X
    let H := HomotopyCategory.homologyFunctor D (.up ℤ) (n : ℤ)
    (F.rightDerivedFunctorPlusHomologyIso n).hom.app X =
      (Plus.homologyFunctor D n).map
        (F.rightDerivedFunctorPlus.map ((singleFunctorIsoInjectiveResolutionsPlus C).hom.app X)) ≫
      (Plus.homologyFunctor D n).map (CategoryTheory.inv (F.rightDerivedFunctorPlusUnith.app K)) ≫
      (Plus.homologyFunctorFactorsh D n).hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
      H.map (F.mapHomotopyCategoryPlusCompι.hom.app K) ≫
      H.map ((F.mapHomotopyCategory (.up ℤ)).map ((injectiveResolutionsPlusCompιIso C).hom.app X)) ≫
      H.map ((F.mapHomotopyCategoryExtendIso upNat).hom.app I) ≫
      ((upNat).extendHomotopyFunctorCompHomologyFunctorIso D (j := n) rfl).hom.app
        ((F.mapHomotopyCategory _).obj I) := by
  dsimp only
  have hunit : (asIso (whiskerLeft (injectiveResolutionsPlus C)
      F.rightDerivedFunctorPlusUnith)).inv.app X =
      CategoryTheory.inv
        (F.rightDerivedFunctorPlusUnith.app ((injectiveResolutionsPlus C).obj X)) :=
    IsIso.eq_inv_of_hom_inv_id
      ((asIso (whiskerLeft (injectiveResolutionsPlus C)
        F.rightDerivedFunctorPlusUnith)).hom_inv_id_app X)
  simp only [Functor.rightDerivedFunctorPlusHomologyIso, Trans.trans, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.comp_obj, hunit, Category.id_comp,
    Category.comp_id, Category.assoc]
  dsimp only [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory, Functor.comp_obj]

variable {F} {G : C ⥤ D} [G.Additive]

private lemma inv_unith_app_naturality (τ : F ⟶ G) (X : C) :
    let K := (injectiveResolutionsPlus C).obj X
    τ.rightDerivedFunctorPlus.app (Plus.Qh.obj K) ≫
        CategoryTheory.inv (G.rightDerivedFunctorPlusUnith.app K) =
      CategoryTheory.inv (F.rightDerivedFunctorPlusUnith.app K) ≫
        Plus.Qh.map (τ.mapHomotopyCategoryPlus.app K) := by
  dsimp only
  apply (cancel_epi (F.rightDerivedFunctorPlusUnith.app ((injectiveResolutionsPlus C).obj X))).1
  simp only [NatTrans.rightDerivedFunctorPlus_fach_app_assoc, IsIso.hom_inv_id_assoc,
    IsIso.hom_inv_id, Category.comp_id]

omit [HasDerivedCategory C] [HasDerivedCategory D] in
/-- The classical derived transformation applies homology to its component on the chosen
injective resolution. -/
private lemma rightDerived_app_eq_homotopy (τ : F ⟶ G) (n : ℕ) (X : C) :
    (τ.rightDerived n).app X = (HomotopyCategory.homologyFunctor D (.up ℕ) n).map
      ((τ.mapHomotopyCategory (.up ℕ)).app ((injectiveResolutions C).obj X)) :=
  (rfl)

variable (F) in
/-- The comparison with the classical right derived functors is natural in the additive functor. -/
@[reassoc]
lemma Functor.rightDerivedFunctorPlusHomologyIso_hom_naturality (τ : F ⟶ G) (n : ℕ) :
    whiskerLeft (Plus.singleFunctor C 0)
        (whiskerRight τ.rightDerivedFunctorPlus (Plus.homologyFunctor D n)) ≫
      (G.rightDerivedFunctorPlusHomologyIso n).hom =
    (F.rightDerivedFunctorPlusHomologyIso n).hom ≫ τ.rightDerived n := by
  apply NatTrans.ext
  funext X
  let K := (injectiveResolutionsPlus C).obj X
  let I := (injectiveResolutions C).obj X
  let A := (singleFunctorIsoInjectiveResolutionsPlus C).hom.app X
  let H := Plus.homologyFunctor D n
  let Hℤ := HomotopyCategory.homologyFunctor D (.up ℤ) (n : ℤ)
  have hAugmentation := congrArg H.map (τ.rightDerivedFunctorPlus.naturality A).symm
  have hUnit := congrArg H.map (inv_unith_app_naturality τ X)
  have hLocalization := (Plus.homologyFunctorFactorsh D n).hom.naturality
    (τ.mapHomotopyCategoryPlus.app K)
  have hInclusion := congrArg Hℤ.map (τ.mapHomotopyCategoryPlusCompι_hom_app_naturality K)
  have hResolution := (τ.mapHomotopyCategory (.up ℤ)).naturality
    ((injectiveResolutionsPlusCompιIso C).hom.app X)
  have hResolutionMap := congrArg Hℤ.map hResolution.symm
  have hExtension :=
    congrArg Hℤ.map (F.mapHomotopyCategoryExtendIso_hom_app_naturality (e := upNat) τ I)
  have hHomology :=
    ((upNat).extendHomotopyFunctorCompHomologyFunctorIso D (j := n) rfl).hom.naturality
      ((τ.mapHomotopyCategory (.up ℕ)).app I)
  simp only [Functor.map_comp] at hAugmentation hUnit hInclusion hResolutionMap hExtension
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    rightDerivedFunctorPlusHomologyIso_hom_app, rightDerived_app_eq_homotopy]
  dsimp only [H, Hℤ, K, I, A, Functor.comp_obj, Functor.comp_map]
    at hAugmentation hUnit hLocalization hInclusion hResolutionMap hExtension hHomology
  dsimp only [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory, Functor.comp_obj]
  simp only [ComplexShape.embeddingUpNat_f] at hHomology
  simp only [Category.assoc]
  calc
    _ = _ := (reassoc_of% hAugmentation) _
    _ = _ := by rw [reassoc_of% hUnit]
    _ = _ := by rw [reassoc_of% hLocalization]
    _ = _ := by rw [reassoc_of% hInclusion]
    _ = _ := by rw [reassoc_of% hResolutionMap]
    _ = _ := by rw [reassoc_of% hExtension]
    _ = _ := by rw [hHomology]

end CategoryTheory
