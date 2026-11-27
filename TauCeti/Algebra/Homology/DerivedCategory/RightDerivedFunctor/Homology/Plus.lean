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

/-- The chosen injective resolutions, viewed in the bounded below homotopy category. -/
def injectiveResolutionsPlus : C ⥤ HomotopyCategory.Plus C :=
  (HomotopyCategory.plus C).lift (injectiveResolutions C ⋙ (upNat).extendHomotopyFunctor C) fun X ↦
    (HomotopyCategory.plus_quotient_obj_iff _).2 ⟨0,
      inferInstanceAs ((injectiveResolution X).cochainComplex.IsStrictlyGE 0)⟩

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
  let I := (injectiveResolution X).cochainComplex
  let K : CochainComplex.Plus (InjectiveObject C) :=
    ⟨HomologicalComplex.liftObjectProperty _ I (fun _ ↦ inferInstanceAs (Injective (I.X _))),
      0, (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff
        _ (InjectiveObject.ι C) _).1 (inferInstanceAs (I.IsStrictlyGE 0))⟩
  -- Forgetting the termwise injectivity of K recovers the extended resolution I.
  have hK : (HomotopyCategory.Plus.quotient C).obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj K) =
      (injectiveResolutionsPlus C).obj X := rfl
  rw [← hK]
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
    Functor.whiskerRight_app, hunit, Category.id_comp, Category.comp_id, Category.assoc]
  -- The composite map on `(injectiveResolutionsPlusCompιIso C).hom.app X` is the
  -- successive application of the mapped homotopy functor and homology.
  rfl

variable {F} {G : C ⥤ D} [G.Additive]

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
  have : IsIso (F.rightDerivedFunctorPlusUnith.app K) :=
    isIso_rightDerivedFunctorPlusUnith_app_injectiveResolutionsPlus F X
  have : IsIso (G.rightDerivedFunctorPlusUnith.app K) :=
    isIso_rightDerivedFunctorPlusUnith_app_injectiveResolutionsPlus G X
  let A := (singleFunctorIsoInjectiveResolutionsPlus C).hom.app X
  let H := Plus.homologyFunctor D n
  let Hℤ := HomotopyCategory.homologyFunctor D (.up ℤ) (n : ℤ)
  let Hℕ := HomotopyCategory.homologyFunctor D (.up ℕ) n
  have hA := congrArg H.map (τ.rightDerivedFunctorPlus.naturality A).symm
  have hU :
      τ.rightDerivedFunctorPlus.app (Plus.Qh.obj K) ≫
        CategoryTheory.inv (G.rightDerivedFunctorPlusUnith.app K) =
        CategoryTheory.inv (F.rightDerivedFunctorPlusUnith.app K) ≫
          Plus.Qh.map (τ.mapHomotopyCategoryPlus.app K) := by
    apply (cancel_epi (F.rightDerivedFunctorPlusUnith.app K)).1
    simp only [NatTrans.rightDerivedFunctorPlus_fach_app_assoc, IsIso.hom_inv_id_assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have hH := (Plus.homologyFunctorFactorsh D n).hom.naturality
    (τ.mapHomotopyCategoryPlus.app K)
  have hK := (τ.mapHomotopyCategory (.up ℤ)).naturality
    ((injectiveResolutionsPlusCompιIso C).hom.app X)
  have hE := congrArg Hℤ.map (F.mapHomotopyCategoryExtendIso_hom_app_naturality (e := upNat) τ I)
  have hN := ((upNat).extendHomotopyFunctorCompHomologyFunctorIso D (j := n) rfl).hom.naturality
    ((τ.mapHomotopyCategory (.up ℕ)).app I)
  simp only [Functor.comp_map] at hH hN
  have hU' := congrArg H.map hU
  have hι := congrArg Hℤ.map (τ.mapHomotopyCategoryPlusCompι_hom_app_naturality K)
  have hK' := congrArg Hℤ.map hK.symm
  simp only [Functor.map_comp] at hA hU' hι hK' hE
  have hR : (τ.rightDerived n).app X = Hℕ.map ((τ.mapHomotopyCategory (.up ℕ)).app I) := by
    dsimp only [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory,
      whiskerRight, whiskerLeft, Hℕ, I]
    rfl
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    rightDerivedFunctorPlusHomologyIso_hom_app, hR]
  -- The squares use composite functor objects for the images of the resolution under
  -- `Plus.Qh`, `Plus.ι` and extension by zero. The component formula uses nested
  -- applications. Extension by zero sends the index `n` to `(n : ℤ)`.
  erw [reassoc_of% hA, reassoc_of% hU', reassoc_of% hH, reassoc_of% hι,
    reassoc_of% hK', reassoc_of% hE, hN]
  -- Reassociate across the target `(G.rightDerived n).obj X`, which is the
  -- homology of the chosen resolution after applying `G`.
  repeat' erw [Category.assoc]
  rfl

end CategoryTheory
