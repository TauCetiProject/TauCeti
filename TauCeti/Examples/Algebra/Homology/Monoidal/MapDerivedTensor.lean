/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.MapDerivedTensor

/-!
# The identity functor and the derived tensor comparison

Supply an arbitrary functorial K-flat resolution and check that the identity functor's
comparison is the identity after the canonical identifications of its induced functors.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe w

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory C] [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory.{w} C]

private def idCochainTensorIso :
    uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ)) ⋙
        (𝟭 C).mapHomologicalComplex (.up ℤ) ≅
      ((𝟭 C).mapHomologicalComplex (.up ℤ)).prod ((𝟭 C).mapHomologicalComplex (.up ℤ)) ⋙
        uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ)) :=
  isoWhiskerLeft _ (mapHomologicalComplexIdIso C (.up ℤ)) ≪≫ Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
    (isoWhiskerRight (NatIso.prod (mapHomologicalComplexIdIso C (.up ℤ))
      (mapHomologicalComplexIdIso C (.up ℤ))) _).symm

private def idDerivedTensorIso :
    MapDerivedTensor.source (𝟭 C) ≅ MapDerivedTensor.target (𝟭 C) :=
  isoWhiskerLeft _ (mapDerivedCategoryIdIso C) ≪≫ Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
    (isoWhiskerRight (NatIso.prod (mapDerivedCategoryIdIso C)
      (mapDerivedCategoryIdIso C)) _).symm

variable (P : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (ε : P ⟶ 𝟭 _)
  [∀ K, QuasiIso (ε.app K)] [∀ K, (P.obj K).IsKFlat]

local instance (K : CochainComplex C ℤ) :
    CochainComplex.IsKFlat (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj (P.obj K)) :=
  by
    let e : ((𝟭 C).mapHomologicalComplex (.up ℤ)).obj (P.obj K) ≅ P.obj K :=
      (mapHomologicalComplexIdIso C (.up ℤ)).app (P.obj K)
    exact CochainComplex.isKFlat_of_iso e.symm

example : MapDerivedTensor.source (𝟭 C) ≅ MapDerivedTensor.target (𝟭 C) :=
  (𝟭 C).mapDerivedTensorIso idCochainTensorIso P ε

example (P' : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (ε' : P' ⟶ 𝟭 _)
    [∀ K, QuasiIso (ε'.app K)] [∀ K, (P'.obj K).IsKFlat] :
    (𝟭 C).mapDerivedTensorIso idCochainTensorIso P ε =
      (𝟭 C).mapDerivedTensorIso idCochainTensorIso P' ε' :=
  (𝟭 C).mapDerivedTensorIso_eq idCochainTensorIso P ε P' ε'

private lemma id_comparison_app_resolution (K L : CochainComplex C ℤ) :
    ((𝟭 C).mapDerivedTensorIso idCochainTensorIso P ε).app
        (DerivedCategory.Q.obj (P.obj K), DerivedCategory.Q.obj L) =
      idDerivedTensorIso.app (DerivedCategory.Q.obj (P.obj K), DerivedCategory.Q.obj L) := by
  rw [mapDerivedTensorIso_app_of_isKFlat]
  apply Iso.ext
  have hi (A : CochainComplex C ℤ) :
      (mapDerivedCategoryIdIso C).inv.app (DerivedCategory.Q.obj A) =
        DerivedCategory.Q.map ((mapHomologicalComplexIdIso C (.up ℤ)).inv.app A) ≫
          (𝟭 C).mapDerivedCategoryFactors.inv.app A := by
    rw [← cancel_mono ((mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj A))]
    rw [Iso.inv_hom_id_app, mapDerivedCategoryIdIso_hom_app]
    simp [← map_comp]
  have h₁ := (mapDerivedCategoryIdIso C).hom.naturality
    (((TauCeti.derivedTensorCounit C).app (P.obj K)).app L)
  have h₂ := (whiskeringLeft₂HomEquiv (TauCeti.derivedTensorCounit C)).naturality
    (((mapHomologicalComplexIdIso C (.up ℤ)).inv.app (P.obj K),
      (mapHomologicalComplexIdIso C (.up ℤ)).inv.app L) :
      (P.obj K, L) ⟶ (_, _))
  dsimp [whiskeringLeft₂HomEquiv] at h₁ h₂
  simp only [mapDerivedCategoryIdIso_hom_app, Category.assoc] at h₁ h₂
  simp only [MapDerivedTensor.kFlatIso_hom]
  simp only [comp_obj, uncurry_obj_obj, prod_obj,
    CochainComplex.derivedTensorKFlatLeftIso_hom, whiskeringRight_obj_obj,
    MonoidalCategory.curriedTensor_obj_obj, idCochainTensorIso, Iso.trans_hom,
    isoWhiskerLeft_hom, Iso.symm_hom, isoWhiskerRight_inv, NatIso.prod_inv,
    NatTrans.comp_app, id_obj, whiskerLeft_app, rightUnitor_hom_app, leftUnitor_inv_app,
    whiskerRight_app, uncurry_obj_map, NatTrans.prod_app_fst,
    MonoidalCategory.curriedTensor_map_app, NatTrans.prod_app_snd,
    MonoidalCategory.curriedTensor_obj_map, Category.id_comp, map_comp,
    CochainComplex.derivedTensorKFlatLeftIso_inv, whiskeringLeft₂_obj_obj_obj_obj_obj,
    Category.assoc, idDerivedTensorIso, NatIso.trans_app, Iso.app_hom, hi]
  rw [reassoc_of% h₁, ← reassoc_of% h₂]
  simp [← NatTrans.naturality_assoc]

example : (𝟭 C).mapDerivedTensorIso idCochainTensorIso P ε = idDerivedTensorIso := by
  apply Iso.ext
  apply Localization.natTrans_ext (DerivedCategory.Q.prod DerivedCategory.Q)
    ((quasiIso C (.up ℤ)).prod (quasiIso C (.up ℤ)))
  rintro ⟨K, L⟩
  let a : (DerivedCategory.Q.obj (P.obj K), DerivedCategory.Q.obj L) ≅
      (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
    (asIso (DerivedCategory.Q.map (ε.app K))).prod (Iso.refl _)
  simp only [Functor.prod_obj]
  rw [← cancel_epi ((MapDerivedTensor.source (𝟭 C)).map a.hom),
    ((𝟭 C).mapDerivedTensorIso idCochainTensorIso P ε).hom.naturality a.hom,
    idDerivedTensorIso.hom.naturality a.hom]
  simp only [← Iso.app_hom, id_comparison_app_resolution]
