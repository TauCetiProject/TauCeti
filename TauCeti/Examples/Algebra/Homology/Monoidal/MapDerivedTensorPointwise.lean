/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.MapDerivedTensorPointwise
public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivabilityStructure

/-!
# Identity check for the canonical derived tensor comparison

The identity functor's canonical comparison agrees with the identifications induced by
`mapDerivedCategoryIdIso`. Pointwise K-flat replacements, without a functorial choice, also
verify its invertibility. The counit-naturality identity test follows the analogous
uncurried test in [Tau Ceti PR #47457](https://github.com/TauCetiProject/TauCeti/pull/47457).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
open CategoryTheory.Functor.MapDerivedTensorPointwise
open scoped MonoidalCategory

universe w

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory.{w} C]

namespace TauCeti.Examples.DerivedTensorPointwise

/-- Cochain tensor compatibility for the identity functor. -/
def identityCochainComparison : MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
    (whiskeringRight _ _ _).obj ((𝟭 C).mapHomologicalComplex (.up ℤ)) ≅
  (((whiskeringLeft₂ (CochainComplex C ℤ)).obj ((𝟭 C).mapHomologicalComplex (.up ℤ))).obj
    ((𝟭 C).mapHomologicalComplex (.up ℤ))).obj
      (MonoidalCategory.curriedTensor (CochainComplex C ℤ)) := by
  let e := mapHomologicalComplexIdIso C (.up ℤ)
  let T := MonoidalCategory.curriedTensor (CochainComplex C ℤ)
  let W := whiskeringLeft₂ (C₁ := CochainComplex C ℤ) (C₂ := CochainComplex C ℤ)
    (D₁ := CochainComplex C ℤ) (D₂ := CochainComplex C ℤ) (CochainComplex C ℤ)
  exact isoWhiskerLeft T ((whiskeringRight _ _ _).mapIso e) ≪≫ rightUnitor T ≪≫
    ((((W.mapIso e).app ((𝟭 C).mapHomologicalComplex (.up ℤ))).app T) ≪≫
      (((W.obj (𝟭 _)).mapIso e).app T)).symm

example : IsIso ((𝟭 C).mapDerivedTensorComparison (identityCochainComparison (C := C))) := by
  apply isIso_mapDerivedTensorComparison_of_exists
  intro K
  obtain ⟨P, f, hf, hP⟩ := K.exists_quasiIso_isKFlat_of_hasLeftResolutions
  refine ⟨P, f, hf, hP, ?_⟩
  have : P.IsKFlat := hP
  exact CochainComplex.isKFlat_of_iso (K := P)
    ((mapHomologicalComplexIdIso C (.up ℤ)).app P).symm

/-- The structural identity comparison on the derived tensor bifunctor. -/
def identityDerivedComparison : tensorImages (𝟭 C) ≅ imageTensor (𝟭 C) := by
  let e := mapDerivedCategoryIdIso C
  let T := TauCeti.derivedTensor C
  let W := whiskeringLeft₂ (C₁ := DerivedCategory C) (C₂ := DerivedCategory C)
    (D₁ := DerivedCategory C) (D₂ := DerivedCategory C) (DerivedCategory C)
  exact (((W.mapIso e).app (𝟭 C).mapDerivedCategory).app T) ≪≫
    (((W.obj (𝟭 _)).mapIso e).app T) ≪≫
    (isoWhiskerLeft T ((whiskeringRight _ _ _).mapIso e) ≪≫ rightUnitor T).symm

example : (𝟭 C).mapDerivedTensorComparison (identityCochainComparison (C := C)) =
    (identityDerivedComparison (C := C)).hom := by
  symm
  apply mapDerivedTensorComparison_unique
  intro K L
  rw [← cancel_mono ((mapDerivedCategoryIdIso C).hom.app
    (DerivedCategory.Q.obj (K ⊗ L)))]
  have h₁ := (mapDerivedCategoryIdIso C).hom.naturality
    (((TauCeti.derivedTensorCounit C).app K).app L)
  have h₂ := (whiskeringLeft₂HomEquiv (TauCeti.derivedTensorCounit C)).naturality
    (((mapHomologicalComplexIdIso C (.up ℤ)).hom.app K,
      (mapHomologicalComplexIdIso C (.up ℤ)).hom.app L) : (_, _) ⟶ (K, L))
  dsimp [whiskeringLeft₂HomEquiv] at h₁ h₂
  simp only [mapDerivedCategoryIdIso_hom_app, comp_obj, id_obj, Category.assoc,
    whiskeringLeft₂_obj_obj_obj_obj_obj, whiskeringRight_obj_obj,
    MonoidalCategory.curriedTensor_obj_obj, identityDerivedComparison, Iso.trans_symm,
    Iso.trans_hom, Iso.app_hom, mapIso_hom, Iso.symm_hom, isoWhiskerLeft_inv, mapIso_inv,
    NatTrans.comp_app, rightUnitor_inv_app, whiskerLeft_app,
    whiskeringLeft₂_map_app_app_app_app, map_comp, whiskeringLeft₂_obj_map_app_app_app,
    NatTrans.id_app, whiskeringRight_map_app_app, Category.id_comp,
    identityCochainComparison, tensorImagesCounit_app_app, Iso.trans_inv, Iso.symm_inv,
    MonoidalCategory.curriedTensor_map_app, MonoidalCategory.curriedTensor_obj_map,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_map, Category.comp_id] at h₁ h₂ ⊢
  rw [h₁]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← NatTrans.naturality_assoc, ← h₂]

end TauCeti.Examples.DerivedTensorPointwise
