/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import TauCeti.CategoryTheory.Functor.Currying

/-!
# Exact functors and derived tensor products

An exact additive functor commutes with derived tensor products if it commutes with cochain
tensor products and admits K-flat resolutions whose images are K-flat. The resolutions need
only resolve the first variable; the second complex is arbitrary and unbounded.

The construction uses `TauCeti.derivedTensorCounit`, the K-flat computation of that counit,
`Functor.mapDerivedCategoryFactors`, and localization on the product category. This is the
abstract comparison used when passing from modules to associated sheaves on an affine scheme.

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX).
* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe w₁ w₂

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory C] [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory.{w₁} C]
  {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ D), GradedObject.HasTensor X₁ X₂]
  [∀ X, PreservesColimit (Functor.empty.{0} D) ((MonoidalCategory.curriedTensor D).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} D) ((MonoidalCategory.curriedTensor D).flip.obj X)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory D] [(CochainComplex.KFlat.localizerMorphism D).IsLeftDerivabilityStructure]
  [HasDerivedCategory.{w₂} D]

namespace CategoryTheory.Functor

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

namespace MapDerivedTensor

/-- Apply the exact derived functor after the derived tensor product. -/
abbrev source : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory D :=
  uncurry.obj (TauCeti.derivedTensor C) ⋙ F.mapDerivedCategory

/-- Tensor the two images under the exact derived functor. -/
abbrev target : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory D :=
  F.mapDerivedCategory.prod F.mapDerivedCategory ⋙ uncurry.obj (TauCeti.derivedTensor D)

variable (χ : uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ)) ⋙
    F.mapHomologicalComplex (.up ℤ) ≅
  (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
    uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex D ℤ)))

private abbrev tensorImage : CochainComplex C ℤ × CochainComplex C ℤ ⥤ DerivedCategory D :=
  uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ)) ⋙
    DerivedCategory.Q ⋙ F.mapDerivedCategory

private def sourceCounit :
    DerivedCategory.Q.prod DerivedCategory.Q ⋙ source F ⟶ tensorImage F :=
  whiskerRight
    (whiskeringLeft₂HomEquiv (TauCeti.derivedTensorCounit C) ≫
      (uncurryObjCompIso (MonoidalCategory.curriedTensor (CochainComplex C ℤ))
        DerivedCategory.Q).hom) F.mapDerivedCategory

private def targetCounit :
    DerivedCategory.Q.prod DerivedCategory.Q ⋙ target F ⟶ tensorImage F := by
  let e := F.mapDerivedCategoryFactors.{w₁, w₂}
  exact (isoWhiskerRight (NatIso.prod e e)
    (uncurry.obj (TauCeti.derivedTensor D))).hom ≫
  whiskerLeft ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)))
    (whiskeringLeft₂HomEquiv (TauCeti.derivedTensorCounit D) ≫
      (uncurryObjCompIso (MonoidalCategory.curriedTensor (CochainComplex D ℤ))
        DerivedCategory.Q).hom) ≫
  (isoWhiskerRight χ DerivedCategory.Q).inv ≫
  (isoWhiskerLeft (uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ)))
    F.mapDerivedCategoryFactors).inv

/-- Compute the tensor comparison directly on a left K-flat complex whose image is K-flat.
No resolution of the second input is needed. -/
def kFlatIso (K L : CochainComplex C ℤ) [K.IsKFlat]
    [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    (source F).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (target F).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  F.mapDerivedCategory.mapIso (CochainComplex.derivedTensorKFlatLeftIso K L) ≪≫
    F.mapDerivedCategoryFactors.app (K ⊗ L) ≪≫ DerivedCategory.Q.mapIso (χ.app (K, L)) ≪≫
    (CochainComplex.derivedTensorKFlatLeftIso
      ((F.mapHomologicalComplex (.up ℤ)).obj K)
      ((F.mapHomologicalComplex (.up ℤ)).obj L)).symm ≪≫
    ((TauCeti.derivedTensor D).mapIso (F.mapDerivedCategoryFactors.app K).symm).app _ ≪≫
    ((TauCeti.derivedTensor D).obj _).mapIso (F.mapDerivedCategoryFactors.app L).symm

/-- The forward map of the K-flat comparison, expressed using the two tensor counits and
the exact-functor and cochain comparison isomorphisms. -/
@[simp]
lemma kFlatIso_hom (K L : CochainComplex C ℤ) [K.IsKFlat]
    [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    (kFlatIso F χ K L).hom =
      F.mapDerivedCategory.map (CochainComplex.derivedTensorKFlatLeftIso K L).hom ≫
        F.mapDerivedCategoryFactors.hom.app (K ⊗ L) ≫ DerivedCategory.Q.map (χ.hom.app (K, L)) ≫
        (CochainComplex.derivedTensorKFlatLeftIso
          ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L)).inv ≫
        ((TauCeti.derivedTensor D).map (F.mapDerivedCategoryFactors.inv.app K)).app _ ≫
        ((TauCeti.derivedTensor D).obj _).map (F.mapDerivedCategoryFactors.inv.app L) := (rfl)

private instance targetCounit_app_isIso (K L : CochainComplex C ℤ)
    [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    IsIso ((targetCounit F χ).app (K, L)) := by
  dsimp [targetCounit, whiskeringLeft₂HomEquiv]
  infer_instance

private lemma kFlatIso_hom_comp_targetCounit (K L : CochainComplex C ℤ) [K.IsKFlat]
    [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    (kFlatIso F χ K L).hom ≫ (targetCounit F χ).app (K, L) =
      (sourceCounit F).app (K, L) := by
  simp [kFlatIso, targetCounit, sourceCounit, whiskeringLeft₂HomEquiv,
    uncurry_obj_map, Category.assoc]

variable (P : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (ε : P ⟶ 𝟭 _)
  [∀ K, QuasiIso (ε.app K)] [∀ K, (P.obj K).IsKFlat]
  [∀ K, CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj (P.obj K))]

private def augmentation (G : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory D) :
    (P.prod (𝟭 _)) ⋙ DerivedCategory.Q.prod DerivedCategory.Q ⋙ G ⟶
      DerivedCategory.Q.prod DerivedCategory.Q ⋙ G :=
  whiskerRight ((whiskerRight ε DerivedCategory.Q).prod (𝟙 DerivedCategory.Q)) G

private instance augmentation_isIso
    (G : DerivedCategory C × DerivedCategory C ⥤ DerivedCategory D) :
    IsIso (augmentation P ε G) := by
  have (K : CochainComplex C ℤ × CochainComplex C ℤ) :
      IsIso ((augmentation P ε G).app K) := by
    have : IsIso ((NatTrans.prod (whiskerRight ε DerivedCategory.Q)
        (𝟙 DerivedCategory.Q)).app K) := by
      apply (isIso_prod_iff _ _).2
      constructor <;> dsimp <;> infer_instance
    exact G.map_isIso _
  exact NatIso.isIso_of_isIso_app _

private instance sourceCounit_isIso :
    IsIso (whiskerLeft (P.prod (𝟭 _)) (sourceCounit F)) := by
  have (K : CochainComplex C ℤ × CochainComplex C ℤ) :
      IsIso ((whiskerLeft (P.prod (𝟭 _)) (sourceCounit F)).app K) := by
    dsimp [sourceCounit, whiskeringLeft₂HomEquiv]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private instance targetCounit_isIso :
    IsIso (whiskerLeft (P.prod (𝟭 _)) (targetCounit F χ)) := by
  have (K : CochainComplex C ℤ × CochainComplex C ℤ) :
      IsIso ((whiskerLeft (P.prod (𝟭 _)) (targetCounit F χ)).app K) := by
    exact targetCounit_app_isIso F χ _ _
  exact NatIso.isIso_of_isIso_app _

private def modelIso :
    DerivedCategory.Q.prod DerivedCategory.Q ⋙ source F ≅
      DerivedCategory.Q.prod DerivedCategory.Q ⋙ target F :=
  (asIso (augmentation P ε (source F))).symm ≪≫
    asIso (whiskerLeft (P.prod (𝟭 _)) (sourceCounit F)) ≪≫
    (asIso (whiskerLeft (P.prod (𝟭 _)) (targetCounit F χ))).symm ≪≫
    asIso (augmentation P ε (target F))

private lemma modelIso_hom_comp_targetCounit (K L : CochainComplex C ℤ) :
    (modelIso F χ P ε).hom.app (K, L) ≫ (targetCounit F χ).app (K, L) =
      (sourceCounit F).app (K, L) := by
  have hs := (sourceCounit F).naturality
    ((ε.app K, 𝟙 L) : (P.obj K, L) ⟶ (K, L))
  have ht := (targetCounit F χ).naturality
    ((ε.app K, 𝟙 L) : (P.obj K, L) ⟶ (K, L))
  dsimp [modelIso]
  simp only [NatIso.isIso_inv_app, whiskerLeft_app, Category.assoc]
  rw [← cancel_epi ((augmentation P ε (source F)).app (K, L))]
  simp only [IsIso.hom_inv_id_assoc]
  dsimp [augmentation] at *
  simp only [Functor.map_id, Category.comp_id] at hs ht ⊢
  rw [hs, ht]
  simp

end MapDerivedTensor

open MapDerivedTensor

variable (χ : uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex C ℤ)) ⋙
    F.mapHomologicalComplex (.up ℤ) ≅
  (F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ)) ⋙
    uncurry.obj (MonoidalCategory.curriedTensor (CochainComplex D ℤ)))
  (P : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (ε : P ⟶ 𝟭 _)
  [∀ K, QuasiIso (ε.app K)] [∀ K, (P.obj K).IsKFlat]
  [∀ K, CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj (P.obj K))]

/-- An exact functor commutes with unbounded derived tensor products when supplied with a
cochain tensor comparison and functorial resolutions which are K-flat before and after mapping.
The comparison is natural in both derived inputs. -/
def mapDerivedTensorIso : source F ≅ target F :=
  Localization.liftNatIso (DerivedCategory.Q.prod DerivedCategory.Q)
    ((quasiIso C (.up ℤ)).prod (quasiIso C (.up ℤ))) _ _ _ _ (modelIso F χ P ε)

private lemma mapDerivedTensorIso_hom_app_Q (K L : CochainComplex C ℤ) :
    (F.mapDerivedTensorIso χ P ε).hom.app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (modelIso F χ P ε).hom.app (K, L) := by
  simpa [mapDerivedTensorIso, Localization.Lifting.iso] using
    (Localization.liftNatTrans_app (DerivedCategory.Q.prod DerivedCategory.Q)
      ((quasiIso C (.up ℤ)).prod (quasiIso C (.up ℤ))) _ _ (source F) (target F)
      (modelIso F χ P ε).hom (K, L))

/-- When the left representative and its image are K-flat, the comparison is given by the
source and target K-flat tensor isomorphisms and the supplied cochain comparison. -/
@[simp]
lemma mapDerivedTensorIso_app_of_isKFlat (K L : CochainComplex C ℤ) [K.IsKFlat]
    [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    (F.mapDerivedTensorIso χ P ε).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      kFlatIso F χ K L := by
  apply Iso.ext
  rw [Iso.app_hom, mapDerivedTensorIso_hom_app_Q]
  rw [← cancel_mono ((targetCounit F χ).app (K, L)),
    modelIso_hom_comp_targetCounit, kFlatIso_hom_comp_targetCounit]

/-- On cochain representatives the comparison is computed by resolving the first input,
using the K-flat tensor comparison there, and transporting along the augmentation. -/
lemma mapDerivedTensorIso_app_Q (K L : CochainComplex C ℤ) :
    let a : (DerivedCategory.Q.obj (P.obj K), DerivedCategory.Q.obj L) ≅
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
      (asIso (DerivedCategory.Q.map (ε.app K))).prod (Iso.refl _)
    (F.mapDerivedTensorIso χ P ε).app (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      ((source F).mapIso a).symm ≪≫ kFlatIso F χ (P.obj K) L ≪≫ (target F).mapIso a := by
  intro a
  apply Iso.ext
  rw [Iso.app_hom, ← cancel_epi ((source F).map a.hom),
    (F.mapDerivedTensorIso χ P ε).hom.naturality a.hom]
  simp only [Iso.trans_hom, Iso.symm_hom, mapIso_hom, mapIso_inv, ← Iso.app_hom,
    mapDerivedTensorIso_app_of_isKFlat]
  rw [← map_comp_assoc, a.hom_inv_id, map_id, Category.id_comp]

/-- The natural derived tensor comparison is independent of the supplied functorial K-flat
resolution and its augmentation, for a fixed cochain tensor comparison. -/
lemma mapDerivedTensorIso_eq
    (P' : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (ε' : P' ⟶ 𝟭 _)
    [∀ K, QuasiIso (ε'.app K)] [∀ K, (P'.obj K).IsKFlat]
    [∀ K, CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj (P'.obj K))] :
    F.mapDerivedTensorIso χ P ε = F.mapDerivedTensorIso χ P' ε' := by
  apply Iso.ext
  apply Localization.natTrans_ext (DerivedCategory.Q.prod DerivedCategory.Q)
    ((quasiIso C (.up ℤ)).prod (quasiIso C (.up ℤ)))
  rintro ⟨K, L⟩
  let a : (DerivedCategory.Q.obj (P'.obj K), DerivedCategory.Q.obj L) ≅
      (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
    (asIso (DerivedCategory.Q.map (ε'.app K))).prod (Iso.refl (DerivedCategory.Q.obj L))
  have h : (F.mapDerivedTensorIso χ P ε).hom.app
        (DerivedCategory.Q.obj (P'.obj K), DerivedCategory.Q.obj L) =
      (F.mapDerivedTensorIso χ P' ε').hom.app
        (DerivedCategory.Q.obj (P'.obj K), DerivedCategory.Q.obj L) := by
    simpa only [Iso.app_hom] using congrArg Iso.hom
      ((F.mapDerivedTensorIso_app_of_isKFlat χ P ε (P'.obj K) L).trans
        (F.mapDerivedTensorIso_app_of_isKFlat χ P' ε' (P'.obj K) L).symm)
  simp only [Functor.prod_obj]
  rw [← cancel_epi ((source F).map a.hom),
    (F.mapDerivedTensorIso χ P ε).hom.naturality a.hom,
    (F.mapDerivedTensorIso χ P' ε').hom.naturality a.hom, h]

end CategoryTheory.Functor
