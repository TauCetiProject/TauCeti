/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The canonical comparison for an exact functor and derived tensor

An exact additive functor equipped with a comparison for unbounded cochain tensor products
has a canonical morphism from the derived tensor of its images to the image of the derived
tensor. The universal property of the absolute left derived tensor defines this morphism
without choosing resolutions. Compatible K-flat replacements make it invertible.

## References

* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX).
* The construction uses Mathlib's `Functor.leftDerived₂Lift` and Tau Ceti's absolute
  left derived tensor and its K-flat computation isomorphisms.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

universe w₁ w₂

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory.{w₁} C]
variable {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D] [MonoidalPreadditive D]
  [∀ (X₁ X₂ : GradedObject ℤ D), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((MonoidalCategory.curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((MonoidalCategory.curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [BraidedCategory D]
  [(CochainComplex.KFlat.localizerMorphism D).IsLeftDerivabilityStructure]
  [HasDerivedCategory.{w₂} D]

namespace CategoryTheory.Functor

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

namespace MapDerivedTensorPointwise

/-- Apply the exact derived functor after tensoring. -/
abbrev imageTensor := TauCeti.derivedTensor C ⋙ (whiskeringRight _ _ _).obj F.mapDerivedCategory

/-- Tensor the two images under the exact derived functor. -/
abbrev tensorImages :=
  (((whiskeringLeft₂ (DerivedCategory D)).obj F.mapDerivedCategory).obj
    F.mapDerivedCategory).obj (TauCeti.derivedTensor D)

/-- The common cochain bifunctor used to compare the two tensor counits. -/
abbrev cochainImage := MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
  (whiskeringRight _ _ _).obj (DerivedCategory.Q ⋙ F.mapDerivedCategory)

/-- The absolute tensor counit after applying the exact derived functor. -/
def imageTensorCounit :
    (((whiskeringLeft₂ (DerivedCategory D)).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (imageTensor F) ⟶ cochainImage F :=
  whiskerRight (TauCeti.derivedTensorCounit C)
    ((whiskeringRight _ _ _).obj F.mapDerivedCategory)

instance : (imageTensor F).IsLeftDerivedFunctor₂ (imageTensorCounit F)
    (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) :=
  isLeftDerivedFunctor₂_comp_of_isLeftDerivedFunctor₂_tensor DerivedCategory.Q
    (Localization.inverts _ _) (TauCeti.derivedTensorCounit C) F.mapDerivedCategory

variable (χ : MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
    (whiskeringRight _ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ≅
  (((whiskeringLeft₂ (CochainComplex D ℤ)).obj (F.mapHomologicalComplex (.up ℤ))).obj
    (F.mapHomologicalComplex (.up ℤ))).obj
      (MonoidalCategory.curriedTensor (CochainComplex D ℤ)))

/-- The tensor counit of the image category, transported to the same cochain bifunctor
as `imageTensorCounit`. -/
def tensorImagesCounit :
    (((whiskeringLeft₂ (DerivedCategory D)).obj DerivedCategory.Q).obj
      DerivedCategory.Q).obj (tensorImages F) ⟶ cochainImage F := by
  let e := F.mapDerivedCategoryFactors.{w₁, w₂}
  let W := whiskeringLeft₂ (C₁ := CochainComplex C ℤ) (C₂ := CochainComplex C ℤ)
    (D₁ := DerivedCategory D) (D₂ := DerivedCategory D) (DerivedCategory D)
  exact (((W.mapIso e).app (DerivedCategory.Q ⋙ F.mapDerivedCategory)).app
      (TauCeti.derivedTensor D)).hom ≫
    (((W.obj (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)).mapIso e).app
      (TauCeti.derivedTensor D)).hom ≫
    (((whiskeringLeft₂ (DerivedCategory D)).obj (F.mapHomologicalComplex (.up ℤ))).obj
      (F.mapHomologicalComplex (.up ℤ))).map (TauCeti.derivedTensorCounit D) ≫
    whiskerRight χ.inv ((whiskeringRight _ _ _).obj DerivedCategory.Q) ≫
    whiskerLeft (MonoidalCategory.curriedTensor (CochainComplex C ℤ))
      (((whiskeringRight _ _ _).mapIso e).inv)

omit [BraidedCategory C]
  [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure] in
/-- Component formula for the transported tensor counit. -/
@[simp]
lemma tensorImagesCounit_app_app (K L : CochainComplex C ℤ) :
    ((tensorImagesCounit F χ).app K).app L =
      ((TauCeti.derivedTensor D).map (F.mapDerivedCategoryFactors.hom.app K)).app _ ≫
      ((TauCeti.derivedTensor D).obj _).map (F.mapDerivedCategoryFactors.hom.app L) ≫
      ((TauCeti.derivedTensorCounit D).app _).app _ ≫
      DerivedCategory.Q.map ((χ.inv.app K).app L) ≫
      F.mapDerivedCategoryFactors.inv.app (K ⊗ L) := (rfl)

end MapDerivedTensorPointwise

open MapDerivedTensorPointwise

variable (χ : MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
    (whiskeringRight _ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ≅
  (((whiskeringLeft₂ (CochainComplex D ℤ)).obj (F.mapHomologicalComplex (.up ℤ))).obj
    (F.mapHomologicalComplex (.up ℤ))).obj
      (MonoidalCategory.curriedTensor (CochainComplex D ℤ)))

/-- The canonical comparison from the derived tensor of the images to the image of the
unbounded derived tensor. No compatible K-flat replacement is needed to define it. -/
def mapDerivedTensorComparison : tensorImages F ⟶ imageTensor F :=
  leftDerived₂Lift (imageTensor F) (imageTensorCounit F)
    (quasiIso C (.up ℤ)) (quasiIso C (.up ℤ)) (tensorImages F) (tensorImagesCounit F χ)

/-- The canonical comparison intertwines the two tensor counits. -/
@[reassoc (attr := simp)]
lemma mapDerivedTensorComparison_fac (K L : CochainComplex C ℤ) :
    ((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L) ≫ F.mapDerivedCategory.map
        (((TauCeti.derivedTensorCounit C).app K).app L) =
      ((tensorImagesCounit F χ).app K).app L :=
  leftDerived₂_fac_app_app _ _ _ _ _ _ K L

/-- The counit equation uniquely determines the canonical comparison. -/
lemma mapDerivedTensorComparison_unique (γ : tensorImages F ⟶ imageTensor F)
    (hγ : ∀ K L : CochainComplex C ℤ,
      (γ.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        F.mapDerivedCategory.map (((TauCeti.derivedTensorCounit C).app K).app L) =
      ((tensorImagesCounit F χ).app K).app L) : γ = F.mapDerivedTensorComparison χ := by
  refine leftDerived₂_ext (LF := imageTensor F) (L₁ := DerivedCategory.Q)
    (L₂ := DerivedCategory.Q) (α := imageTensorCounit F) (W₁ := quasiIso C (.up ℤ))
    (W₂ := quasiIso C (.up ℤ)) ?_
  ext K L
  exact (hγ K L).trans (F.mapDerivedTensorComparison_fac χ K L).symm

/-- On a K-flat left model whose image is K-flat, the comparison is the composite of
ordinary cochain compatibility with the two K-flat tensor computation isomorphisms. -/
@[simp]
lemma mapDerivedTensorComparison_app_of_isKFlat (K L : CochainComplex C ℤ) [K.IsKFlat]
    [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    ((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L) =
      (((TauCeti.derivedTensor D).mapIso (F.mapDerivedCategoryFactors.app K)).app _ ≪≫
        ((TauCeti.derivedTensor D).obj _).mapIso (F.mapDerivedCategoryFactors.app L) ≪≫
        CochainComplex.derivedTensorKFlatLeftIso
          ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L) ≪≫
        DerivedCategory.Q.mapIso ((χ.app K).app L).symm ≪≫
        (F.mapDerivedCategoryFactors.app (K ⊗ L)).symm ≪≫
        F.mapDerivedCategory.mapIso (CochainComplex.derivedTensorKFlatLeftIso K L).symm).hom := by
  rw [← cancel_mono (F.mapDerivedCategory.map
    (((TauCeti.derivedTensorCounit C).app K).app L)), mapDerivedTensorComparison_fac]
  simp [Category.assoc]

/-- K-flatness of the left complex and of its image makes the canonical component invertible. -/
instance isIso_mapDerivedTensorComparison_app_of_isKFlat (K L : CochainComplex C ℤ)
    [K.IsKFlat] [CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj K)] :
    IsIso (((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
      (DerivedCategory.Q.obj L)) := by
  rw [F.mapDerivedTensorComparison_app_of_isKFlat χ K L]
  infer_instance

/-- Pointwise compatible K-flat replacements suffice for the canonical derived tensor
comparison to be an isomorphism. No functorial choice of replacements is required. -/
theorem isIso_mapDerivedTensorComparison_of_exists
    (h : ∀ K : CochainComplex C ℤ, ∃ (P : CochainComplex C ℤ) (f : P ⟶ K),
      QuasiIso f ∧ P.IsKFlat ∧
        CochainComplex.IsKFlat ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (F.mapDerivedTensorComparison χ) := by
  have hmodels (K L : CochainComplex C ℤ) :
      IsIso (((F.mapDerivedTensorComparison χ).app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L)) := by
    obtain ⟨P, f, hf, hP, hFP⟩ := h K
    let e := (asIso (DerivedCategory.Q.map f)).prod (Iso.refl (DerivedCategory.Q.obj L))
    exact (NatTrans.isIso_app_iff_of_iso
      (uncurry.map (F.mapDerivedTensorComparison χ)) e).1
      (isIso_mapDerivedTensorComparison_app_of_isKFlat F χ P L)
  have hderived (X Y : DerivedCategory C) :
      IsIso (((F.mapDerivedTensorComparison χ).app X).app Y) := by
    let e := (DerivedCategory.Q.objObjPreimageIso X).prod
      (DerivedCategory.Q.objObjPreimageIso Y)
    exact (NatTrans.isIso_app_iff_of_iso
      (uncurry.map (F.mapDerivedTensorComparison χ)) e).1 (hmodels _ _)
  have (X : DerivedCategory C) : IsIso ((F.mapDerivedTensorComparison χ).app X) :=
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

end CategoryTheory.Functor
