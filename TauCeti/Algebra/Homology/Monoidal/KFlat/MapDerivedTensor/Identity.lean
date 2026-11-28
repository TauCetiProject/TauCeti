/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.MapDerivedTensor.Basic
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Identity

/-!
# The canonical derived tensor comparison for the identity functor

The canonical comparison for the identity functor equals the structural comparison induced
by `mapDerivedCategoryIdIso`. In particular, it is invertible without any chosen resolution.
Both the cochain and derived structural comparisons specialize
`Functor.bifunctorCompIsoOfIsoId`.

The identity law adapts the counit-naturality argument in
[Tau Ceti PR #47483](https://github.com/TauCetiProject/TauCeti/pull/47483), itself adapted
from [PR #47457](https://github.com/TauCetiProject/TauCeti/pull/47457).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits HomologicalComplex
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

namespace TauCeti

/-- The structural identity comparison on the derived tensor bifunctor. -/
def identityDerivedComparison : derivedTensorOfMap (𝟭 C) ≅ mapDerivedTensor (𝟭 C) :=
  (TauCeti.derivedTensor C).bifunctorCompIsoOfIsoId (mapDerivedCategoryIdIso C)

/-- Component formula for the structural identity comparison on derived tensors. -/
@[simp]
lemma identityDerivedComparison_hom_app_app (X Y : DerivedCategory C) :
    ((identityDerivedComparison (C := C)).hom.app X).app Y =
      ((derivedTensor C).map ((mapDerivedCategoryIdIso C).hom.app X)).app _ ≫
        ((derivedTensor C).obj X).map ((mapDerivedCategoryIdIso C).hom.app Y) ≫
        (mapDerivedCategoryIdIso C).inv.app (((derivedTensor C).obj X).obj Y) := by
  simp [identityDerivedComparison]

/-- Component formula for the inverse structural identity comparison on derived tensors. -/
@[simp]
lemma identityDerivedComparison_inv_app_app (X Y : DerivedCategory C) :
    ((identityDerivedComparison (C := C)).inv.app X).app Y =
      (mapDerivedCategoryIdIso C).hom.app (((derivedTensor C).obj X).obj Y) ≫
        ((derivedTensor C).obj X).map ((mapDerivedCategoryIdIso C).inv.app Y) ≫
        ((derivedTensor C).map ((mapDerivedCategoryIdIso C).inv.app X)).app _ := by
  simp [identityDerivedComparison]

end TauCeti

namespace CategoryTheory.Functor

/-- The canonical comparison for the identity functor is the structural identity comparison. -/
@[simp]
lemma mapDerivedTensorComparison_id :
    (𝟭 C).mapDerivedTensorComparison (TauCeti.identityCochainComparison (C := C)).inv =
      (TauCeti.identityDerivedComparison (C := C)).hom := by
  symm
  apply mapDerivedTensorComparison_unique
  intro K L
  let e := mapHomologicalComplexIdIso C (.up ℤ)
  let T := TauCeti.derivedTensor C
  let ε := TauCeti.derivedTensorCounit C
  -- First transport the tensor counit along the derived identity isomorphism.
  have h₁ :
      (𝟭 C).mapDerivedCategory.map ((ε.app K).app L) ≫
          (mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj (K ⊗ L)) =
        (mapDerivedCategoryIdIso C).hom.app
          ((T.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L)) ≫
          (ε.app K).app L :=
    (mapDerivedCategoryIdIso C).hom.naturality ((ε.app K).app L)
  -- Then apply tensor counit naturality in each cochain variable.
  have h₂ :
      (T.map (DerivedCategory.Q.map (e.hom.app K))).app _ ≫
          (ε.app K).app (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj L) =
        (ε.app (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K)).app _ ≫
          DerivedCategory.Q.map (e.hom.app K ▷ _) :=
    NatTrans.congr_app (ε.naturality (e.hom.app K))
      (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj L)
  have h₃ :
      (T.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map (e.hom.app L)) ≫
          (ε.app K).app L =
        (ε.app K).app (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj L) ≫
          DerivedCategory.Q.map (K ◁ e.hom.app L) :=
    (ε.app K).naturality (e.hom.app L)
  have hc :
      (T.map (DerivedCategory.Q.map (e.hom.app K))).app _ ≫
          (T.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map (e.hom.app L)) ≫
          (ε.app K).app L =
        (ε.app (((𝟭 C).mapHomologicalComplex (.up ℤ)).obj K)).app _ ≫
          DerivedCategory.Q.map (e.hom.app K ⊗ₘ e.hom.app L) := by
    calc
      _ = (T.map (DerivedCategory.Q.map (e.hom.app K))).app _ ≫
          (ε.app K).app _ ≫ DerivedCategory.Q.map (K ◁ e.hom.app L) := by rw [h₃]
      _ = _ := by rw [← Category.assoc, h₂]; simp [Category.assoc, ← Functor.map_comp,
        MonoidalCategory.tensorHom_def]
  dsimp only [T, ε, e] at h₁ hc
  rw [← cancel_mono ((mapDerivedCategoryIdIso C).hom.app
    (DerivedCategory.Q.obj (K ⊗ L)))]
  simp only [TauCeti.identityDerivedComparison_hom_app_app, Category.assoc]
  rw [h₁]
  simp [Category.assoc, derivedTensorOfMapCounit_app_app, mapDerivedCategoryIdIso_hom_app,
    TauCeti.identityCochainComparison_inv_app_app, ← NatTrans.naturality_assoc, hc]

/-- The canonical identity comparison is invertible on the entire derived category. -/
instance isIso_mapDerivedTensorComparison_id : IsIso ((𝟭 C).mapDerivedTensorComparison
    (TauCeti.identityCochainComparison (C := C)).inv) := by
  rw [mapDerivedTensorComparison_id]
  infer_instance

end CategoryTheory.Functor
