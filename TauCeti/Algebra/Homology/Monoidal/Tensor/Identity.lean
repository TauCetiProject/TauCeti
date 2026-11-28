/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import TauCeti.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Homology.Additive

/-!
# Cochain tensor comparison for the identity functor

The degreewise identity functor commutes with the tensor product of unbounded cochain
complexes through its native `mapHomologicalComplexIdIso`. This structural comparison
specializes `Functor.bifunctorCompIsoOfIsoId` and is used to normalize tensor comparisons
on derived categories.

The construction adapts the identity comparison from
[Tau Ceti PR #47483](https://github.com/TauCetiProject/TauCeti/pull/47483).
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

open CategoryTheory.Functor

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C]
  [(MonoidalCategory.curriedTensor C).Additive]
  [∀ (X : C), ((MonoidalCategory.curriedTensor C).obj X).Additive] [HasZeroObject C]
  [∀ (X₁ X₂ : GradedObject ℤ C), GradedObject.HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] Functor.preservesInitialObject_of_preservesZeroMorphisms

/-- Cochain tensor compatibility for the identity functor. -/
noncomputable def identityCochainComparison : MonoidalCategory.curriedTensor (CochainComplex C ℤ) ⋙
    (whiskeringRight _ _ _).obj ((𝟭 C).mapHomologicalComplex (.up ℤ)) ≅
  (((whiskeringLeft₂ (CochainComplex C ℤ)).obj ((𝟭 C).mapHomologicalComplex (.up ℤ))).obj
    ((𝟭 C).mapHomologicalComplex (.up ℤ))).obj
      (MonoidalCategory.curriedTensor (CochainComplex C ℤ)) :=
  ((MonoidalCategory.curriedTensor (CochainComplex C ℤ)).bifunctorCompIsoOfIsoId
    (mapHomologicalComplexIdIso C (.up ℤ))).symm

/-- The forward identity comparison applies the cochain identity isomorphism to the tensor
and its inverses to the two factors. -/
@[simp]
lemma identityCochainComparison_hom_app_app (K L : CochainComplex C ℤ) :
    ((identityCochainComparison (C := C)).hom.app K).app L =
      (mapHomologicalComplexIdIso C (.up ℤ)).hom.app (K ⊗ L) ≫
        ((mapHomologicalComplexIdIso C (.up ℤ)).inv.app K ⊗ₘ
          (mapHomologicalComplexIdIso C (.up ℤ)).inv.app L) := by
  simp [identityCochainComparison, tensorHom_def']

/-- The inverse identity comparison applies the cochain identity isomorphism to the two
factors and its inverse to their tensor. -/
@[simp]
lemma identityCochainComparison_inv_app_app (K L : CochainComplex C ℤ) :
    ((identityCochainComparison (C := C)).inv.app K).app L =
      ((mapHomologicalComplexIdIso C (.up ℤ)).hom.app K ⊗ₘ
        (mapHomologicalComplexIdIso C (.up ℤ)).hom.app L) ≫
          (mapHomologicalComplexIdIso C (.up ℤ)).inv.app (K ⊗ L) := by
  simp [identityCochainComparison, tensorHom_def]

end TauCeti
