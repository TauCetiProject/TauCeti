/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.MapDerivedTensorPointwise

/-!
# Identity check for the canonical derived tensor comparison

The identity functor's canonical comparison agrees with the identifications induced by
`mapDerivedCategoryIdIso`, using the named library identity law. Pointwise K-flat replacements,
without a functorial choice, also verify its invertibility.
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

namespace TauCeti.Examples.DerivedTensorPointwise

example : IsIso ((𝟭 C).mapDerivedTensorComparison
    (TauCeti.identityCochainComparison (C := C)).inv) := by
  apply isIso_mapDerivedTensorComparison_of_exists_quasiIso_isKFlat_and_isKFlat_map
  intro K
  obtain ⟨P, f, hf, hP⟩ := K.exists_quasiIso_isKFlat_of_hasLeftResolutions
  refine ⟨P, f, hf, hP, ?_⟩
  exact CochainComplex.isKFlat_of_iso (K := P)
    ((mapHomologicalComplexIdIso C (.up ℤ)).app P).symm

example : (𝟭 C).mapDerivedTensorComparison (TauCeti.identityCochainComparison (C := C)).inv =
    (TauCeti.identityDerivedComparison (C := C)).hom :=
  mapDerivedTensorComparison_id

end TauCeti.Examples.DerivedTensorPointwise
