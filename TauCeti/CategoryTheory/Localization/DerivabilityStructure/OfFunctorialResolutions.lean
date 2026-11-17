/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions
public import TauCeti.CategoryTheory.Localization.LocalizerMorphism

/-!
# Functorial left resolutions give left derivability structures

Let `Φ : LocalizerMorphism W₁ W₂` be a morphism of localizers whose underlying functor
`Φ.functor : C₁ ⥤ C₂` is fully faithful and induces `W₁ = W₂.inverseImage Φ.functor`. Assume
that `C₂` admits functorial left resolutions in `C₁`, given by a functor `ρ : C₂ ⥤ C₁` and a
natural transformation `p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂` whose components belong to `W₂`. When `W₂` is
multiplicative and satisfies the two-out-of-three property, `Φ` is a left derivability structure
(`CategoryTheory.LocalizerMorphism.isLeftDerivabilityStructure_of_functorial_resolutions`).

This is the left-resolution dual of
`Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions` (by Joël Riou),
deduced by passing to opposite categories and applying
`CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_functorial_right_resolutions`,
`CategoryTheory.LocalizerMorphism.isConnected_rightResolution_of_functorial_resolutions`, and
`CategoryTheory.LocalizerMorphism.isRightDerivabilityStructure_of_functorial_resolutions`.

## References

* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318,
  Lemme 6.5.
* J. Riou, `Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions` and
  `Mathlib.CategoryTheory.Localization.LocalizerMorphism`.
-/

public section

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)
  {ρ : C₂ ⥤ C₁} (p : ρ ⋙ Φ.functor ⟶ 𝟭 C₂) (hp : ∀ X₂, W₂ (p.app X₂))
  (hW₁ : W₁ = W₂.inverseImage Φ.functor)

include hp in
/-- Functorial left resolutions on `C₂` induce left resolutions in the arrow category. -/
lemma hasLeftResolutions_arrow_of_functorial_resolutions :
    Φ.arrow.HasLeftResolutions :=
  fun f ↦
    ⟨{ X₁ := Arrow.mk (ρ.map f.hom)
       w := Arrow.homMk (p.app _) (p.app _) (p.naturality f.hom).symm
       hw := ⟨hp _, hp _⟩ }⟩

private def functorialLeftResolutionsOp : 𝟭 C₂ᵒᵖ ⟶ ρ.op ⋙ Φ.op.functor :=
  (Functor.opId C₂).inv ≫ NatTrans.op p ≫ (Functor.opComp ρ Φ.functor).hom

include hp in
private lemma mem_op_functorialLeftResolutionsOp_app (X : C₂ᵒᵖ) :
    W₂.op ((functorialLeftResolutionsOp Φ p).app X) := by
  simpa [functorialLeftResolutionsOp] using hp X.unop

include hW₁ in
private lemma inverseImage_op_eq :
    W₁.op = W₂.op.inverseImage Φ.op.functor := by
  ext X Y f
  simp [hW₁]

variable [Φ.functor.Full] [Φ.functor.Faithful] [W₂.HasTwoOutOfThreeProperty]

include hp hW₁

/-- A localizer morphism `Φ : LocalizerMorphism W₁ W₂` whose underlying functor is fully faithful,
with `W₁ = W₂.inverseImage Φ.functor`, is a localized equivalence whenever `C₂` admits functorial
left resolutions and `W₂` satisfies the two-out-of-three property. -/
lemma isLocalizedEquivalence_of_functorial_left_resolutions :
    Φ.IsLocalizedEquivalence :=
  (isLocalizedEquivalence_iff_op Φ).2 <|
    Φ.op.isLocalizedEquivalence_of_functorial_right_resolutions
      (functorialLeftResolutionsOp Φ p)
      (mem_op_functorialLeftResolutionsOp_app Φ p hp)
      (inverseImage_op_eq Φ hW₁)

variable [W₂.IsMultiplicative]

/-- If `Φ : LocalizerMorphism W₁ W₂` has a fully faithful underlying functor with
`W₁ = W₂.inverseImage Φ.functor`, `W₂` is multiplicative and satisfies the two-out-of-three
property, and `C₂` admits functorial left resolutions, then the category `Φ.LeftResolution X₂` of
left resolutions of any object `X₂ : C₂` is connected. -/
lemma isConnected_leftResolution_of_functorial_resolutions (X₂ : C₂) :
    letI : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
    IsConnected (Φ.LeftResolution X₂) := by
  have : W₁.IsMultiplicative := by rw [hW₁]; infer_instance
  have : IsConnected (Φ.op.RightResolution (Opposite.op X₂)) :=
    Φ.op.isConnected_rightResolution_of_functorial_resolutions
      (functorialLeftResolutionsOp Φ p)
      (mem_op_functorialLeftResolutionsOp_app Φ p hp)
      (inverseImage_op_eq Φ hW₁) (Opposite.op X₂)
  have : IsConnected (Φ.LeftResolution X₂)ᵒᵖ :=
    isConnected_of_equivalent (LeftResolution.opEquivalence Φ X₂).symm
  exact isConnected_of_isConnected_op

/-- A fully faithful localizer morphism `Φ : LocalizerMorphism W₁ W₂` with
`W₁ = W₂.inverseImage Φ.functor` that admits functorial left resolutions is a left derivability
structure whenever `W₂` is multiplicative and has the two-out-of-three property. -/
lemma isLeftDerivabilityStructure_of_functorial_resolutions :
    Φ.IsLeftDerivabilityStructure :=
  (Φ.isLeftDerivabilityStructure_iff_op).2 <|
    Φ.op.isRightDerivabilityStructure_of_functorial_resolutions
      (functorialLeftResolutionsOp Φ p)
      (mem_op_functorialLeftResolutionsOp_app Φ p hp)
      (inverseImage_op_eq Φ hW₁)

end LocalizerMorphism

end CategoryTheory
