/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Opposite-category and counit criteria for localized equivalences

For a morphism of localizers `Φ : LocalizerMorphism W₁ W₂`, this file proves:

* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_op_iff`: `Φ.op` induces an equivalence
  on localized categories if and only if `Φ` does.
* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_counit_of_counit`: dualizing
  `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit`, a localizer morphism
  admitting an inverse up to natural transformations `Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁` and
  `Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂` with components in `W₁` and `W₂` induces an equivalence on
  localized categories.

## References

* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.LocalizerMorphism

variable {C₁ : Type u₁} {C₂ : Type u₂} [Category.{v₁} C₁] [Category.{v₂} C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} (Φ : LocalizerMorphism W₁ W₂)

/-- The opposite localizer morphism `Φ.op` induces an equivalence on localized categories if and
only if `Φ` does. -/
@[simp]
lemma isLocalizedEquivalence_op_iff :
    Φ.op.IsLocalizedEquivalence ↔ Φ.IsLocalizedEquivalence := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : (Φ.functor ⋙ W₂.Q).op.IsLocalization W₁.op :=
    IsLocalizedEquivalence.isLocalization Φ.op W₂.Q.op
  rw [Functor.IsLocalization.op_iff] at this
  exact IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ W₂.Q

/-- If a localizer morphism `Φ : LocalizerMorphism W₁ W₂` admits a localizer morphism
`Ψ : LocalizerMorphism W₂ W₁` in the opposite direction together with natural transformations
`η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁` and `η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie
in `W₁` and `W₂`, then `Φ` induces an equivalence on the localized categories. -/
lemma isLocalizedEquivalence_of_counit_of_counit (Ψ : LocalizerMorphism W₂ W₁)
    (η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁) (η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂)
    (hη₁ : ∀ X₁, W₁ (η₁.app X₁)) (hη₂ : ∀ X₂, W₂ (η₂.app X₂)) :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_op_iff.1
    (Φ.op.isLocalizedEquivalence_of_unit_of_unit Ψ.op (NatTrans.op η₁) (NatTrans.op η₂)
      (fun X₁ ↦ hη₁ X₁.unop) (fun X₂ ↦ hη₂ X₂.unop))

end CategoryTheory.LocalizerMorphism
