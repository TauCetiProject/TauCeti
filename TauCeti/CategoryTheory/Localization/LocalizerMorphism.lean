/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Localized equivalences via opposite categories and counits

For a morphism of localizers `Φ : LocalizerMorphism W₁ W₂`, being a localized equivalence is
equivalent to the opposite morphism `Φ.op` being a localized equivalence
(`CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_iff_op`). Passing to opposite categories
gives `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_counit_of_counit`, the counit dual
of `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit` from
`Mathlib.CategoryTheory.Localization.LocalizerMorphism` (by Joël Riou).

## References

* B. Kahn and G. Maltsiniotis, *Structures de dérivabilité*, Adv. Math. 218 (2008), 1286–1318.
* J. Riou, `Mathlib.CategoryTheory.Localization.LocalizerMorphism`.
-/

public section

namespace CategoryTheory

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

/-- A morphism of localizers `Φ : LocalizerMorphism W₁ W₂` is a localized equivalence if and only
if its opposite `Φ.op : LocalizerMorphism W₁.op W₂.op` is a localized equivalence. -/
lemma isLocalizedEquivalence_iff_op (Φ : LocalizerMorphism W₁ W₂) :
    Φ.IsLocalizedEquivalence ↔ Φ.op.IsLocalizedEquivalence where
  mp _ := inferInstance
  mpr _ := by
    have : (Φ.op.functor ⋙ W₂.Q.op).IsLocalization W₁.op :=
      IsLocalizedEquivalence.isLocalization Φ.op W₂.Q.op
    have : (Φ.functor ⋙ W₂.Q).IsLocalization W₁ :=
      (Functor.IsLocalization.op_iff (Φ.functor ⋙ W₂.Q) W₁).1
        (Functor.IsLocalization.of_iso W₁.op (Functor.opComp Φ.functor W₂.Q).symm)
    exact IsLocalizedEquivalence.of_isLocalization_of_isLocalization Φ W₂.Q

/-- If morphisms of localizers `Φ : LocalizerMorphism W₁ W₂` and `Ψ : LocalizerMorphism W₂ W₁`
are equipped with natural transformations `η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁` and
`η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie in `W₁` and `W₂` respectively, then `Φ`
is a localized equivalence. -/
lemma isLocalizedEquivalence_of_counit_of_counit (Φ : LocalizerMorphism W₁ W₂)
    (Ψ : LocalizerMorphism W₂ W₁)
    (η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁) (η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂)
    (hη₁ : ∀ X₁, W₁ (η₁.app X₁)) (hη₂ : ∀ X₂, W₂ (η₂.app X₂)) :
    Φ.IsLocalizedEquivalence :=
  (isLocalizedEquivalence_iff_op Φ).2 <|
    Φ.op.isLocalizedEquivalence_of_unit_of_unit Ψ.op
      ((Functor.opId C₁).inv ≫ NatTrans.op η₁ ≫ (Functor.opComp Φ.functor Ψ.functor).hom)
      ((Functor.opId C₂).inv ≫ NatTrans.op η₂ ≫ (Functor.opComp Ψ.functor Φ.functor).hom)
      (fun X₁ ↦ by simpa using hη₁ X₁.unop)
      (fun X₂ ↦ by simpa using hη₂ X₂.unop)

end LocalizerMorphism

end CategoryTheory
