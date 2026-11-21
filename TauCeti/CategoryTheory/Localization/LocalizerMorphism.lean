/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Morphisms of localizers: opposites and composites

A morphism of localizers `Φ : LocalizerMorphism W₁ W₂` induces an equivalence on localized
categories if and only if its opposite localizer morphism `Φ.op` does
(`CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_iff_op`). The forward implication is an
instance in Joël Riou's `Mathlib.CategoryTheory.Localization.LocalizerMorphism`; this file supplies
the converse and equivalence. Dualizing Mathlib's
`CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit`, a localizer morphism
admitting an inverse up to natural transformations to the identities with components in `W₁` and
`W₂` induces an equivalence on localized categories
(`CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_counit_of_counit`).

For morphisms of localizers `Φ : LocalizerMorphism W₁ W₂` and `Ψ : LocalizerMorphism W₂ W₃` and
localization functors `L₁`, `L₂`, `L₃` for `W₁`, `W₂`, `W₃`, the composite of the induced functors
`Φ.localizedFunctor L₁ L₂ ⋙ Ψ.localizedFunctor L₂ L₃` lifts `(Φ.functor ⋙ Ψ.functor) ⋙ L₃`
through `L₁`, by pasting the two commutative squares of the induced functors.

## Main definitions

* `CategoryTheory.LocalizerMorphism.liftingCompLocalizedFunctor`: the composite of the induced
  functors lifts the composite of the functors of the morphisms of localizers.
-/

public section

namespace CategoryTheory.LocalizerMorphism

section Op

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂)

/-- A localizer morphism induces an equivalence on localized categories if and only if its opposite
localizer morphism does. -/
lemma isLocalizedEquivalence_iff_op :
    Φ.IsLocalizedEquivalence ↔ Φ.op.IsLocalizedEquivalence := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  let G := Φ.localizedFunctor W₁.Q W₂.Q
  let : CatCommSq Φ.op.functor W₁.Q.op W₂.Q.op G.op :=
    ⟨NatIso.op (CatCommSq.iso Φ.functor W₁.Q W₂.Q G).symm⟩
  have : G.op.IsEquivalence := Φ.op.isEquivalence W₁.Q.op W₂.Q.op G.op
  exact ⟨G.op.asEquivalence.unop.isEquivalence_functor⟩

/-- If a localizer morphism `Φ : LocalizerMorphism W₁ W₂` admits a localizer morphism
`Ψ : LocalizerMorphism W₂ W₁` in the opposite direction together with natural transformations
`η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁` and `η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂` whose components lie
in `W₁` and `W₂`, then `Φ` induces an equivalence on the localized categories. This is the dual
of Mathlib's `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_unit_of_unit`. -/
lemma isLocalizedEquivalence_of_counit_of_counit (Ψ : LocalizerMorphism W₂ W₁)
    (η₁ : Φ.functor ⋙ Ψ.functor ⟶ 𝟭 C₁) (η₂ : Ψ.functor ⋙ Φ.functor ⟶ 𝟭 C₂)
    (hη₁ : ∀ X₁, W₁ (η₁.app X₁)) (hη₂ : ∀ X₂, W₂ (η₂.app X₂)) :
    Φ.IsLocalizedEquivalence :=
  Φ.isLocalizedEquivalence_iff_op.2
    (Φ.op.isLocalizedEquivalence_of_unit_of_unit Ψ.op (NatTrans.op η₁) (NatTrans.op η₂)
      (fun X₁ ↦ hη₁ X₁.unop) (fun X₂ ↦ hη₂ X₂.unop))

end Op

section Comp

open Localization

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* D₁] [Category* D₂] [Category* D₃]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂} {W₃ : MorphismProperty C₃}
  (Φ : LocalizerMorphism W₁ W₂) (Ψ : LocalizerMorphism W₂ W₃)
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
  (L₃ : C₃ ⥤ D₃) [L₃.IsLocalization W₃]

/-- The composite of the functors induced on localizations by two morphisms of localizers lifts
the composite of their functors, followed by the last localization functor. -/
noncomputable instance liftingCompLocalizedFunctor :
    Lifting L₁ W₁ ((Φ.functor ⋙ Ψ.functor) ⋙ L₃)
      (Φ.localizedFunctor L₁ L₂ ⋙ Ψ.localizedFunctor L₂ L₃) :=
  ⟨(CatCommSq.hComp _ _ L₁ L₂ L₃ _ _).iso.symm⟩

end Comp

end CategoryTheory.LocalizerMorphism
