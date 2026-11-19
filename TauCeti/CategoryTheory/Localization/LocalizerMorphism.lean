/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Opposite localizer morphisms and localized equivalences

A morphism of localizers `Φ : LocalizerMorphism W₁ W₂` induces an equivalence on localized
categories if and only if its opposite localizer morphism `Φ.op` does
(`CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_iff_op`). The forward implication is an
instance in Joël Riou's `Mathlib.CategoryTheory.Localization.LocalizerMorphism`; this file supplies
the converse and equivalence.
-/

public section

namespace CategoryTheory.LocalizerMorphism

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

end CategoryTheory.LocalizerMorphism
