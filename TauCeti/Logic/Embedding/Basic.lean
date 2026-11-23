/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Embedding.Basic

/-!
# Congruence equivalences on subtypes of injective functions

Transferring an injective function `f : α₁ → β₁` along equivalences `e₁ : α₁ ≃ α₂` and
`e₂ : β₁ ≃ β₂` defines an equivalence `Equiv.subtypeInjectiveCongr e₁ e₂` between
`{f : α₁ → β₁ // Function.Injective f}` and `{f : α₂ → β₂ // Function.Injective f}`, obtained by
conjugating `Equiv.embeddingCongr e₁ e₂` along `Equiv.subtypeInjectiveEquivEmbedding`.

## Main definitions

* `Equiv.subtypeInjectiveCongr`: equivalence on subtypes of injective functions induced by
  equivalences on the domain and codomain.
-/

public section

namespace Equiv

/-- Equivalences on the domain and codomain induce an equivalence on subtypes of injective
functions, sending `f` to `e₂ ∘ f ∘ e₁.symm`. -/
def subtypeInjectiveCongr {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    {f : α₁ → β₁ // Function.Injective f} ≃ {f : α₂ → β₂ // Function.Injective f} :=
  (subtypeInjectiveEquivEmbedding α₁ β₁).trans
    ((embeddingCongr e₁ e₂).trans (subtypeInjectiveEquivEmbedding α₂ β₂).symm)

/-- Applying `subtypeInjectiveCongr e₁ e₂` conjugates an injective function by `e₁.symm` on the
right and `e₂` on the left. -/
@[simp]
theorem subtypeInjectiveCongr_apply {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂)
    (f : {f : α₁ → β₁ // Function.Injective f}) :
    subtypeInjectiveCongr e₁ e₂ f =
      ⟨e₂ ∘ f.val ∘ e₁.symm, e₂.injective.comp (f.property.comp e₁.symm.injective)⟩ :=
  Subtype.ext rfl

/-- The inverse of `subtypeInjectiveCongr e₁ e₂` is `subtypeInjectiveCongr e₁.symm e₂.symm`. -/
@[simp]
theorem subtypeInjectiveCongr_symm {α₁ α₂ β₁ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (subtypeInjectiveCongr e₁ e₂).symm = subtypeInjectiveCongr e₁.symm e₂.symm :=
  (rfl)

/-- `subtypeInjectiveCongr` sends identity equivalences to the identity equivalence. -/
@[simp]
theorem subtypeInjectiveCongr_refl {α β : Sort*} :
    subtypeInjectiveCongr (Equiv.refl α) (Equiv.refl β) =
      Equiv.refl {f : α → β // Function.Injective f} :=
  (rfl)

/-- `subtypeInjectiveCongr` respects composition of equivalences. -/
@[simp]
theorem subtypeInjectiveCongr_trans {α₁ α₂ α₃ β₁ β₂ β₃ : Sort*} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂)
    (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
    subtypeInjectiveCongr (e₁.trans e₂) (e₁'.trans e₂') =
      (subtypeInjectiveCongr e₁ e₁').trans (subtypeInjectiveCongr e₂ e₂') :=
  (rfl)

end Equiv
