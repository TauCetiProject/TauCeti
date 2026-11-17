/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Composing the functors induced by morphisms of localizers

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

end CategoryTheory.LocalizerMorphism
