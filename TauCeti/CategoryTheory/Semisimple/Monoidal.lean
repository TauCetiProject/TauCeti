/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Simple constituents of tensor products

In a finite semisimple monoidal category, a simple constituent of an object `Y` is a simple object
with a nonzero morphism to `Y`. This file relates the simple constituents of a tensor product
`X ⊗ Y` to those of its factors.

## Main results

* `TauCeti.comp_whiskerRight_ne_zero` and `TauCeti.comp_whiskerLeft_ne_zero`: a nonzero morphism
  into `X ⊗ Y` stays nonzero after whiskering a nonzero morphism out of a simple factor onto it.
* `TauCeti.exists_simple_of_nonzero_to_tensor_left` and
  `TauCeti.exists_simple_of_nonzero_to_tensor_right`: a nonzero morphism into `X ⊗ Y` gives a
  nonzero morphism into `W ⊗ Y` (resp. `X ⊗ W`) for a simple constituent `W` of `X` (resp. `Y`).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]
  [MonoidalCategory C]

/-- A nonzero morphism into `X ⊗ Y`, with `X` simple, stays nonzero after whiskering a nonzero
morphism out of `X` onto it. -/
theorem comp_whiskerRight_ne_zero {U X X' Y : C} [Simple X] {f : U ⟶ X ⊗ Y} (hf : f ≠ 0)
    {g : X ⟶ X'} (hg : g ≠ 0) : f ≫ g ▷ Y ≠ 0 := fun h ↦ by
  have := isSplitMono_of_nonzero_from_simple hg
  exact hf (by simpa [← comp_whiskerRight] using h =≫ retraction g ▷ Y)

/-- A nonzero morphism into `X ⊗ Y`, with `Y` simple, stays nonzero after whiskering a nonzero
morphism out of `Y` onto it. -/
theorem comp_whiskerLeft_ne_zero {U X Y Y' : C} [Simple Y] {f : U ⟶ X ⊗ Y} (hf : f ≠ 0)
    {g : Y ⟶ Y'} (hg : g ≠ 0) : f ≫ X ◁ g ≠ 0 := fun h ↦ by
  have := isSplitMono_of_nonzero_from_simple hg
  exact hf (by simpa [← whiskerLeft_comp] using h =≫ X ◁ retraction g)

variable [MonoidalPreadditive C]

/-- A nonzero morphism into `X ⊗ Y` gives a nonzero morphism into `W ⊗ Y` for some simple
constituent `W` of `X`: a summand of a decomposition of `X` into simple objects. -/
theorem exists_simple_of_nonzero_to_tensor_left {U X Y : C} {f : U ⟶ X ⊗ Y} (hf : f ≠ 0) :
    ∃ (W : C) (_ : Simple W) (g : U ⟶ W ⊗ Y) (j : W ⟶ X), g ≠ 0 ∧ j ≠ 0 := by
  obtain ⟨ι, hι, a, ha, hba, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  obtain ⟨i, hi⟩ : ∃ i, f ≫ (e.hom ≫ biproduct.π a i) ▷ Y ≠ 0 := by
    by_contra! h
    -- The components of `f` along `(⨁ a) ⊗ Y ≅ ⨁ i, a i ⊗ Y` all vanish.
    refine hf <| (cancel_mono (e.hom ▷ Y ≫ (rightDistributor a Y).hom)).1 ?_
    ext i
    simpa using h i
  exact ⟨a i, ha i, _, _, hi, biproduct_ι_comp_inv_ne_zero e i⟩

/-- A nonzero morphism into `X ⊗ Y` gives a nonzero morphism into `X ⊗ W` for some simple
constituent `W` of `Y`: a summand of a decomposition of `Y` into simple objects. -/
theorem exists_simple_of_nonzero_to_tensor_right {U X Y : C} {f : U ⟶ X ⊗ Y} (hf : f ≠ 0) :
    ∃ (W : C) (_ : Simple W) (g : U ⟶ X ⊗ W) (j : W ⟶ Y), g ≠ 0 ∧ j ≠ 0 := by
  obtain ⟨ι, hι, a, ha, hba, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples Y
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  obtain ⟨i, hi⟩ : ∃ i, f ≫ X ◁ (e.hom ≫ biproduct.π a i) ≠ 0 := by
    by_contra! h
    -- The components of `f` along `X ⊗ ⨁ a ≅ ⨁ i, X ⊗ a i` all vanish.
    refine hf <| (cancel_mono (X ◁ e.hom ≫ (leftDistributor X a).hom)).1 ?_
    ext i
    simpa using h i
  exact ⟨a i, ha i, _, _, hi, biproduct_ι_comp_inv_ne_zero e i⟩

end TauCeti
