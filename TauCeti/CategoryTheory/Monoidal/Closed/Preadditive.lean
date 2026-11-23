/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive

import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Biclosed preadditive categories are monoidal preadditive

If tensoring on either side with a fixed object is a left adjoint (for instance in a closed braided
monoidal category), it preserves binary coproducts. In a preadditive category, binary coproducts
are binary biproducts, and a functor preserving them is additive. Hence the tensor product of
morphisms is additive in each variable: the category is `MonoidalPreadditive`.

This applies to categories such as sheaves of modules, whose monoidal structure is constructed
abstractly (for instance by localization) rather than from a bilinear formula on morphisms.

## Main declarations

* `TauCeti.monoidalPreadditive_of_isLeftAdjoint`.
* `TauCeti.tensorSwapCurryEquiv`: additive currying after braiding the tensor factors.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

/-- A preadditive monoidal category with binary coproducts, in which tensoring on either side with
a fixed object is a left adjoint, is monoidal preadditive: whiskering on either side is additive.
This applies to closed braided monoidal categories. -/
theorem monoidalPreadditive_of_isLeftAdjoint (C : Type*) [Category* C] [Preadditive C]
    [HasBinaryCoproducts C] [MonoidalCategory C] [∀ X : C, (tensorLeft X).IsLeftAdjoint]
    [∀ X : C, (tensorRight X).IsLeftAdjoint] :
    MonoidalPreadditive C := by
  have : HasBinaryBiproducts C := .of_hasBinaryCoproducts
  have (X : C) : (tensorLeft X).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
    Functor.additive_of_preservesBinaryBiproducts _
  have (X : C) : (tensorRight X).Additive :=
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight X)
    Functor.additive_of_preservesBinaryBiproducts _
  exact
    { whiskerLeft_zero := (tensorLeft _).map_zero _ _
      zero_whiskerRight := (tensorRight _).map_zero _ _
      whiskerLeft_add _ _ := (tensorLeft _).map_add
      add_whiskerRight _ _ := (tensorRight _).map_add }

open MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
variable (X Y Z : C) [Closed Y] [(tensorLeft Y).Additive]

/-- Swapping the tensor factors and currying is an additive equivalence. Only the right
factor needs to be closed, and only tensoring on the left by that factor needs to be additive. -/
noncomputable def tensorSwapCurryEquiv : (X ⊗ Y ⟶ Z) ≃+ (X ⟶ (Y ⟶[C] Z)) :=
  ((Linear.homCongr ℤ (β_ X Y) (Iso.refl Z)).toAddEquiv).trans
    ((ihom.adjunction Y).homAddEquiv X Z)

/-- The swapped currying comparison is currying after the inverse braiding. -/
lemma tensorSwapCurryEquiv_apply (g : X ⊗ Y ⟶ Z) :
    tensorSwapCurryEquiv X Y Z g = curry ((β_ X Y).inv ≫ g) := by
  unfold tensorSwapCurryEquiv
  erw [AddEquiv.trans_apply, Adjunction.homAddEquiv_apply, LinearEquiv.coe_addEquiv_apply,
    Linear.homCongr_apply]
  simp only [Iso.refl_hom, Category.comp_id, homEquiv_apply_eq]

/-- Precomposition in the first tensor factor becomes precomposition after swapped currying. -/
lemma tensorSwapCurryEquiv_precomp {X' : C} (f : X' ⟶ X) (g : X ⊗ Y ⟶ Z) :
    tensorSwapCurryEquiv X' Y Z ((f ▷ Y) ≫ g) =
      f ≫ tensorSwapCurryEquiv X Y Z g := by
  rw [tensorSwapCurryEquiv_apply, tensorSwapCurryEquiv_apply, ← curry_natural_left]
  congr 1
  rw [← Category.assoc, ← BraidedCategory.braiding_inv_naturality_right, Category.assoc]

end TauCeti
