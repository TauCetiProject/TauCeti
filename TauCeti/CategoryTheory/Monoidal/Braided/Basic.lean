/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braiding coherence and naturality lemmas

In a braided monoidal category, braiding an object `Z` past a morphism `f : A ⊗ A' ⟶ 𝟙_ C`
or `g : 𝟙_ C ⟶ A ⊗ A'` moves `Z` from one side of the morphism to the other. Splitting the
braiding of `Z` with `A ⊗ A'` into crossings with `A` and `A'` by the hexagon identities, the
crossing with one factor can be traded for the inverse crossing with the other factor. These
identities are used to move objects past evaluations and coevaluations of exact pairings, for
which no rigidity is needed.

This file also records naturality of the re-associated crossing
`(α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom : X ⊗ (Y ⊗ Z) ⟶ Y ⊗ (X ⊗ Z)` of the first
two factors of a right-bracketed triple with respect to whiskered and tensor-product morphisms,
and the unitor identity `(λ_ X).hom ▷ 𝟙_ C ≫ (ρ_ X).hom` expressed through the braiding
`β_ X (𝟙_ C)` of `X` past the tensor unit.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Braiding `A` past `Z` and then applying `f : A ⊗ A' ⟶ 𝟙_ C` after `Z` is braiding `A'` back
under `Z` and then applying `f` before `Z`. -/
@[reassoc]
theorem braiding_whiskerRight_comp_whiskerLeft {A A' : C} (Z : C) (f : A ⊗ A' ⟶ 𝟙_ C) :
    (β_ A Z).hom ▷ A' ≫ (α_ Z A A').hom ≫ Z ◁ f =
      (α_ A Z A').hom ≫ A ◁ (β_ A' Z).inv ≫ (α_ A A' Z).inv ≫ f ▷ Z ≫ (λ_ Z).hom ≫
        (ρ_ Z).inv := by
  have h := braiding_naturality_left f Z
  rw [braiding_tensorUnit_left, braiding_tensor_left_hom] at h
  simp only [Category.assoc] at h ⊢
  rw [h]
  simp only [Iso.inv_hom_id_assoc, whiskerLeft_inv_hom_assoc, Iso.hom_inv_id_assoc]

/-- Braiding `Z` past `A` and then applying `f : A' ⊗ A ⟶ 𝟙_ C` before `Z` is braiding `Z` back
under `A'` and then applying `f` after `Z`. -/
@[reassoc]
theorem whiskerLeft_braiding_comp_whiskerRight {A A' : C} (Z : C) (f : A' ⊗ A ⟶ 𝟙_ C) :
    A' ◁ (β_ Z A).hom ≫ (α_ A' A Z).inv ≫ f ▷ Z =
      (α_ A' Z A).inv ≫ (β_ Z A').inv ▷ A ≫ (α_ Z A' A).hom ≫ Z ◁ f ≫ (ρ_ Z).hom ≫
        (λ_ Z).inv := by
  have h := braiding_naturality_right Z f
  rw [braiding_tensorUnit_right, braiding_tensor_right_hom] at h
  simp [h]

/-- Applying `g : 𝟙_ C ⟶ A ⊗ A'` after `Z` and then braiding `Z` past `A` is applying `g` before
`Z` and then braiding `Z` back under `A'`. -/
@[reassoc]
theorem whiskerLeft_comp_braiding_whiskerRight {A A' : C} (Z : C) (g : 𝟙_ C ⟶ A ⊗ A') :
    Z ◁ g ≫ (α_ Z A A').inv ≫ (β_ Z A).hom ▷ A' =
      (ρ_ Z).hom ≫ (λ_ Z).inv ≫ g ▷ Z ≫ (α_ A A' Z).hom ≫ A ◁ (β_ Z A').inv ≫
        (α_ A Z A').inv := by
  have h := braiding_naturality_right Z g
  rw [braiding_tensorUnit_right, braiding_tensor_right_hom] at h
  simp only [Category.assoc] at h
  rw [← reassoc_of% h]
  simp

/-- Applying `g : 𝟙_ C ⟶ A' ⊗ A` before `Z` and then braiding `A` past `Z` is applying `g` after
`Z` and then braiding `A'` back under `Z`. -/
@[reassoc]
theorem whiskerRight_comp_whiskerLeft_braiding {A A' : C} (Z : C) (g : 𝟙_ C ⟶ A' ⊗ A) :
    g ▷ Z ≫ (α_ A' A Z).hom ≫ A' ◁ (β_ A Z).hom =
      (λ_ Z).hom ≫ (ρ_ Z).inv ≫ Z ◁ g ≫ (α_ Z A' A).inv ≫ (β_ A' Z).inv ▷ A ≫
        (α_ A' Z A).hom := by
  have h := braiding_naturality_left g Z
  rw [braiding_tensorUnit_left, braiding_tensor_left_hom] at h
  simp only [Category.assoc] at h
  rw [← reassoc_of% h]
  simp

/-- Whiskering a morphism on the first factor of `X ⊗ (Y ⊗ Z)` commutes with swapping the first
two factors via `(α_ _ Y Z).inv ≫ (β_ _ Y).hom ▷ Z ≫ (α_ Y _ Z).hom`, moving the morphism onto
the middle factor. -/
@[reassoc]
theorem whiskerRight_comp_associator_inv_braiding_associator_hom {X X' : C} (f : X ⟶ X')
    (Y Z : C) :
    f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv ≫ (β_ X' Y).hom ▷ Z ≫ (α_ Y X' Z).hom =
      (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (f ▷ Z) := by
  rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc, braiding_naturality_left,
    comp_whiskerRight_assoc, associator_naturality_middle]

/-- Whiskering `f ⊗ₘ g` on the right two factors of `X ⊗ (Y ⊗ Z)` commutes with swapping the first
two factors via `(α_ X _ _).inv ≫ (β_ X _).hom ▷ _ ≫ (α_ _ X _).hom`, moving `f` onto the first
factor and `g` onto the third factor. -/
@[reassoc]
theorem whiskerLeft_tensorHom_comp_associator_inv_braiding_associator_hom (X : C)
    {Y Y' Z Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z') :
    X ◁ (f ⊗ₘ g) ≫ (α_ X Y' Z').inv ≫ (β_ X Y').hom ▷ Z' ≫ (α_ Y' X Z').hom =
      (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ f ▷ (X ⊗ Z) ≫ Y' ◁ (X ◁ g) := by
  rw [tensorHom_def, MonoidalCategory.whiskerLeft_comp_assoc,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc, associator_naturality_right,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, braiding_naturality_right,
    comp_whiskerRight_assoc, associator_naturality_left_assoc]

/-- **Unitors through the braiding with the unit.** The two ways of mapping
`(𝟙_ C ⊗ X) ⊗ 𝟙_ C` to `X` agree: whiskering the left unitor and applying the right unitor, or
reassociating, braiding `X` past the unit, reassociating back, and applying the unitors. -/
@[reassoc]
theorem leftUnitor_whiskerRight_comp_rightUnitor_eq (X : C) :
    (λ_ X).hom ▷ 𝟙_ C ≫ (ρ_ X).hom =
      (α_ (𝟙_ C) X (𝟙_ C)).hom ≫ 𝟙_ C ◁ (β_ X (𝟙_ C)).hom ≫
        (α_ (𝟙_ C) (𝟙_ C) X).inv ≫ (λ_ (𝟙_ C)).hom ▷ X ≫ (λ_ X).hom := by
  rw [braiding_tensorUnit_right]
  monoidal

end TauCeti
