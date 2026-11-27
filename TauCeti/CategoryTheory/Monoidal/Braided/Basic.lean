/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braiding coherence and naturality lemmas

In a braided monoidal category, braiding an object `Z` past a morphism `f : A ⊗ A' ⟶ B`
or `g : B ⟶ A ⊗ A'` moves `Z` from one side of the morphism to the other. Splitting the
braiding of `Z` with `A ⊗ A'` into crossings with `A` and `A'` by the hexagon identities, the
crossing with one factor can be traded for the inverse crossing with the other factor, together
with a crossing of `Z` and `B`. With `B = 𝟙_ C` these identities move objects past evaluations
and coevaluations of exact pairings, for which no rigidity is needed; the crossing with `𝟙_ C`
is then given by unitors (`braiding_tensorUnit_left`, `braiding_tensorUnit_right`).

This file also records naturality of the re-associated crossing
`(α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom : X ⊗ (Y ⊗ Z) ⟶ Y ⊗ (X ⊗ Z)` of the first
two factors of a right-bracketed triple with respect to whiskered and tensor-product morphisms,
and the unitor identity `(λ_ X).hom ▷ 𝟙_ C ≫ (ρ_ X).hom` expressed through the braiding
`β_ X (𝟙_ C)` of `X` past the tensor unit.

It also records that the inverse tensorator `δ` of a braided functor commutes with the braiding
(`CategoryTheory.Functor.δ_braiding`), the `δ`-form of `Functor.map_braiding`.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Braiding `A` past `Z` and then applying `f : A ⊗ A' ⟶ B` after `Z` is braiding `A'` back
under `Z`, applying `f` before `Z`, and then braiding `B` past `Z`. -/
@[reassoc]
theorem braiding_whiskerRight_comp_whiskerLeft {A A' B : C} (Z : C) (f : A ⊗ A' ⟶ B) :
    (β_ A Z).hom ▷ A' ≫ (α_ Z A A').hom ≫ Z ◁ f =
      (α_ A Z A').hom ≫ A ◁ (β_ A' Z).inv ≫ (α_ A A' Z).inv ≫ f ▷ Z ≫ (β_ B Z).hom := by
  rw [braiding_naturality_left, braiding_tensor_left_hom]
  simp

/-- Braiding `Z` past `A` and then applying `f : A' ⊗ A ⟶ B` before `Z` is braiding `Z` back
under `A'`, applying `f` after `Z`, and then braiding `Z` past `B`. -/
@[reassoc]
theorem whiskerLeft_braiding_comp_whiskerRight {A A' B : C} (Z : C) (f : A' ⊗ A ⟶ B) :
    A' ◁ (β_ Z A).hom ≫ (α_ A' A Z).inv ≫ f ▷ Z =
      (α_ A' Z A).inv ≫ (β_ Z A').inv ▷ A ≫ (α_ Z A' A).hom ≫ Z ◁ f ≫ (β_ Z B).hom := by
  rw [braiding_naturality_right, braiding_tensor_right_hom]
  simp

/-- Applying `g : B ⟶ A ⊗ A'` after `Z` and then braiding `Z` past `A` is braiding `Z` past `B`,
applying `g` before `Z`, and then braiding `Z` back under `A'`. -/
@[reassoc]
theorem whiskerLeft_comp_braiding_whiskerRight {A A' B : C} (Z : C) (g : B ⟶ A ⊗ A') :
    Z ◁ g ≫ (α_ Z A A').inv ≫ (β_ Z A).hom ▷ A' =
      (β_ Z B).hom ≫ g ▷ Z ≫ (α_ A A' Z).hom ≫ A ◁ (β_ Z A').inv ≫ (α_ A Z A').inv := by
  rw [← braiding_naturality_right_assoc, braiding_tensor_right_hom]
  simp

/-- Applying `g : B ⟶ A' ⊗ A` before `Z` and then braiding `A` past `Z` is braiding `B` past `Z`,
applying `g` after `Z`, and then braiding `A'` back under `Z`. -/
@[reassoc]
theorem whiskerRight_comp_whiskerLeft_braiding {A A' B : C} (Z : C) (g : B ⟶ A' ⊗ A) :
    g ▷ Z ≫ (α_ A' A Z).hom ≫ A' ◁ (β_ A Z).hom =
      (β_ B Z).hom ≫ Z ◁ g ≫ (α_ Z A' A).inv ≫ (β_ A' Z).inv ▷ A ≫ (α_ A' Z A).hom := by
  rw [← braiding_naturality_left_assoc, braiding_tensor_left_hom]
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

/-- Whiskering `g` on the third factor of `X ⊗ (Y ⊗ Z)` commutes with swapping the first two
factors via `(α_ X _ _).inv ≫ (β_ X _).hom ▷ _ ≫ (α_ _ X _).hom`. -/
@[reassoc]
theorem whiskerLeft_whiskerLeft_comp_associator_inv_braiding_associator_hom (X Y : C)
    {Z Z' : C} (g : Z ⟶ Z') :
    X ◁ Y ◁ g ≫ (α_ X Y Z').inv ≫ (β_ X Y).hom ▷ Z' ≫ (α_ Y X Z').hom =
      (α_ X Y Z).inv ≫ (β_ X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ X ◁ g := by
  simpa using whiskerLeft_tensorHom_comp_associator_inv_braiding_associator_hom X (𝟙 Y) g

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

/-- The inverse tensorator `δ` of a braided functor intertwines the braiding of the images with the
image of the braiding. This is the `δ` counterpart of `Functor.map_braiding`. -/
@[reassoc]
theorem _root_.CategoryTheory.Functor.δ_braiding {D : Type*} [Category* D] [MonoidalCategory D]
    [BraidedCategory D] (F : C ⥤ D) [F.Braided] (X Y : C) :
    Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom =
      F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X := by
  rw [← cancel_mono (Functor.LaxMonoidal.μ F Y X)]
  simp

end TauCeti
