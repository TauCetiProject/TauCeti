/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Functoriality of projections and the product comparison map

For any functor `F : C ⥤ D` out of a cartesian monoidal category `C`, the images under `F` of
`f ⊗ₘ g`, `f ▷ Z`, and `X ◁ f` commute with the mapped projections `F.map (fst _ _)` and
`F.map (snd _ _)` (`CategoryTheory.Functor.map_tensorHom_comp_map_fst`,
`CategoryTheory.Functor.map_tensorHom_comp_map_snd`, and their whiskering variants, together with
their `@[elementwise]` forms for concrete target categories).

When `D` is also cartesian monoidal, the comparison map
`CartesianMonoidalCategory.prodComparison F A B : F (A ⊗ B) ⟶ F A ⊗ F B` sends the image of a
lift `lift f g` to the lift of the images `lift (F.map f) (F.map g)`, and it commutes with the
braidings, which swap the factors.  The latter is the analogue for chosen finite products of
Mathlib's `CategoryTheory.Limits.map_braiding_hom_comp_prodComparison`.
-/

public section

namespace CategoryTheory.Functor

open MonoidalCategory CartesianMonoidalCategory

section Projections

variable {C D : Type*} [Category* C] [Category* D] [CartesianMonoidalCategory C] (F : C ⥤ D)

/-- Applying `F` to `f ⊗ₘ g` followed by the first projection factors `F.map f` through the first
projection. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_tensorHom_comp_map_fst {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    F.map (f ⊗ₘ g) ≫ F.map (fst X₂ Y₂) = F.map (fst X₁ Y₁) ≫ F.map f := by
  rw [← F.map_comp, tensorHom_fst, F.map_comp]

/-- Applying `F` to `f ⊗ₘ g` followed by the second projection factors `F.map g` through the second
projection. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_tensorHom_comp_map_snd {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    F.map (f ⊗ₘ g) ≫ F.map (snd X₂ Y₂) = F.map (snd X₁ Y₁) ≫ F.map g := by
  rw [← F.map_comp, tensorHom_snd, F.map_comp]

/-- Applying `F` to `f ▷ Z` followed by the first projection factors `F.map f` through the first
projection. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_whiskerRight_comp_map_fst {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ▷ Z) ≫ F.map (fst Y Z) = F.map (fst X Z) ≫ F.map f := by
  rw [← F.map_comp, whiskerRight_fst, F.map_comp]

/-- Applying `F` to `f ▷ Z` followed by the second projection is the second projection. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_whiskerRight_comp_map_snd {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ▷ Z) ≫ F.map (snd Y Z) = F.map (snd X Z) := by
  rw [← F.map_comp, whiskerRight_snd]

/-- Applying `F` to `X ◁ f` followed by the first projection is the first projection. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_whiskerLeft_comp_map_fst (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (X ◁ f) ≫ F.map (fst X Z) = F.map (fst X Y) := by
  rw [← F.map_comp, whiskerLeft_fst]

/-- Applying `F` to `X ◁ f` followed by the second projection factors `F.map f` through the second
projection. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma map_whiskerLeft_comp_map_snd (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (X ◁ f) ≫ F.map (snd X Z) = F.map (snd X Y) ≫ F.map f := by
  rw [← F.map_comp, whiskerLeft_snd, F.map_comp]

end Projections

variable {C D : Type*} [Category* C] [Category* D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] (F : C ⥤ D)

/-- The product comparison map sends the image of a lift to the lift of the images. -/
@[reassoc (attr := simp)]
lemma map_lift_prodComparison {T A B : C} (f : T ⟶ A) (g : T ⟶ B) :
    F.map (lift f g) ≫ prodComparison F A B = lift (F.map f) (F.map g) := by
  ext <;> simp [← Functor.map_comp]

variable [BraidedCategory C] [BraidedCategory D]

/-- The product comparison map commutes with the braidings. -/
@[reassoc]
lemma map_braiding_hom_comp_prodComparison (A B : C) :
    F.map (β_ A B).hom ≫ prodComparison F B A =
      prodComparison F A B ≫ (β_ (F.obj A) (F.obj B)).hom := by
  ext <;> simp [← Functor.map_comp]

end CategoryTheory.Functor
