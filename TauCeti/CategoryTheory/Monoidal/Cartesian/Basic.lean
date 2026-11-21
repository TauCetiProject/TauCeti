/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The product comparison map, lifts and the braiding

For a functor `F` between cartesian monoidal categories, the comparison map
`CartesianMonoidalCategory.prodComparison F A B : F (A ⊗ B) ⟶ F A ⊗ F B` sends the image of a
lift `lift f g` to the lift of the images `lift (F.map f) (F.map g)`, and it commutes with the
braidings, which swap the factors.  The latter is the analogue for chosen finite products of
Mathlib's `CategoryTheory.Limits.map_braiding_hom_comp_prodComparison`.
-/

public section

namespace CategoryTheory.Functor

open MonoidalCategory CartesianMonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] (F : C ⥤ D)

/-- The product comparison map sends the image of a lift to the lift of the images. -/
@[reassoc (attr := simp)]
lemma map_lift_comp_prodComparison {T A B : C} (f : T ⟶ A) (g : T ⟶ B) :
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
