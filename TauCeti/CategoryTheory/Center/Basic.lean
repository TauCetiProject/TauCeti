/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Center.Basic

/-!
# Units of the centre of a category

A unit `z` of the centre `CatCenter C` of a category `C` acts on every object `X` by an
isomorphism: its component `z.val.app X` has inverse `z⁻¹.val.app X`.
-/

public section

universe v u

namespace CategoryTheory.CatCenter

variable {C : Type u} [Category.{v} C]

/-- The component of `z⁻¹` at `X` is a left inverse of that of `z`. -/
@[reassoc (attr := simp)]
lemma inv_app_comp_app (z : (CatCenter C)ˣ) (X : C) : z⁻¹.val.app X ≫ z.val.app X = 𝟙 X := by
  rw [← mul_app, Units.inv_mul, app_one]

/-- The component of `z⁻¹` at `X` is a right inverse of that of `z`. -/
@[reassoc (attr := simp)]
lemma app_comp_inv_app (z : (CatCenter C)ˣ) (X : C) : z.val.app X ≫ z⁻¹.val.app X = 𝟙 X := by
  rw [← mul_app, Units.mul_inv, app_one]

/-- The component of a unit of the centre at every object is an isomorphism. -/
instance isIso_app (z : (CatCenter C)ˣ) (X : C) : IsIso (z.val.app X) :=
  ⟨⟨_, app_comp_inv_app z X, inv_app_comp_app z X⟩⟩

/-- The component of the inverse of a unit of the centre is the inverse of its component. -/
lemma inv_val_app (z : (CatCenter C)ˣ) (X : C) : z⁻¹.val.app X = inv (z.val.app X) :=
  (IsIso.inv_eq_of_hom_inv_id (app_comp_inv_app z X)).symm

end CategoryTheory.CatCenter
