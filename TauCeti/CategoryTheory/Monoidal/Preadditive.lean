/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Integer multiples and the tensor product in a monoidal preadditive category

In a monoidal preadditive category the whiskerings are additive, so they commute with integer
multiples of morphisms.  Mathlib's `CategoryTheory.MonoidalPreadditive` records the additivity
(and `CategoryTheory.MonoidalLinear` the compatibility with scalars of a chosen ring), but not the
`ℤ`-multiples every preadditive category carries.  These are the signs of the simplicial boundary
and of the Koszul rule, which have to be moved through tensor products of morphisms.
-/

public section

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

@[simp]
lemma zsmul_whiskerRight {X Y : C} (m : ℤ) (f : X ⟶ Y) (Z : C) :
    (m • f) ▷ Z = m • (f ▷ Z) :=
  map_zsmul ((tensoringRight C).obj Z).mapAddHom m f

@[simp]
lemma whiskerLeft_zsmul (X : C) {Y Z : C} (m : ℤ) (f : Y ⟶ Z) :
    X ◁ (m • f) = m • (X ◁ f) :=
  map_zsmul ((tensoringLeft C).obj X).mapAddHom m f

@[simp]
lemma zsmul_tensorHom {W X Y Z : C} (m : ℤ) (f : W ⟶ X) (g : Y ⟶ Z) :
    (m • f) ⊗ₘ g = m • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, zsmul_whiskerRight, Preadditive.zsmul_comp]

@[simp]
lemma tensorHom_zsmul {W X Y Z : C} (m : ℤ) (f : W ⟶ X) (g : Y ⟶ Z) :
    f ⊗ₘ (m • g) = m • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, whiskerLeft_zsmul, Preadditive.comp_zsmul]

end CategoryTheory
