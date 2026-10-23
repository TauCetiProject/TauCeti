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
multiples of morphisms (Mathlib's `Functor.map_zsmul` for `tensorLeft` and `tensorRight`); hence
so does the tensor product of morphisms in each variable.  Mathlib's
`CategoryTheory.MonoidalPreadditive` records the additivity (and `CategoryTheory.MonoidalLinear`
the compatibility with scalars of a chosen ring), but not the `ℤ`-multiples every preadditive
category carries.  These are the signs of the simplicial boundary and of the Koszul rule, which
have to be moved through tensor products of morphisms.
-/

public section

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

/-- Tensoring morphisms commutes with integer scalar multiplication in the first variable. -/
@[simp]
lemma zsmul_tensorHom {W X Y Z : C} (m : ℤ) (f : W ⟶ X) (g : Y ⟶ Z) :
    (m • f) ⊗ₘ g = m • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, ← Preadditive.zsmul_comp]
  exact congrArg (· ≫ X ◁ g) ((tensorRight Y).map_zsmul (f := f) (r := m))

/-- Tensoring morphisms commutes with integer scalar multiplication in the second variable. -/
@[simp]
lemma tensorHom_zsmul {W X Y Z : C} (m : ℤ) (f : W ⟶ X) (g : Y ⟶ Z) :
    f ⊗ₘ (m • g) = m • (f ⊗ₘ g) := by
  rw [tensorHom_def', tensorHom_def', ← Preadditive.zsmul_comp]
  exact congrArg (· ≫ f ▷ Z) ((tensorLeft W).map_zsmul (f := g) (r := m))

end CategoryTheory
