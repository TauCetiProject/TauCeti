/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Negatives, differences and integer multiples in a monoidal preadditive category

In a monoidal preadditive category the whiskerings are additive, so they commute with negatives,
differences and natural and integer multiples of morphisms (Mathlib's `Functor.map_neg`,
`Functor.map_sub`, `Functor.map_nsmul` and `Functor.map_zsmul` for `tensorLeft` and
`tensorRight`); hence so does the tensor product of morphisms in each variable.  Mathlib's
`CategoryTheory.MonoidalPreadditive` records the additivity (and `CategoryTheory.MonoidalLinear`
the compatibility with scalars of a chosen ring), but not these consequences for the `ℤ`-module
structure every preadditive category carries.  The integer multiples are the signs of the
simplicial boundary and of the Koszul rule, which have to be moved through tensor products of
morphisms.
-/

public section

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalPreadditive C]

/-- Right whiskering commutes with negation. -/
@[simp]
lemma neg_whiskerRight {Y Z : C} (g : Y ⟶ Z) (U : C) : (-g) ▷ U = -(g ▷ U) :=
  (tensorRight U).map_neg

/-- Left whiskering commutes with negation. -/
@[simp]
lemma whiskerLeft_neg (U : C) {Y Z : C} (g : Y ⟶ Z) : U ◁ (-g) = -(U ◁ g) :=
  (tensorLeft U).map_neg

/-- Right whiskering commutes with subtraction. -/
@[simp]
lemma sub_whiskerRight {Y Z : C} (g h : Y ⟶ Z) (U : C) : (g - h) ▷ U = g ▷ U - h ▷ U :=
  (tensorRight U).map_sub

/-- Left whiskering commutes with subtraction. -/
@[simp]
lemma whiskerLeft_sub (U : C) {Y Z : C} (g h : Y ⟶ Z) : U ◁ (g - h) = U ◁ g - U ◁ h :=
  (tensorLeft U).map_sub

/-- Right whiskering commutes with natural number scalar multiplication. -/
@[simp]
lemma nsmul_whiskerRight (n : ℕ) {Y Z : C} (g : Y ⟶ Z) (U : C) : (n • g) ▷ U = n • (g ▷ U) :=
  (tensorRight U).map_nsmul

/-- Left whiskering commutes with natural number scalar multiplication. -/
@[simp]
lemma whiskerLeft_nsmul (n : ℕ) (U : C) {Y Z : C} (g : Y ⟶ Z) : U ◁ (n • g) = n • (U ◁ g) :=
  (tensorLeft U).map_nsmul

/-- Right whiskering commutes with integer scalar multiplication. -/
@[simp]
lemma zsmul_whiskerRight (n : ℤ) {Y Z : C} (g : Y ⟶ Z) (U : C) : (n • g) ▷ U = n • (g ▷ U) :=
  (tensorRight U).map_zsmul

/-- Left whiskering commutes with integer scalar multiplication. -/
@[simp]
lemma whiskerLeft_zsmul (n : ℤ) (U : C) {Y Z : C} (g : Y ⟶ Z) : U ◁ (n • g) = n • (U ◁ g) :=
  (tensorLeft U).map_zsmul

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
