/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear

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

Consequently, if a natural number `e` kills an object `X`, in the sense that `e • 𝟙 X = 0`, then it
kills `X ⊗ Y` and `Y ⊗ X` (`CategoryTheory.nsmul_id_tensor_eq_zero_of_left` and
`CategoryTheory.nsmul_id_tensor_eq_zero_of_right`).

In particular whiskering is `ℤ`-linear for the `ℤ`-linear structure of a preadditive category
(`CategoryTheory.monoidalLinearInt`). This is not an instance: a category such as `ModuleCat ℤ`
also carries its own `ℤ`-linear structure, for which Mathlib states `MonoidalLinear ℤ`, while
instance search finds the preadditive one; files needing the latter use it as a local instance.
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

/-- If a natural number `e` kills `X`, in the sense that `e • 𝟙 X = 0`, then it kills `X ⊗ Y`. -/
lemma nsmul_id_tensor_eq_zero_of_left {X : C} {e : ℕ} (hX : e • 𝟙 X = 0) (Y : C) :
    e • 𝟙 (X ⊗ Y) = 0 := by
  rw [← id_whiskerRight, ← nsmul_whiskerRight, hX, MonoidalPreadditive.zero_whiskerRight]

/-- If a natural number `e` kills `Y`, in the sense that `e • 𝟙 Y = 0`, then it kills `X ⊗ Y`. -/
lemma nsmul_id_tensor_eq_zero_of_right {Y : C} {e : ℕ} (hY : e • 𝟙 Y = 0) (X : C) :
    e • 𝟙 (X ⊗ Y) = 0 := by
  rw [← whiskerLeft_id, ← whiskerLeft_nsmul, hY, MonoidalPreadditive.whiskerLeft_zero]

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

variable (C) in
/-- Whiskering commutes with the integer multiples of a monoidal preadditive category, that is,
it is linear for the `ℤ`-linear structure `CategoryTheory.Linear.preadditiveIntLinear`. -/
abbrev monoidalLinearInt : MonoidalLinear ℤ C where
  whiskerLeft_smul X _ _ r f := whiskerLeft_zsmul r X f
  smul_whiskerRight r _ _ f X := zsmul_whiskerRight r f X

end CategoryTheory
