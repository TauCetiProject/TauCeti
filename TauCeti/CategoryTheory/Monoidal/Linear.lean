/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Scalar multiples and the tensor product in a monoidal linear category

In an `R`-linear monoidal category whose whiskerings are `R`-linear (Mathlib's
`CategoryTheory.MonoidalLinear`), the tensor product of morphisms commutes with scalar
multiplication in each variable.  Mathlib records this only for the whiskerings; these are the
statements needed to see that a tensor product of morphisms is `R`-bilinear.
-/

public section

namespace CategoryTheory

open MonoidalCategory

section

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C]

/-- Tensoring morphisms commutes with scalar multiplication in the first variable. -/
@[simp]
lemma smul_tensorHom {W X Y Z : C} (r : R) (f : W ⟶ X) (g : Y ⟶ Z) :
    (r • f) ⊗ₘ g = r • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

/-- Tensoring morphisms commutes with scalar multiplication in the second variable. -/
@[simp]
lemma tensorHom_smul {W X Y Z : C} (r : R) (f : W ⟶ X) (g : Y ⟶ Z) :
    f ⊗ₘ (r • g) = r • (f ⊗ₘ g) := by
  rw [tensorHom_def, tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

end

variable {R : Type*} [CommSemiring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C]

/-- Tensor product of morphisms as a bilinear map. -/
def MonoidalCategory.tensorHomLinear {W X Y Z : C} :
    (W ⟶ X) →ₗ[R] (Y ⟶ Z) →ₗ[R] (W ⊗ Y ⟶ X ⊗ Z) :=
  LinearMap.mk₂ R (fun f g ↦ f ⊗ₘ g)
    MonoidalPreadditive.add_tensor smul_tensorHom MonoidalPreadditive.tensor_add tensorHom_smul

/-- The bilinear tensor product acts by tensoring the two morphisms. -/
@[simp]
theorem MonoidalCategory.tensorHomLinear_apply {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHomLinear (R := R) f g = f ⊗ₘ g :=
  (rfl)

end CategoryTheory
