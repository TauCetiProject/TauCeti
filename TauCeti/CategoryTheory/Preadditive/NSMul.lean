/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Multiplication by an integer in a preadditive category

In a preadditive category, multiplication by an integer `n` on an object `X` is the
morphism `n • 𝟙 X`, which is also the image of `n` in the endomorphism ring `End X`
(`CategoryTheory.End.intCast_asHom`, `CategoryTheory.End.natCast_asHom`). It commutes with every
morphism (`CategoryTheory.End.intCast_asHom_comp`, `CategoryTheory.End.natCast_asHom_comp`).

The inverse of a scalar multiple `r • 𝟙` and its preservation by linear functors are in
`TauCeti.CategoryTheory.Linear.Endomorphism`.
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

namespace End

/-- The integer `n` in the endomorphism ring of `X` is multiplication by `n`, the morphism
`n • 𝟙 X`. -/
theorem intCast_asHom (X : C) (n : ℤ) : (n : End X).asHom = n • 𝟙 X := by
  rw [← zsmul_one, zsmul_asHom, one_asHom]

/-- The natural number `n` in the endomorphism ring of `X` is multiplication by `n`, the morphism
`n • 𝟙 X`. -/
theorem natCast_asHom (X : C) (n : ℕ) : (n : End X).asHom = n • 𝟙 X := by
  rw [← nsmul_one, nsmul_asHom, one_asHom]

/-- Multiplication by an integer `n` commutes with every morphism. -/
@[reassoc]
theorem intCast_asHom_comp {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    (n : End X).asHom ≫ f = f ≫ (n : End Y).asHom := by
  simp [intCast_asHom, Preadditive.zsmul_comp, Preadditive.comp_zsmul]

/-- Multiplication by a natural number `n` commutes with every morphism. -/
@[reassoc]
theorem natCast_asHom_comp {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (n : End X).asHom ≫ f = f ≫ (n : End Y).asHom := by
  simpa using intCast_asHom_comp f n

end End

end CategoryTheory
