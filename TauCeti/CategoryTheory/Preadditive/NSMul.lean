/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Multiplication by an integer in a preadditive category

In a preadditive category, multiplication by an integer `n` on an object `X` is the
morphism `n • 𝟙 X`, which is also the image of `n` in the endomorphism ring `End X`
(`CategoryTheory.End.intCast_asHom`, `CategoryTheory.End.natCast_asHom`). It commutes with every
morphism (`CategoryTheory.End.intCast_asHom_comp`, `CategoryTheory.End.natCast_asHom_comp`).

This file also records two facts about multiplication by a natural number `d` when it is
invertible:

* `CategoryTheory.Preadditive.comp_inv_nsmul_id`: the inverse of multiplication by `d` commutes
  with every morphism.
* `CategoryTheory.Functor.isIso_nsmul_id_obj`: an additive functor keeps multiplication by `d`
  invertible.
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
  rw [intCast_asHom, intCast_asHom, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    Category.id_comp, Category.comp_id]

/-- Multiplication by a natural number `n` commutes with every morphism. -/
@[reassoc]
theorem natCast_asHom_comp {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (n : End X).asHom ≫ f = f ≫ (n : End Y).asHom := by
  rw [natCast_asHom, natCast_asHom, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp, Category.comp_id]

end End

namespace Preadditive

/-- The inverse of multiplication by a natural number commutes with every morphism. -/
lemma comp_inv_nsmul_id {X Y : C} (f : X ⟶ Y) (d : ℕ) [IsIso (d • 𝟙 X)] [IsIso (d • 𝟙 Y)] :
    f ≫ inv (d • 𝟙 Y) = inv (d • 𝟙 X) ≫ f := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  simp [Preadditive.nsmul_comp, Preadditive.comp_nsmul]

end Preadditive

namespace Functor

/-- If multiplication by a natural number `d` is invertible on `X`, then it is invertible on the
image of `X` under any additive functor. -/
lemma isIso_nsmul_id_obj {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (d : ℕ) (X : C) [IsIso (d • 𝟙 X)] : IsIso (d • 𝟙 (F.obj X)) := by
  rw [← F.map_id, ← F.map_nsmul]
  infer_instance

end Functor

end CategoryTheory
