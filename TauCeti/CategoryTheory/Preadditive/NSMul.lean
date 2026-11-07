/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Multiplication by integers and scalars in a preadditive category

In a preadditive category, multiplication by an integer `n` on an object `X` is the
morphism `n • 𝟙 X`, which is also the image of `n` in the endomorphism ring `End X`
(`CategoryTheory.End.intCast_asHom`, `CategoryTheory.End.natCast_asHom`). It commutes with every
morphism (`CategoryTheory.End.intCast_asHom_comp`, `CategoryTheory.End.natCast_asHom_comp`).

This file also records two facts about multiplication by a scalar `r` in an `R`-linear category
(for instance a natural number or an integer in any preadditive category) when it is invertible:

* `CategoryTheory.Linear.comp_inv_smul_id`: the inverse of `r • 𝟙` commutes with every morphism.
* `CategoryTheory.Functor.isIso_smul_id_obj`: an `R`-linear functor keeps `r • 𝟙` invertible.
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
  simp [intCast_asHom]

/-- Multiplication by a natural number `n` commutes with every morphism. -/
@[reassoc]
theorem natCast_asHom_comp {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (n : End X).asHom ≫ f = f ≫ (n : End Y).asHom := by
  simpa using intCast_asHom_comp f n

end End

variable {R : Type*} [Semiring R] [CategoryTheory.Linear R C]

namespace Linear

/-- The inverse of multiplication by a scalar `r` commutes with every morphism. -/
lemma comp_inv_smul_id {X Y : C} (f : X ⟶ Y) (r : R) [IsIso (r • 𝟙 X)] [IsIso (r • 𝟙 Y)] :
    f ≫ inv (r • 𝟙 Y) = inv (r • 𝟙 X) ≫ f := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  simp

end Linear

namespace Functor

/-- If multiplication by a scalar `r` is invertible on `X`, then it is invertible on the image of
`X` under any `R`-linear functor. -/
lemma isIso_smul_id_obj {D : Type*} [Category D] [Preadditive D] [CategoryTheory.Linear R D]
    (F : C ⥤ D) [F.Linear R] (r : R) (X : C) [IsIso (r • 𝟙 X)] :
    IsIso (r • 𝟙 (F.obj X)) := by
  rw [← F.map_id, ← F.map_smul]
  infer_instance

end Functor

end CategoryTheory
