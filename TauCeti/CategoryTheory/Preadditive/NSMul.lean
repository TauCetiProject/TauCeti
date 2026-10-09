/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Invertible multiplication by a natural number

In a preadditive category, multiplication by a natural number `d` on an object `X` is the
morphism `d • 𝟙 X`. This file records two facts about it when it is invertible:

* `CategoryTheory.Preadditive.comp_inv_nsmul_id`: the inverse of multiplication by `d` commutes
  with every morphism.
* `CategoryTheory.Functor.isIso_nsmul_id_obj`: an additive functor keeps multiplication by `d`
  invertible.
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

namespace Preadditive

/-- The inverse of multiplication by a natural number commutes with every morphism. -/
lemma comp_inv_nsmul_id {X Y : C} (f : X ⟶ Y) (d : ℕ) [IsIso (d • 𝟙 X)] [IsIso (d • 𝟙 Y)] :
    f ≫ inv (d • 𝟙 Y) = inv (d • 𝟙 X) ≫ f := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

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
