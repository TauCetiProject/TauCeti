/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Uncurried bifunctors on a constant first coordinate

For a bifunctor `H : B ⥤ C ⥤ D`, the uncurried functor `Functor.uncurry.obj H : B × C ⥤ D`
restricted along a functor `J ⥤ B × C` whose first coordinate is constant at `b` is the
restriction of `H.obj b` along the second coordinate
(`CategoryTheory.Functor.const_obj_prod'_comp_uncurry_obj`).
-/

public section

namespace CategoryTheory.Functor

variable {J B C D : Type*} [Category J] [Category B] [Category C] [Category D]

/-- On a constant first coordinate `b`, the uncurried functor of `H : B ⥤ C ⥤ D` restricts to
`H.obj b`. -/
lemma const_obj_prod'_comp_uncurry_obj (H : B ⥤ C ⥤ D) (b : B) (x : J ⥤ C) :
    ((Functor.const J).obj b).prod' x ⋙ Functor.uncurry.obj H = x ⋙ H.obj b :=
  Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ by simp)

end CategoryTheory.Functor
