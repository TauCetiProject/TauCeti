/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Tensorator square of a lax monoidal functor

The tensorator of a lax monoidal functor is natural in its right argument, giving a
square between left tensoring and the functor.
-/

public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The natural tensorator square for left tensoring by `A` under a lax monoidal functor. -/
def laxCommTensorLeft (F : C ⥤ D) [F.LaxMonoidal] (A : C) :
    TwoSquare F (MonoidalCategory.tensorLeft A)
      (MonoidalCategory.tensorLeft (F.obj A)) F :=
  .mk _ _ _ _ { app := fun B => Functor.LaxMonoidal.μ F A B
                naturality := fun _ _ f => Functor.LaxMonoidal.μ_natural_right F A f }

/-- The component of the tensorator square is the tensorator. -/
@[simp]
theorem laxCommTensorLeft_app (F : C ⥤ D) [F.LaxMonoidal] (A B : C) :
    (laxCommTensorLeft F A).app B = Functor.LaxMonoidal.μ F A B := by
  unfold laxCommTensorLeft
  rfl

end CategoryTheory.Functor
