/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.CategoryTheory.Triangulated.Basic

/-!
# Signs of triangle arrows

Negating the identity on the third object gives an isomorphism between triangles differing
by the signs of their second and third arrows. This comparison is used to identify the rotation
of a curved DG right-module cone triangle in `StablePeriodicCurved`, Layer 5.
-/

public section

namespace CategoryTheory.Pretriangulated.Triangle

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]

/-- Negating the third object of a triangle negates its two adjacent arrows. -/
@[expose, simps! hom_hom₁ hom_hom₂ hom_hom₃]
noncomputable def isoNegThird {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ X⟦(1 : ℤ)⟧) : Triangle.mk a (-b) (-c) ≅ Triangle.mk a b c :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (-Iso.refl _)
    (by simp) (by simp) (by simp)

end CategoryTheory.Pretriangulated.Triangle
