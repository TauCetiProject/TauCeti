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
noncomputable def isoNegThird {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ X⟦(1 : ℤ)⟧) : Triangle.mk a (-b) (-c) ≅ Triangle.mk a b c :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (-Iso.refl _)
    (by simp) (by simp) (by simp)

variable {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ X⟦(1 : ℤ)⟧)

@[simp]
theorem isoNegThird_hom_hom₁ : (isoNegThird a b c).hom.hom₁ = 𝟙 X := by
  simp only [isoNegThird, Triangle.isoMk_hom, Triangle.homMk_hom₁,
    Iso.refl_hom, Triangle.mk_obj₁]

@[simp]
theorem isoNegThird_hom_hom₂ : (isoNegThird a b c).hom.hom₂ = 𝟙 Y := by
  simp only [isoNegThird, Triangle.isoMk_hom, Triangle.homMk_hom₂,
    Iso.refl_hom, Triangle.mk_obj₂]

@[simp]
theorem isoNegThird_hom_hom₃ : (isoNegThird a b c).hom.hom₃ = -𝟙 Z := by
  simp only [isoNegThird, Triangle.isoMk_hom, Triangle.homMk_hom₃,
    Preadditive.neg_iso_hom, Iso.refl_hom, Triangle.mk_obj₃]

@[simp]
theorem isoNegThird_inv_hom₁ : (isoNegThird a b c).inv.hom₁ = 𝟙 X := by
  simp only [isoNegThird, Triangle.isoMk_inv, Triangle.homMk_hom₁,
    Iso.refl_inv, Triangle.mk_obj₁]

@[simp]
theorem isoNegThird_inv_hom₂ : (isoNegThird a b c).inv.hom₂ = 𝟙 Y := by
  simp only [isoNegThird, Triangle.isoMk_inv, Triangle.homMk_hom₂,
    Iso.refl_inv, Triangle.mk_obj₂]

@[simp]
theorem isoNegThird_inv_hom₃ : (isoNegThird a b c).inv.hom₃ = -𝟙 Z := by
  simp only [isoNegThird, Triangle.isoMk_inv, Triangle.homMk_hom₃,
    Preadditive.neg_iso_inv, Iso.refl_inv, Triangle.mk_obj₃]

end CategoryTheory.Pretriangulated.Triangle
