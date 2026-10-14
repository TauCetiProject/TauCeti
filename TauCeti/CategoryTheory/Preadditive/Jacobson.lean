/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.Abel

/-!
# Jacobson's lemma in a preadditive category

For morphisms `a : X ⟶ Y` and `b : Y ⟶ X`, the endomorphisms `𝟙 X - a ≫ b` and
`𝟙 Y - b ≫ a` are invertible together. The inverse in one direction is obtained from the other
by the formula `(𝟙 Y - b ≫ a)⁻¹ = 𝟙 Y + b ≫ (𝟙 X - a ≫ b)⁻¹ ≫ a`.

`CategoryTheory.isIso_id_sub_comp_comm` is the categorical form of Jacobson's lemma for rings.
It applies even when the two morphisms have different sources and targets, and gives the
left-right symmetry of the radical of a preadditive category.
-/

public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

private theorem isIso_id_sub_comp_swap {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X)
    (h : IsIso (𝟙 X - a ≫ b)) : IsIso (𝟙 Y - b ≫ a) := by
  obtain ⟨w, hw₁, hw₂⟩ := h.out
  rw [Preadditive.sub_comp, Category.id_comp, Category.assoc] at hw₁
  rw [Preadditive.comp_sub, Category.comp_id] at hw₂
  -- `hw₁ : w - a ≫ b ≫ w = 𝟙 X` and `hw₂ : w - w ≫ a ≫ b = 𝟙 X`
  have key₁ : a ≫ b ≫ w ≫ a = w ≫ a - a := by
    have h₁ : a ≫ b ≫ w = w - 𝟙 X := by
      rw [eq_sub_iff_add_eq, ← hw₁]; abel
    have := congrArg (fun t : X ⟶ X => t ≫ a) h₁
    simpa [Preadditive.sub_comp] using this
  have key₂ : w ≫ a ≫ b ≫ a = w ≫ a - a := by
    have h₂ : w ≫ a ≫ b = w - 𝟙 X := by
      rw [eq_sub_iff_add_eq, ← hw₂]; abel
    have := congrArg (fun t : X ⟶ X => t ≫ a) h₂
    simpa [Preadditive.sub_comp] using this
  refine ⟨⟨𝟙 Y + b ≫ w ≫ a, ?_, ?_⟩⟩
  · simp only [Preadditive.sub_comp, Preadditive.comp_add, Category.id_comp, Category.comp_id,
      Category.assoc, key₁, Preadditive.comp_sub]
    abel
  · simp only [Preadditive.add_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
      Category.assoc, key₂, Preadditive.comp_sub]
    abel

/-- **Jacobson's lemma**: `𝟙 X - a ≫ b` is invertible exactly when `𝟙 Y - b ≫ a` is. -/
theorem isIso_id_sub_comp_comm {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X) :
    IsIso (𝟙 X - a ≫ b) ↔ IsIso (𝟙 Y - b ≫ a) :=
  ⟨isIso_id_sub_comp_swap a b, isIso_id_sub_comp_swap b a⟩

end CategoryTheory
