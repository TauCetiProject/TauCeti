/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

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

open Preadditive in
private theorem isIso_id_sub_comp_swap {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X)
    [IsIso (𝟙 X - a ≫ b)] : IsIso (𝟙 Y - b ≫ a) := by
  refine ⟨𝟙 Y + b ≫ inv (𝟙 X - a ≫ b) ≫ a, ?_, ?_⟩
  · have := congr(b ≫ $(IsIso.hom_inv_id (𝟙 X - a ≫ b)) ≫ a)
    simp only [sub_comp, comp_sub, comp_add, Category.assoc, Category.id_comp,
      Category.comp_id] at this ⊢
    linear_combination (norm := abel) this
  · have := congr(b ≫ $(IsIso.inv_hom_id (𝟙 X - a ≫ b)) ≫ a)
    simp only [comp_sub, sub_comp, add_comp, Category.assoc, Category.id_comp,
      Category.comp_id] at this ⊢
    linear_combination (norm := abel) this

/-- **Jacobson's lemma**: `𝟙 X - a ≫ b` is invertible exactly when `𝟙 Y - b ≫ a` is. -/
theorem isIso_id_sub_comp_comm {X Y : C} (a : X ⟶ Y) (b : Y ⟶ X) :
    IsIso (𝟙 X - a ≫ b) ↔ IsIso (𝟙 Y - b ≫ a) :=
  ⟨fun _ => isIso_id_sub_comp_swap a b, fun _ => isIso_id_sub_comp_swap b a⟩

end CategoryTheory
