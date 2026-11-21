/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Invertibility of whiskered two-squares

Whiskering a two-square `w` at the top or at the bottom by an isomorphism changes it by
composition with an isomorphism, so the whiskered square is invertible exactly when `w` is. This
lets invertibility of a two-square be read back through conjugation by an isomorphism.

## Main declarations

* `CategoryTheory.TwoSquare.isIso_whiskerTop_iff`: a two-square whiskered at the top by an
  isomorphism is invertible if and only if the square is.
* `CategoryTheory.TwoSquare.isIso_whiskerBottom_iff`: the same at the bottom.
-/

public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T T' : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B B' : C₃ ⥤ C₄}

/-- A two-square whiskered at the top by an isomorphism is invertible if and only if the square
is. -/
theorem TwoSquare.isIso_whiskerTop_iff (w : TwoSquare T' L R B) (α : T ⟶ T') [IsIso α] :
    IsIso (w.whiskerTop α) ↔ IsIso w :=
  isIso_comp_left_iff (Functor.whiskerRight α R) (g := w)

/-- A two-square whiskered at the bottom by an isomorphism is invertible if and only if the
square is. -/
theorem TwoSquare.isIso_whiskerBottom_iff (w : TwoSquare T L R B) (α : B ⟶ B') [IsIso α] :
    IsIso (w.whiskerBottom α) ↔ IsIso w :=
  isIso_comp_right_iff (Functor.whiskerLeft L α) (g := w)

end CategoryTheory
