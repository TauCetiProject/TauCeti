/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Isomorphism classes of vertices in composable strings

All vertices of a composable string in a groupoid have the same isomorphism class.
-/

public noncomputable section

namespace CategoryTheory.ComposableArrows

variable {C : Type*} [Category C] [IsGroupoid C] {n : ℕ}

/-- All vertices of a composable string in a groupoid represent the same isomorphism class. -/
@[simp]
theorem quotient_mk_obj (F : ComposableArrows C n) (i : Fin (n + 1)) :
    Quotient.mk (isIsomorphicSetoid C) (F.obj i) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) := by
  symm
  exact Quotient.sound (s := isIsomorphicSetoid C)
    ⟨asIso (F.map (homOfLE (Fin.zero_le i)))⟩


omit [IsGroupoid C] in
/-- The composable arrows `mk₁ f` and `mk₁ f'` are equal exactly when `f` and `f'` are equal
as arrows. -/
lemma mk₁_eq_mk₁_iff {X₀ X₁ Y₀ Y₁ : C} {f : X₀ ⟶ X₁} {f' : Y₀ ⟶ Y₁} :
    mk₁ f = mk₁ f' ↔ Arrow.mk f = Arrow.mk f' :=
  arrowEquiv.apply_eq_iff_eq.symm

end CategoryTheory.ComposableArrows
