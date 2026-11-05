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

end CategoryTheory.ComposableArrows
