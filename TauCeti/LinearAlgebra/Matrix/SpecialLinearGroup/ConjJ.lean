/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Conjugation by a coordinate reflection in the special linear group

Conjugating a two-by-two matrix by `diag(-1, 1)` negates both off-diagonal entries and
preserves its determinant. The canonical `conjJ` operation is available over every commutative
ring, for modular-form conjugation and reflection of binary quadratic forms.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- Conjugation by the coordinate reflection `diag(-1, 1)` in `SL₂(R)`. -/
def conjJ (γ : SL(2, R)) : SL(2, R) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    simpa only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, neg_mul_neg] using γ.det_coe⟩

@[simp] theorem coe_conjJ (γ : SL(2, R)) :
    (conjJ γ : Matrix (Fin 2) (Fin 2) R) = !![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1] := (rfl)

end Matrix.SpecialLinearGroup
