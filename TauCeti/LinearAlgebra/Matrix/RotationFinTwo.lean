/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Tactic.FinCases

/-!
# The rotation `!![0, -1; 1, 0]` and the big cell of `2 × 2` matrices

The rotation `!![0, -1; 1, 0]` is invertible over every ring
(`TauCeti.isUnit_rotation_fin_two`). Over a division ring, every `2 × 2` matrix whose lower left
entry is nonzero is an upper triangular matrix times the rotation times a unipotent upper triangular
matrix (`TauCeti.eq_upper_mul_rotation_mul_upper_fin_two`).
-/

public section

namespace TauCeti

/-- The rotation `!![0, -1; 1, 0]` is invertible, with inverse `!![0, 1; -1, 0]`. -/
theorem isUnit_rotation_fin_two (R : Type*) [Ring R] :
    IsUnit (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) := by
  refine ⟨⟨!![0, -1; 1, 0], !![0, 1; -1, 0], ?_, ?_⟩, rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

/-- Over a division ring, a `2 × 2` matrix with nonzero lower left entry is an upper triangular
matrix times the rotation `!![0, -1; 1, 0]` times a unipotent upper triangular matrix. -/
theorem eq_upper_mul_rotation_mul_upper_fin_two {D : Type*} [DivisionRing D]
    (M : Matrix (Fin 2) (Fin 2) D) (hc : M 1 0 ≠ 0) :
    M = !![M 0 0 * (M 1 0)⁻¹ * M 1 1 - M 0 1, M 0 0; 0, M 1 0] * !![0, -1; 1, 0] *
      !![1, (M 1 0)⁻¹ * M 1 1; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, mul_assoc, mul_inv_cancel_left₀ hc]

end TauCeti
