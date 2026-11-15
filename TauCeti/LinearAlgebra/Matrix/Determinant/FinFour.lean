/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant of a `4 × 4` matrix

This file expands the determinant of a `4 × 4` matrix along its first row into the products of its
entries, extending Mathlib's `Matrix.det_fin_two` and `Matrix.det_fin_three`. It turns identities
between volumes of four vectors in an oriented four-space into polynomial identities in their
coordinates.

## Main results

* `Matrix.det_fin_four`: the determinant of a `4 × 4` matrix, expanded.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The determinant of a `4 × 4` matrix, expanded along the first row. -/
theorem det_fin_four (m : Matrix (Fin 4) (Fin 4) R) : m.det =
    m 0 0 * (m 1 1 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 1 * m 3 3 - m 2 3 * m 3 1)
      + m 1 3 * (m 2 1 * m 3 2 - m 2 2 * m 3 1))
    - m 0 1 * (m 1 0 * (m 2 2 * m 3 3 - m 2 3 * m 3 2) - m 1 2 * (m 2 0 * m 3 3 - m 2 3 * m 3 0)
      + m 1 3 * (m 2 0 * m 3 2 - m 2 2 * m 3 0))
    + m 0 2 * (m 1 0 * (m 2 1 * m 3 3 - m 2 3 * m 3 1) - m 1 1 * (m 2 0 * m 3 3 - m 2 3 * m 3 0)
      + m 1 3 * (m 2 0 * m 3 1 - m 2 1 * m 3 0))
    - m 0 3 * (m 1 0 * (m 2 1 * m 3 2 - m 2 2 * m 3 1) - m 1 1 * (m 2 0 * m 3 2 - m 2 2 * m 3 0)
      + m 1 2 * (m 2 0 * m 3 1 - m 2 1 * m 3 0)) := by
  have h₁ : (Fin.succAbove 1 2 : Fin 4) = 3 := rfl
  have h₂ : (Fin.succAbove 2 2 : Fin 4) = 3 := rfl
  have h₃ : (Fin.succAbove 3 2 : Fin 4) = 2 := rfl
  rw [det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_fin_three, submatrix_apply, Fin.succ_succAbove_one, h₁, h₂, h₃]
  ring

end Matrix
