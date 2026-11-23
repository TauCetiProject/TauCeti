/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Determinants of antidiagonal block matrices

Mathlib computes the determinant of a block triangular matrix `[[A, B], [0, D]]` or
`[[A, 0], [C, D]]` (`Matrix.det_fromBlocks_zero₂₁`, `Matrix.det_fromBlocks_zero₁₂`). This file adds
the antidiagonal case: with square blocks of size `n`, `det [[0, B], [C, 0]] = (-1)ⁿ det B det C`.
It follows by factoring `[[0, B], [C, 0]] = [[B, 0], [0, C]] * J * [[1, 0], [0, -1]]`, where the
standard symplectic matrix `J` has determinant `1`.

## Main results

* `Matrix.det_fromBlocks_zero₁₁_zero₂₂`: the determinant of an antidiagonal block matrix
  `[[0, B], [C, 0]]` with square blocks of size `n` is `(-1)ⁿ det B det C`.
-/

public section

namespace Matrix

variable {l R : Type*} [Fintype l] [DecidableEq l] [CommRing R]

/-- **The determinant of an antidiagonal block matrix.** With square blocks of size `n`,
`det [[0, B], [C, 0]] = (-1)ⁿ det B det C`. -/
@[simp]
theorem det_fromBlocks_zero₁₁_zero₂₂ (B C : Matrix l l R) :
    (fromBlocks 0 B C 0).det = (-1) ^ Fintype.card l * B.det * C.det := by
  -- `[[0, B], [C, 0]] = [[B, 0], [0, C]] * J * [[1, 0], [0, -1]]`, and `det J = 1`.
  have h : fromBlocks 0 B C 0 = fromBlocks B 0 0 C * (J l R * fromBlocks 1 0 0 (-1)) := by
    simp [J, fromBlocks_multiply]
  rw [h]
  simp [det_J, det_fromBlocks_zero₂₁, det_neg]
  ring

end Matrix
