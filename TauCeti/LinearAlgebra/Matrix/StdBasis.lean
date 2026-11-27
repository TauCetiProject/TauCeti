/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Coordinates in the standard basis of matrices

The coordinate of a matrix `M` at the index `(i, j)` in the standard basis `Matrix.stdBasis` of
`Matrix m n R` is its entry `M i j` (`Matrix.stdBasis_repr_apply`).
-/

public section

namespace Matrix

variable {R m n : Type*} [Fintype m] [Finite n] [Semiring R]

/-- The coordinate of a matrix at `p` in the standard basis is its entry at `p`. -/
@[simp]
theorem stdBasis_repr_apply (M : Matrix m n R) (p : m × n) :
    (stdBasis R m n).repr M p = M p.1 p.2 := by
  simp [stdBasis]

end Matrix
