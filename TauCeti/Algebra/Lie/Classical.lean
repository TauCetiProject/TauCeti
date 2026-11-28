/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The hyperbolic Gram matrix `JD`

Mathlib's `LieAlgebra.Orthogonal.JD l R` is the block matrix `(0 1; 1 0)` on `l ⊕ l`, the Gram
matrix of the split form defining the classical Lie algebra of type `D`. Read as a hermitian Gram
matrix, it is the Gram matrix of the hyperbolic space on `l ⊕ l` whose two copies of `l` span dual
isotropic subspaces. This file records that it is hermitian and is its own inverse.

## Main results

* `LieAlgebra.Orthogonal.isHermitian_JD`: `(JD l R)ᴴ = JD l R`.
* `LieAlgebra.Orthogonal.JD_mul_JD`: `JD l R * JD l R = 1`.
* `LieAlgebra.Orthogonal.isUnit_JD`: `JD l R` is invertible.
-/

public section

open Matrix

namespace LieAlgebra.Orthogonal

variable (l R : Type*) [DecidableEq l] [CommRing R]

/-- The hyperbolic Gram matrix `(0 1; 1 0)` is hermitian. -/
theorem isHermitian_JD [StarRing R] : Matrix.IsHermitian (JD l R) := by
  rw [IsHermitian, JD, fromBlocks_conjTranspose]
  simp

variable [Fintype l]

/-- The hyperbolic Gram matrix `(0 1; 1 0)` is its own inverse. -/
@[simp]
theorem JD_mul_JD : JD l R * JD l R = 1 := by
  simp [JD, fromBlocks_multiply]

/-- The hyperbolic Gram matrix `(0 1; 1 0)` is invertible. -/
theorem isUnit_JD : IsUnit (JD l R) :=
  IsUnit.of_mul_eq_one_right _ (JD_mul_JD l R)

end LieAlgebra.Orthogonal
