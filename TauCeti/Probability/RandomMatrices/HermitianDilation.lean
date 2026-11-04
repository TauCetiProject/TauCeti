/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Hermitian dilation of a rectangular matrix

The Hermitian dilation embeds a rectangular matrix into a Hermitian block matrix. Its square has
the two Gram matrices on the diagonal, which lets results for Hermitian matrices be applied to
rectangular matrices.
-/

public section

namespace Matrix

variable {m n : Type*}
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Hermitian dilation of a rectangular matrix `A`. -/
def hermitianDilation (A : Matrix m n 𝕜) : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  fromBlocks 0 A Aᴴ 0

/-- The Hermitian dilation of a matrix is Hermitian. -/
theorem isHermitian_hermitianDilation (A : Matrix m n 𝕜) :
    (hermitianDilation A).IsHermitian := by
  classical
  exact IsHermitian.fromBlocks (by simp) (by simp) (by simp)

/-- The square of the Hermitian dilation has the Gram matrices on its diagonal. -/
theorem hermitianDilation_sq [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n 𝕜) :
    hermitianDilation A ^ 2 = fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
  rw [pow_two, hermitianDilation, Matrix.fromBlocks_multiply]
  simp

end Matrix
