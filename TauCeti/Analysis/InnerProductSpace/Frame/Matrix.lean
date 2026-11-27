/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Frame.Basic

/-!
# Matrix of a frame operator

An identity for the product of a rectangular matrix with its conjugate transpose gives the frame
operator of its columns. In particular, coordinate orthogonality across the rows gives a tight
frame bound for a family written in Euclidean coordinates.
-/

public section

open scoped Matrix

namespace Matrix

/-- The frame operator of the columns of `A` is represented by `A * Aᴴ` in the standard
orthonormal basis. -/
theorem toEuclideanLin_mul_conjTranspose_eq_frameOperator {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix m n 𝕜) :
    (A * Aᴴ).toEuclideanLin = TauCeti.frameOperator 𝕜 (fun j ↦ WithLp.toLp 2 (A.col j)) := by
  ext x i
  simp only [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.conjTranspose_apply, TauCeti.frameOperator_apply, PiLp.inner_apply, RCLike.inner_apply',
    RCLike.star_def, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.toLp_apply, Finset.sum_apply,
    Pi.smul_apply, Matrix.col_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_comm (A i _)]

end Matrix
