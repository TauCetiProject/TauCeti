/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Ordered eigenvalues of Gram matrices

The decreasing eigenvalues of the row and column Gram matrices of a rectangular matrix are
the squares of its singular values, up to the dimension of the corresponding Gram matrix.
This includes zero eigenvalues when the two Gram matrices have different sizes or the
rectangular matrix is rank deficient.
-/

public section

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The eigenvalues of the row Gram matrix are the squared singular values, in decreasing
order, for all indices below the row dimension. -/
theorem eigenvalues₀_mul_conjTranspose_self_eq_sq_singularValues
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card m)) :
    (isHermitian_mul_conjTranspose_self A).eigenvalues₀ i =
      (toEuclideanLin A).singularValues i ^ 2 := by
  rw [LinearMap.sq_singularValues_eq_eigenvalues_self_comp_adjoint _
    finrank_euclideanSpace i.isLt, IsHermitian.eigenvalues₀]
  have h : toEuclideanLin (A * Aᴴ) = toEuclideanLin A ∘ₗ (toEuclideanLin A).adjoint := by
    rw [← toEuclideanLin_conjTranspose_eq_adjoint]
    exact toLpLin_mul_same 2 A Aᴴ
  exact congrFun (LinearMap.IsSymmetric.eigenvalues_congr h _ _ _) i

omit [DecidableEq m] in
/-- The eigenvalues of the column Gram matrix are the squared singular values, in decreasing
order, for all indices below the column dimension. -/
theorem eigenvalues₀_conjTranspose_mul_self_eq_sq_singularValues
    (A : Matrix m n 𝕜) (i : Fin (Fintype.card n)) :
    (isHermitian_conjTranspose_mul_self A).eigenvalues₀ i =
      (toEuclideanLin A).singularValues i ^ 2 := by
  classical
  simpa only [conjTranspose_conjTranspose, toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.singularValues_adjoint] using
    eigenvalues₀_mul_conjTranspose_self_eq_sq_singularValues Aᴴ i

end Matrix
