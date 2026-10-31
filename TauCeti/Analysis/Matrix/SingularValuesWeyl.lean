/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Weyl's perturbation bound for singular values of rectangular matrices

For two matrices of the same rectangular shape, each singular value, indexed by `ℕ` and padded by
zeros past the rank bound, moves by at most the spectral (`ℓ²` operator) norm of the difference.
The singular values are those of `Matrix.toEuclideanLin`, and the bound is the matrix form of
`LinearMap.abs_singularValues_sub_singularValues_le`.

## Main results

* `Matrix.abs_singularValues_toEuclideanLin_sub_le`: `|σₙ(A) - σₙ(B)| ≤ ‖A - B‖`.
* `Matrix.singularValues_toEuclideanLin_le_add_norm_sub`: `σₙ(A) ≤ σₙ(B) + ‖A - B‖`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997,
  Corollary III.2.6.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **Weyl's perturbation bound for rectangular matrices.** For `A B : Matrix ι κ 𝕜`, every
zero-padded singular value satisfies `|σₙ(A) - σₙ(B)| ≤ ‖A - B‖`, where the norm is the `ℓ²`
operator norm. -/
theorem abs_singularValues_toEuclideanLin_sub_le (A B : Matrix ι κ 𝕜) (n : ℕ) :
    |(toEuclideanLin A).singularValues n - (toEuclideanLin B).singularValues n| ≤ ‖A - B‖ := by
  simpa [l2_opNorm_def] using
    LinearMap.abs_singularValues_sub_singularValues_le (toEuclideanLin A) (toEuclideanLin B) n

/-- One-sided form of `Matrix.abs_singularValues_toEuclideanLin_sub_le`. -/
theorem singularValues_toEuclideanLin_le_add_norm_sub (A B : Matrix ι κ 𝕜) (n : ℕ) :
    (toEuclideanLin A).singularValues n ≤ (toEuclideanLin B).singularValues n + ‖A - B‖ := by
  have h := (abs_le.mp (abs_singularValues_toEuclideanLin_sub_le A B n)).2
  linarith

end Matrix
