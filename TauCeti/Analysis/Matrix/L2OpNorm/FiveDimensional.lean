/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# An exact five-dimensional Euclidean operator norm

We compute the Euclidean operator norm of a matrix with orthogonal columns of unequal
lengths. Its Gram matrix is diagonal with largest entry `350`, so its operator norm is
`sqrt 350`, attained at the fourth coordinate vector. The computation works over both
`ℝ` and `ℂ` and uses the native Euclidean continuous linear map, not an entrywise norm.

The norm computation uses `Matrix.l2_opNorm_conjTranspose_mul_self` and
`Matrix.l2_opNorm_diagonal`; no eigenvalue ordering or spectral-measure construction is
needed for this orthogonal-column example.
-/

public section

open scoped Matrix Matrix.Norms.L2Operator

namespace TauCeti.MatrixNormExample

/-- A five-dimensional matrix whose columns are orthogonal and have distinct lengths. -/
def matrix (𝕜 : Type*) [RCLike 𝕜] : Matrix (Fin 5) (Fin 5) 𝕜 :=
  !![3, 8, 0, -10, 2;
     -3, 4, 1, 0, -7;
     3, -4, 1, 0, 7;
     3, 4, 0, 15, -3;
     3, -4, 0, -5, -13]

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The squared column lengths are `45`, `128`, `2`, `350`, and `280`; distinct columns
are orthogonal. -/
@[simp]
theorem conjTranspose_mul :
    (matrix 𝕜)ᴴ * matrix 𝕜 = Matrix.diagonal ![45, 128, 2, 350, 280] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      map_ofNat]

/-- The square of the Euclidean operator norm is the largest Gram diagonal entry. -/
theorem norm_toEuclideanCLM_sq :
    ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (matrix 𝕜)‖ ^ 2 = 350 := by
  rw [Matrix.l2_opNorm_toEuclideanCLM, pow_two,
    ← Matrix.l2_opNorm_conjTranspose_mul_self, conjTranspose_mul, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i ↦ ?_
    fin_cases i <;> norm_num
  · simpa using norm_le_pi_norm (![45, 128, 2, 350, 280] : Fin 5 → 𝕜) 3

/-- The Euclidean operator norm is exactly `sqrt 350`. -/
@[simp]
theorem norm_toEuclideanCLM :
    ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (matrix 𝕜)‖ = Real.sqrt 350 := by
  rw [← norm_toEuclideanCLM_sq (𝕜 := 𝕜), Real.sqrt_sq (norm_nonneg _)]

/-- The fourth coordinate vector is sent to the fourth column. Indices are zero-based. -/
@[simp]
theorem toEuclideanLin_single_three :
    Matrix.toEuclideanLin (matrix 𝕜) (EuclideanSpace.single 3 1) =
      WithLp.toLp 2 ![-10, 0, 0, 15, -5] := by
  ext i
  change (matrix 𝕜 *ᵥ Pi.single 3 1) i = ![-10, 0, 0, 15, -5] i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, matrix, Fin.sum_univ_succ, Pi.single_apply]

/-- The fourth unit coordinate vector attains the Euclidean operator norm. -/
theorem norm_toEuclideanCLM_basisFun_three :
    ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (matrix 𝕜) (EuclideanSpace.basisFun (Fin 5) 𝕜 3)‖ =
      ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (matrix 𝕜)‖ := by
  change ‖Matrix.toEuclideanLin (matrix 𝕜) (EuclideanSpace.basisFun (Fin 5) 𝕜 3)‖ = _
  rw [norm_toEuclideanCLM, EuclideanSpace.basisFun_apply, toEuclideanLin_single_three,
    EuclideanSpace.norm_eq]
  congr 1
  norm_num [Fin.sum_univ_succ]

end TauCeti.MatrixNormExample
