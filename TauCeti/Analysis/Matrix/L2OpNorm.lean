/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The `ℓ²` operator norm as a normed real algebra

Mathlib's scoped `ℓ²` operator norm (`Matrix.Norms.L2Operator`) makes `Matrix n n 𝕜` a normed
`𝕜`-algebra, for `𝕜 = ℝ` or `ℂ` (any `RCLike` field). Results about continuous functional
calculi and the exponential stated over `ℝ` additionally need a normed `ℝ`-algebra structure on
`Matrix n n 𝕜`. This file provides it, extending the existing `ℝ`-algebra structure on matrices
rather than restricting scalars, so that no algebra diamond arises.

## Main results

* `Matrix.l2OpNormedAlgebraReal`: `Matrix n n 𝕜` with the `ℓ²` operator norm, as a normed
  `ℝ`-algebra;
* `Matrix.norm_entry_le_l2_opNorm`: every entry of a matrix is bounded in norm by its `ℓ²`
  operator norm;
* `Matrix.l2_opNorm_sub_diagonal_diag_le`: zeroing the diagonal of a square matrix at most doubles
  its `ℓ²` operator norm.
-/

public section

namespace Matrix

variable {m n 𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- `Matrix n n 𝕜` with the `ℓ²` operator norm, as a normed `ℝ`-algebra. It extends the existing
`ℝ`-algebra structure rather than restricting scalars, so that no algebra diamond arises. -/
protected noncomputable abbrev l2OpNormedAlgebraReal : NormedAlgebra ℝ (Matrix n n 𝕜) where
  __ := (inferInstance : Algebra ℝ (Matrix n n 𝕜))
  norm_smul_le r A := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) r A]
    exact (norm_smul_le _ _).trans_eq (by rw [RCLike.norm_ofReal, Real.norm_eq_abs])

open scoped Matrix.Norms.L2Operator in
/-- Every entry of a matrix has norm at most its `ℓ²` operator norm. -/
theorem norm_entry_le_l2_opNorm (A : Matrix m n 𝕜) (i : m) (j : n) :
    ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace 𝕜 n := WithLp.toLp 2 (Pi.single j (1 : 𝕜))
  let y : EuclideanSpace 𝕜 m := (EuclideanSpace.equiv m 𝕜).symm (A *ᵥ e)
  have hy_apply : y i = A i j := by
    simp [y, e, mulVec_single]
  have hy_le : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have he_norm : ‖e‖ ≤ 1 := by
    simp [e]
  calc ‖A i j‖ = ‖y i‖ := by rw [hy_apply]
    _ ≤ ‖y‖ := hy_le
    _ ≤ ‖A‖ * ‖e‖ := A.l2_opNorm_mulVec e
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left he_norm (norm_nonneg A)
    _ = ‖A‖ := mul_one _

open scoped Matrix.Norms.L2Operator in
/-- Removing the diagonal of a square matrix increases its `ℓ²` operator norm by at most a factor
of `2`. -/
theorem l2_opNorm_sub_diagonal_diag_le (A : Matrix n n 𝕜) :
    ‖A - diagonal A.diag‖ ≤ 2 * ‖A‖ := by
  have hdiag : ‖(diagonal A.diag : Matrix n n 𝕜)‖ ≤ ‖A‖ := by
    rw [l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr fun i ↦ A.norm_entry_le_l2_opNorm i i
  linarith [norm_sub_le A (diagonal A.diag)]

end Matrix
