/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
public import TauCeti.Analysis.Matrix.SampleSecondMoment
import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# The operator norm of a sample covariance matrix

For a `p × n` data matrix `X`, the Euclidean operator norm of the sample covariance `X Xᴴ / n`
is `‖X‖² / n`, the squared operator norm of the normalized data matrix `X / √n`. Since the sample
covariance is positive semidefinite, this is also its largest eigenvalue. Operator-norm bounds
for the data matrix, for instance after truncating its entries, therefore control the upper edge
of the covariance spectrum. The identities hold for an empty sample, whose covariance is zero.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 p n : Type*} [RCLike 𝕜] [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n]

/-- The Euclidean operator norm of the sample covariance of `X` is `‖X‖² / n`. -/
theorem l2_opNorm_sampleCovariance (X : Matrix p n 𝕜) :
    ‖sampleCovariance X‖ = ‖X‖ ^ 2 / Fintype.card n := by
  rw [sampleCovariance_def, RCLike.real_smul_eq_coe_smul (K := 𝕜), norm_smul,
    l2_opNorm_mul_conjTranspose_self, ← sq, RCLike.norm_ofReal, abs_of_nonneg (by positivity),
    one_div, inv_mul_eq_div]

/-- The largest eigenvalue of the sample covariance of `X` is `‖X‖² / n`. -/
theorem eigenvalues₀_zero_sampleCovariance [Nonempty p] (X : Matrix p n 𝕜) :
    (isHermitian_sampleCovariance X).eigenvalues₀ ⟨0, Fintype.card_pos⟩ =
      ‖X‖ ^ 2 / Fintype.card n := by
  rw [← l2_opNorm_sampleCovariance, (posSemidef_sampleCovariance X).l2_opNorm_eq_eigenvalues₀_zero]

end Matrix
