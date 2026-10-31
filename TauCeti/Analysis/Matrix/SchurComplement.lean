/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CovariancePseudoInverse
public import TauCeti.LinearAlgebra.Matrix.SchurComplement

/-!
# Generalized Schur complements of covariance matrices

The Schur complement formed with the covariance pseudoinverse is positive semidefinite
for every positive-semidefinite block matrix. This permits singular observed covariances
in the conditional-covariance formula, including zero covariance and empty coordinate types.

The proofs use `Matrix.PosSemidef.schur_complement₂₂` and the second Penrose equation for
`Matrix.covariancePseudoInverse`.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley,
  2003, Chapter 2.
-/

public section

namespace Matrix

variable {m n : Type*}

/-- The generalized Schur complement of the observed block of a covariance matrix is
positive semidefinite, with no nonsingularity assumption on that block. -/
theorem PosSemidef.schur_complement₂₂_covariancePseudoInverse
    [Finite m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {D : Matrix n n ℝ}
    (h : (fromBlocks A B Bᴴ D).PosSemidef) :
    (A - B * D.covariancePseudoInverse * Bᴴ).PosSemidef :=
  h.schur_complement₂₂ (posSemidef_covariancePseudoInverse D).isHermitian
    (covariancePseudoInverse_mul_self_mul D)

/-- The generalized Schur complement of the first block of a covariance matrix is
positive semidefinite, including singular and zero first blocks. -/
theorem PosSemidef.schur_complement₁₁_covariancePseudoInverse
    [Fintype m] [DecidableEq m] [Finite n]
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {D : Matrix n n ℝ}
    (h : (fromBlocks A B Bᴴ D).PosSemidef) :
    (D - Bᴴ * A.covariancePseudoInverse * B).PosSemidef :=
  h.schur_complement₁₁ (posSemidef_covariancePseudoInverse A).isHermitian
    (covariancePseudoInverse_mul_self_mul A)

end Matrix
