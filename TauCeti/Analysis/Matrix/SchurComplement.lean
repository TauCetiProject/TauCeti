/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.CovariancePseudoInverse
public import TauCeti.LinearAlgebra.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.SchurComplement
public import TauCeti.Analysis.Matrix.PosSemidef.Block

/-!
# Generalized Schur complements of covariance matrices

The Schur complement formed with the covariance pseudoinverse is positive semidefinite
for every positive-semidefinite block matrix. This permits singular observed covariances
in the conditional-covariance formula, including zero covariance and empty coordinate types.
The file also proves the block cancellation identity `S₁₂ S₂₂⁺ S₂₂ = S₁₂` for
positive-semidefinite block matrices: the kernel of `S₂₂` is contained in that of `S₁₂`.

The proofs use `Matrix.PosSemidef.schur_complement₂₂` and the second Penrose equation for
`Matrix.covariancePseudoInverse`.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley,
  2003, Chapter 2.
-/

public section

namespace Matrix

variable {m n : Type*}

/-- Regression through a possibly singular covariance block preserves the cross covariance.
This is the block cancellation identity used by Gaussian regression. -/
theorem PosSemidef.toBlocks₁₂_mul_covariancePseudoInverse_mul
    [Finite m] [Fintype n] [DecidableEq n] {S : Matrix (m ⊕ n) (m ⊕ n) ℝ}
    (hS : S.PosSemidef) :
    S.toBlocks₁₂ * S.toBlocks₂₂.covariancePseudoInverse * S.toBlocks₂₂ = S.toBlocks₁₂ := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  have hD := isMoorePenroseInverse_covariancePseudoInverse (hS.submatrix Sum.inr)
  rw [← toBlocks₂₂_eq_submatrix] at hD
  have hker : S.toBlocks₂₂.toEuclideanLin
      (S.toBlocks₂₂.covariancePseudoInverse.toEuclideanLin (S.toBlocks₂₂.toEuclideanLin x) - x) =
      0 := by
    rw [map_sub, hD.apply_apply_apply, sub_self]
  have h := hS.ker_toEuclideanLin_toBlocks₂₂_le hker
  simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero, toLpLin_mul_same,
    LinearMap.comp_apply] using h

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
