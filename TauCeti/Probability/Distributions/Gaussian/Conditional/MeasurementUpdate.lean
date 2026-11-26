/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Control.Riccati
public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic

/-!
# The measurement update as a Gaussian conditional covariance

A state with covariance `P`, observed through `C` with independent noise of covariance `R`, forms
with the observation a jointly Gaussian vector whose covariance has the blocks `P`, `P Cᵀ`, `C P`
and the innovation covariance `C P Cᵀ + R`. When the innovation covariance is positive definite,
the conditional covariance of the state given the observation, `Matrix.gaussianCondCov` of that
block matrix, is the measurement update of the Kalman filter. This identifies the covariance
update of one filter step with the Schur-complement conditional covariance
`Matrix.gaussianCondCov` of the joint block covariance.

## Main results

* `Matrix.gaussianCondCov_fromBlocks_innovationCov`: the conditional covariance of the state given
  one observation is `Matrix.measurementUpdate C R P`.

## References

* Brian D. O. Anderson and John B. Moore, *Optimal Filtering*, Prentice-Hall, 1979, §3.1.
-/

public section

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  {P : Matrix ι ι ℝ} {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

/-- When the innovation covariance `S = C P Cᵀ + R` is positive definite, the conditional
covariance of the first block of the block matrix with blocks `P`, `P Cᵀ`, `C P` and `S`, which is
the joint covariance of a state and of its observation through `C` with noise covariance `R`, is
the measurement update of `P`. -/
theorem gaussianCondCov_fromBlocks_innovationCov (hS : (innovationCov C R P).PosDef) :
    (fromBlocks P (P * Cᵀ) (C * P) (innovationCov C R P)).gaussianCondCov =
      measurementUpdate C R P := by
  set M := fromBlocks P (P * Cᵀ) (C * P) (innovationCov C R P)
  have h₁₁ : M.submatrix Sum.inl Sum.inl = P := by ext; simp [M]
  have h₁₂ : M.submatrix Sum.inl Sum.inr = P * Cᵀ := by ext; simp [M]
  have h₂₁ : M.submatrix Sum.inr Sum.inl = C * P := by ext; simp [M]
  have h₂₂ : M.submatrix Sum.inr Sum.inr = innovationCov C R P := by ext; simp [M]
  rw [gaussianCondCov_of_posDef (h₂₂ ▸ hS), h₁₁, h₁₂, h₂₁, h₂₂, measurementUpdate_eq_sub]

end Matrix
