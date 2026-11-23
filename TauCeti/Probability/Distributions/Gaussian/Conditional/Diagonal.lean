/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic

/-!
# Gaussian conditioning on diagonal observed covariances

For a nonnegative diagonal observed covariance, the conditional mean and covariance are finite
sums with reciprocal diagonal entries. Zero-variance observations contribute nothing (`0⁻¹ = 0`),
while positive-variance observations retain their reciprocal weights. In contrast, the totalized
matrix inverse of a singular diagonal matrix is the zero matrix, losing even those weights.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003,
  Chapter 2.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory

namespace EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- With diagonal nonnegative observed covariance, the regression mean is a sum over observed
coordinates, and zero-variance coordinates have zero coefficient. -/
theorem gaussianCondMean_apply_of_diagonal (m : EuclideanSpace ℝ (ι ⊕ κ))
    {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {d : κ → ℝ}
    (hS₂₂ : S.submatrix Sum.inr Sum.inr = diagonal d) (hd : ∀ k, 0 ≤ d k)
    (x₂ : EuclideanSpace ℝ κ) (i : ι) :
    m.gaussianCondMean S x₂ i = m (Sum.inl i) +
      ∑ k, S (Sum.inl i) (Sum.inr k) * (d k)⁻¹ * (x₂ k - m (Sum.inr k)) := by
  rw [gaussianCondMean_def, hS₂₂, covariancePseudoInverse_diagonal hd]
  -- Read the Euclidean operator and the block-coordinate equivalence on coordinates.
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, EuclideanSpace.sumEquivProd]

end EuclideanSpace

namespace Matrix

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-- With diagonal nonnegative observed covariance, the Schur correction is the sum of the
coordinatewise regression corrections, with zero contribution from zero-variance observations. -/
theorem gaussianCondCov_apply_of_diagonal {S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} {d : κ → ℝ}
    (hS₂₂ : S.submatrix Sum.inr Sum.inr = diagonal d) (hd : ∀ k, 0 ≤ d k) (i j : ι) :
    S.gaussianCondCov i j = S (Sum.inl i) (Sum.inl j) -
      ∑ k, S (Sum.inl i) (Sum.inr k) * (d k)⁻¹ * S (Sum.inr k) (Sum.inl j) := by
  rw [gaussianCondCov_def, hS₂₂, covariancePseudoInverse_diagonal hd]
  simp only [Matrix.sub_apply]
  congr 1
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.submatrix_apply]

end Matrix
