/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Convolution of multivariate Gaussian laws

Independent Gaussian vectors add their means and covariance matrices. The convolution identity
allows singular covariances and empty coordinate types. In particular, exponentiating this sum
identifies componentwise products of independent multivariate log-normal vectors.

The proof uses Mathlib's `charFun_multivariateGaussian` and characteristic-function uniqueness,
following the scalar `ProbabilityTheory.gaussianReal_conv_gaussianReal`.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Convolution adds the means and positive-semidefinite covariance matrices of Gaussian laws.
No nonsingularity or nonemptiness assumption is needed. -/
@[simp]
theorem multivariateGaussian_conv_multivariateGaussian (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef) :
    (multivariateGaussian m₁ S₁) ∗ (multivariateGaussian m₂ S₂) =
      multivariateGaussian (m₁ + m₂) (S₁ + S₂) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv, charFun_multivariateGaussian hS₁, charFun_multivariateGaussian hS₂,
    charFun_multivariateGaussian (hS₁.add hS₂), ← Complex.exp_add]
  congr 1
  simp only [inner_add_right, Matrix.add_mulVec, dotProduct_add, Complex.ofReal_add]
  ring

end TauCeti.Probability
