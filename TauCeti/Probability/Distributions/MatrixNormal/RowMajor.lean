/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix
public import TauCeti.Probability.Distributions.MatrixNormal.Basic

import TauCeti.Probability.Distributions.Gaussian.Affine

/-!
# Row-major coordinates for matrix normal laws

The matrix normal law is defined through column-stacking vectorization. This file gives its
equivalent row-indexed presentation: a Gaussian vector indexed by row-column pairs is read as a
matrix without a Jacobian factor. In these coordinates the covariance between `(i, j)` and
`(k, l)` is `U i k * V j l`, matching the row and column covariance parameters directly.

## References

* A. K. Gupta and D. K. Nagar, *Matrix Variate Distributions*, Chapman & Hall/CRC, 2000,
  chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Kronecker

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A matrix normal law is the image of a row-indexed multivariate Gaussian. Its covariance at
row-column pairs `(i, j)` and `(k, l)` is `U i k * V j l`. -/
theorem matrixNormalMeasure_eq_map_rowMajor (M : Matrix ι κ ℝ)
    {U : Matrix ι ι ℝ} {V : Matrix κ κ ℝ}
    (hU : U.PosSemidef) (hV : V.PosSemidef) :
    matrixNormalMeasure M U V =
      (multivariateGaussian (WithLp.toLp 2 fun ij : ι × κ => M ij.1 ij.2)
        (Matrix.of fun (ij kl : ι × κ) => U ij.1 kl.1 * V ij.2 kl.2)).map
          (TauCeti.matrixRowMeasurableEquiv 2) := by
  have hcov :
      Matrix.of (fun (ij kl : ι × κ) => U ij.1 kl.1 * V ij.2 kl.2) =
        (V ⊗ₖ U).submatrix Prod.swap Prod.swap := by
    ext ij kl
    simp [mul_comm]
  have h := map_comp_multivariateGaussian (WithLp.toLp 2 M.vec) (hV.kronecker hU) Prod.swap
  rw [← map_vec_matrixNormalMeasure M hU hV, Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hrow :
      (matrixNormalMeasure M U V).map (TauCeti.matrixRowMeasurableEquiv 2).symm =
        multivariateGaussian (WithLp.toLp 2 fun ij : ι × κ => M ij.1 ij.2)
          (Matrix.of fun (ij kl : ι × κ) => U ij.1 kl.1 * V ij.2 kl.2) := by
    rw [hcov]
    rw [show ⇑(TauCeti.matrixRowMeasurableEquiv 2).symm =
      (fun X : Matrix ι κ ℝ => WithLp.toLp 2 fun ij => X ij.1 ij.2) from
        funext fun X => TauCeti.matrixRowMeasurableEquiv_symm_apply 2 X]
    simpa [Function.comp_def] using h
  rw [← hrow]
  exact (MeasurableEquiv.map_map_symm
    (TauCeti.matrixRowMeasurableEquiv (m := ι) (n := κ) (α := ℝ) 2)).symm

end TauCeti.Probability
