/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# The isotropic Gaussian density is the heat kernel

For `v > 0` the isotropic Gaussian law `N(m, v • 1)` on `EuclideanSpace ℝ ι` has density
`(2πv)^(-d/2) exp(-‖y - m‖² / (2v))`, which is the heat kernel at time `v / 2` evaluated at
`y - m`. This identification transfers the analytic results proved for the heat kernel
(smoothness, Gaussian bounds on all derivatives, the semigroup law) to Gaussian densities.

## Main results

* `TauCeti.Probability.multivariateGaussianPDFReal_smul_one`: the density of `N(m, v • 1)` at `y`
  is `heatKernel (v / 2) (y - m)`.
* `TauCeti.Probability.multivariateGaussian_smul_one_eq_withDensity_heatKernel`: `N(m, v • 1)` is
  Lebesgue measure weighted by this translated heat kernel.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For `v > 0`, the density of the isotropic Gaussian law `N(m, v • 1)` at `y` is the heat kernel
at time `v / 2` evaluated at `y - m`; both equal `(2πv)^(-d/2) exp(-‖y - m‖² / (2v))`. -/
theorem multivariateGaussianPDFReal_smul_one {v : ℝ} (hv : 0 < v) (m y : EuclideanSpace ℝ ι) :
    multivariateGaussianPDFReal m (v • 1) y = heatKernel (v / 2) (y - m) := by
  have hinv : (v • (1 : Matrix ι ι ℝ))⁻¹ = v⁻¹ • 1 := by
    exact Matrix.inv_eq_left_inv (by simp [smul_smul, hv.ne'])
  have hdet : (v • (1 : Matrix ι ι ℝ)).det ^ (-(1 : ℝ) / 2) =
      v ^ (-(Fintype.card ι : ℝ) / 2) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, ← Real.rpow_natCast,
      ← Real.rpow_mul hv.le]
    congr 1
    ring
  have hquad : ⟪y - m, (v⁻¹ • (1 : Matrix ι ι ℝ)).toEuclideanLin (y - m)⟫ = ‖y - m‖ ^ 2 / v := by
    simp [inner_smul_right, div_eq_inv_mul]
  rw [multivariateGaussianPDFReal_def, heatKernel_apply, finrank_euclideanSpace, hinv, hdet]
  dsimp only
  rw [hquad, show 4 * π * (v / 2) = 2 * π * v by ring, Real.mul_rpow (by positivity) hv.le]
  congr 2
  field_simp
  ring

/-- For `v > 0`, the isotropic Gaussian law `N(m, v • 1)` is Lebesgue measure weighted by the
heat kernel at time `v / 2`, translated to `m`. -/
theorem multivariateGaussian_smul_one_eq_withDensity_heatKernel {v : ℝ} (hv : 0 < v)
    (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m (v • 1) =
      volume.withDensity fun y ↦ ENNReal.ofReal (heatKernel (v / 2) (y - m)) := by
  rw [multivariateGaussian_eq_withDensity (Matrix.PosDef.one.smul hv)]
  congr 1
  funext y
  rw [multivariateGaussianPDF_def, ← multivariateGaussianPDFReal_smul_one hv]

/-- For `v > 0`, the density `φ` of the isotropic Gaussian law `N(m, v • 1)` has gradient
`-v⁻¹ φ(y) (y - m)` at `y`; equivalently, the score `∇ log φ` of `N(m, v • 1)` is
`-(y - m) / v`. -/
theorem hasGradientAt_multivariateGaussianPDFReal_smul_one {v : ℝ} (hv : 0 < v)
    (m y : EuclideanSpace ℝ ι) :
    HasGradientAt (multivariateGaussianPDFReal m (v • 1))
      (-v⁻¹ • multivariateGaussianPDFReal m (v • 1) y • (y - m)) y := by
  set A : ℝ := (4 * π * (v / 2)) ^ (-(Fintype.card ι : ℝ) / 2)
  have hfun : multivariateGaussianPDFReal m (v • 1) =
      fun z ↦ A * exp (‖id z - m‖ ^ 2 * -(2 * v)⁻¹) := by
    funext z
    rw [multivariateGaussianPDFReal_smul_one hv, heatKernel_apply, finrank_euclideanSpace, id]
    congr 2
    ring
  have hsq := ((hasFDerivAt_id (𝕜 := ℝ) y).sub_const m).norm_sq
  rw [hasGradientAt_iff_hasFDerivAt, hfun]
  refine (((hsq.mul_const (-(2 * v)⁻¹)).exp).const_mul A).congr_fderiv ?_
  ext w
  simp
  field_simp

end TauCeti.Probability
