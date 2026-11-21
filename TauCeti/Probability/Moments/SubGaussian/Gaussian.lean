/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Moments.SubGaussian.Vector
import TauCeti.Probability.Distributions.Gaussian.Transforms

/-!
# Centred Gaussian vectors are sub-Gaussian vectors

A real random variable with law `gaussianReal 0 v` is sub-Gaussian with variance proxy `v`. A
random vector with law `multivariateGaussian 0 S` is a sub-Gaussian vector
(`TauCeti.IsSubgaussianVector`) whose variance proxy is the Euclidean operator norm `‖S‖₊` of the
matrix parameter `S`. When `S` is positive semidefinite it is the covariance matrix; otherwise
Mathlib's `multivariateGaussian 0 S` is the Dirac mass at `0`.

## Main results

* `ProbabilityTheory.HasLaw.hasSubgaussianMGF`
* `ProbabilityTheory.HasLaw.isSubgaussianVector`

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §3.4.
-/

public section

open MeasureTheory TauCeti
open scoped NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace ProbabilityTheory

/-- A random variable with centred Gaussian law `gaussianReal 0 v` is `v`-sub-Gaussian. -/
theorem HasLaw.hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ := by
  rw [← HasSubgaussianMGF.id_map_iff hX.aemeasurable, hX.map_eq]
  exact ⟨integrable_exp_mul_gaussianReal, fun t ↦ by simp [mgf_id_gaussianReal]⟩

/-- A random vector with law `multivariateGaussian 0 S` is a sub-Gaussian vector whose variance
proxy is the Euclidean operator norm `‖S‖₊` of the matrix parameter `S`. For positive
semidefinite `S`, the covariance matrix, each linear form `⟪u, x⟫` has variance
`⟪u, S u⟫ ≤ ‖S‖ ‖u‖²`; otherwise the law is the Dirac mass at `0`. -/
theorem HasLaw.isSubgaussianVector {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype ι] [DecidableEq ι] {x : Ω → EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hx : HasLaw x (multivariateGaussian 0 S) μ) : IsSubgaussianVector x ‖S‖₊ μ := by
  refine isSubgaussianVector_def.2 fun u ↦ ?_
  by_cases hS : S.PosSemidef
  · set q := ⟪u, S.toEuclideanLin u⟫
    have hlaw : HasLaw (fun y : EuclideanSpace ℝ ι ↦ ⟪u, y⟫) (gaussianReal 0 q.toNNReal)
        (multivariateGaussian 0 S) :=
      ⟨by fun_prop, by simpa using TauCeti.Probability.map_inner_multivariateGaussian 0 u hS⟩
    refine (hlaw.comp hx).hasSubgaussianMGF.mono ?_
    rw [Real.toNNReal_le_iff_le_coe]
    push_cast
    have hSu : ‖S.toEuclideanLin u‖ ≤ ‖S‖ * ‖u‖ := S.l2_opNorm_mulVec u
    calc q ≤ ‖u‖ * ‖S.toEuclideanLin u‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖S‖ * ‖u‖) := by gcongr
      _ = ‖S‖ * ‖u‖ ^ 2 := by ring
  · rw [multivariateGaussian_of_not_posSemidef 0 hS] at hx
    have := hx.isProbabilityMeasure
    refine (HasSubgaussianMGF.zero.congr ?_).mono (by positivity)
    filter_upwards [hx.ae_eq_of_dirac] with ω hω
    simp [hω]

end ProbabilityTheory
