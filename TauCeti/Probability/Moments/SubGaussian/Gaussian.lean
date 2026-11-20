/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Probability.Moments.SubGaussian.Vector
import TauCeti.Probability.Distributions.Gaussian.Transforms
import TauCeti.Probability.Moments.SubGaussian

/-!
# Centred Gaussian vectors are sub-Gaussian vectors

A random vector with law `multivariateGaussian 0 S` is a sub-Gaussian vector
(`TauCeti.IsSubgaussianVector`) whose variance proxy is the Euclidean operator norm `‖S‖₊` of the
covariance matrix.

## Main result

* `ProbabilityTheory.HasLaw.isSubgaussianVector`

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §3.4.
-/

public section

open MeasureTheory TauCeti
open scoped NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace ProbabilityTheory

/-- A centred Gaussian vector with covariance matrix `S` is a sub-Gaussian vector whose variance
proxy is the Euclidean operator norm `‖S‖₊`. Each linear form `⟪u, x⟫` has the law
`gaussianReal 0 ⟪u, S u⟫` by `TauCeti.Probability.map_inner_multivariateGaussian`, hence proxy
`⟪u, S u⟫ ≤ ‖S‖ ‖u‖²` by `ProbabilityTheory.HasLaw.hasSubgaussianMGF`. If `S` is not positive
semidefinite, Mathlib's `multivariateGaussian 0 S` is the Dirac mass at `0` and the statement
holds trivially. -/
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
    have hSu : ‖S.toEuclideanLin u‖ ≤ ‖S‖ * ‖u‖ := by
      rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe,
        ← Matrix.l2_opNorm_toEuclideanCLM]
      exact ContinuousLinearMap.le_opNorm _ _
    calc q ≤ ‖u‖ * ‖S.toEuclideanLin u‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖S‖ * ‖u‖) := by gcongr
      _ = ‖S‖ * ‖u‖ ^ 2 := by ring
  · rw [multivariateGaussian_of_not_posSemidef 0 hS] at hx
    have := hx.isProbabilityMeasure
    refine (HasSubgaussianMGF.zero.congr ?_).mono (by positivity)
    filter_upwards [hx.ae_eq_of_dirac] with ω hω
    simp [hω]

end ProbabilityTheory
