/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Probability.Distributions.Gaussian.Transforms
import TauCeti.Probability.Moments.SubGaussian

/-!
# Sub-Gaussian random vectors

A random vector `x` in a real inner product space is sub-Gaussian with variance proxy `c` when
every linear form `⟪u, x⟫` satisfies a sub-Gaussian moment-generating function bound with
variance proxy `c * ‖u‖²`. A condition on the coordinates alone is weaker: for `g` standard
Gaussian, `(g, g)` has coordinates with proxy `1`, but its form along `(1, 1) / √2` is `√2 g`,
whose variance is `2`.

## Main definitions and results

* `ProbabilityTheory.IsSubgaussianVector x c μ`: every linear form `⟪u, x⟫` has variance proxy
  `c * ‖u‖₊ ^ 2`.
* `ProbabilityTheory.iIndepFun.isSubgaussianVector`: a vector of `EuclideanSpace ℝ ι` with
  independent coordinates of proxy `c` is a sub-Gaussian vector with proxy `c`.
* `ProbabilityTheory.HasLaw.isSubgaussianVector`: a centred Gaussian vector
  with covariance matrix `S` is a sub-Gaussian vector with proxy the operator norm `‖S‖₊`.
* `ProbabilityTheory.IsSubgaussianVector.continuousLinearMap_comp`: the image under a continuous
  linear map `A` of a sub-Gaussian vector with proxy `c` has proxy `‖A‖₊ ^ 2 * c`.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §3.4.
-/

public section

open MeasureTheory Real
open scoped NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A random vector `x` in a real inner product space is sub-Gaussian with variance proxy `c`
if every linear form `⟪u, x⟫` has a sub-Gaussian moment-generating function with variance proxy
`c * ‖u‖₊ ^ 2`. -/
def IsSubgaussianVector (x : Ω → E) (c : ℝ≥0) (μ : Measure Ω) : Prop :=
  ∀ u : E, HasSubgaussianMGF (fun ω ↦ ⟪u, x ω⟫) (c * ‖u‖₊ ^ 2) μ

/-- Unfolding lemma for `IsSubgaussianVector`. -/
theorem isSubgaussianVector_def {x : Ω → E} {c : ℝ≥0} :
    IsSubgaussianVector x c μ ↔
      ∀ u : E, HasSubgaussianMGF (fun ω ↦ ⟪u, x ω⟫) (c * ‖u‖₊ ^ 2) μ := Iff.rfl

namespace IsSubgaussianVector

variable {x : Ω → E} {c : ℝ≥0}

/-- The linear form `⟪u, x⟫` of a sub-Gaussian vector with proxy `c` has proxy
`c * ‖u‖₊ ^ 2`. -/
theorem hasSubgaussianMGF_inner (h : IsSubgaussianVector x c μ) (u : E) :
    HasSubgaussianMGF (fun ω ↦ ⟪u, x ω⟫) (c * ‖u‖₊ ^ 2) μ :=
  h u

/-- Monotonicity of `IsSubgaussianVector` in the variance proxy. -/
theorem mono (h : IsSubgaussianVector x c μ) {c' : ℝ≥0} (hc : c ≤ c') :
    IsSubgaussianVector x c' μ :=
  fun u ↦ (h u).mono (mul_le_mul_left hc _)

/-- Each coordinate of a sub-Gaussian vector of `EuclideanSpace ℝ ι` with proxy `c` has proxy
`c`. -/
theorem hasSubgaussianMGF_apply {ι : Type*} [Fintype ι] {x : Ω → EuclideanSpace ℝ ι}
    (h : IsSubgaussianVector x c μ) (i : ι) : HasSubgaussianMGF (fun ω ↦ x ω i) c μ := by
  classical
  simpa [EuclideanSpace.inner_single_left] using h (EuclideanSpace.single i 1)

/-- The image of a sub-Gaussian vector with proxy `c` under a continuous linear map `A` is a
sub-Gaussian vector with proxy `‖A‖₊ ^ 2 * c`. -/
theorem continuousLinearMap_comp [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (h : IsSubgaussianVector x c μ) (A : E →L[ℝ] F) :
    IsSubgaussianVector (fun ω ↦ A (x ω)) (‖A‖₊ ^ 2 * c) μ := by
  intro v
  set w := (InnerProductSpace.toDual ℝ E).symm ((innerSL ℝ v).comp A)
  have hw : ‖w‖₊ ≤ ‖A‖₊ * ‖v‖₊ := by
    rw [LinearIsometryEquiv.nnNorm_map, mul_comm]
    refine (ContinuousLinearMap.opNNNorm_comp_le _ _).trans ?_
    gcongr
    exact (innerSL ℝ v).opNNNorm_le_bound _ fun y ↦ by
      simpa using nnNorm_inner_le_nnNorm (𝕜 := ℝ) v y
  refine ((h w).congr (ae_of_all _ fun ω ↦ ?_)).mono ?_
  · simp [w, InnerProductSpace.toDual_symm_apply]
  · calc c * ‖w‖₊ ^ 2 ≤ c * (‖A‖₊ * ‖v‖₊) ^ 2 := by gcongr
      _ = ‖A‖₊ ^ 2 * c * ‖v‖₊ ^ 2 := by ring

end IsSubgaussianVector

/-- A random vector of `EuclideanSpace ℝ ι` with independent coordinates, each with variance
proxy `c`, is a sub-Gaussian vector with proxy `c`. -/
theorem iIndepFun.isSubgaussianVector {ι : Type*} [Fintype ι] {x : Ω → EuclideanSpace ℝ ι}
    {c : ℝ≥0} (hindep : iIndepFun (fun i ω ↦ x ω i) μ)
    (hx : ∀ i, HasSubgaussianMGF (fun ω ↦ x ω i) c μ) : IsSubgaussianVector x c μ := by
  intro u
  have hproxy : ∑ i, ‖u i‖₊ ^ 2 * c = c * ‖u‖₊ ^ 2 := by
    rw [← Finset.sum_mul, mul_comm, EuclideanSpace.nnNorm_eq, NNReal.sq_sqrt]
  rw [← hproxy]
  refine (hindep.hasSubgaussianMGF_dotProduct hx u).congr (ae_of_all _ fun ω ↦ ?_)
  simp [dotProduct, PiLp.inner_apply, mul_comm]

/-- A centred Gaussian vector with covariance matrix `S` is a sub-Gaussian vector whose variance
proxy is the Euclidean operator norm `‖S‖₊`. If `S` is not positive semidefinite, Mathlib's
`multivariateGaussian 0 S` is the Dirac mass at `0` and the statement holds trivially. -/
theorem HasLaw.isSubgaussianVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x : Ω → EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hx : HasLaw x (multivariateGaussian 0 S) μ) : IsSubgaussianVector x ‖S‖₊ μ := by
  intro u
  by_cases hS : S.PosSemidef
  · set q := ⟪u, S.toEuclideanLin u⟫
    have hlaw : HasLaw (fun y : EuclideanSpace ℝ ι ↦ ⟪u, y⟫) (gaussianReal 0 q.toNNReal)
        (multivariateGaussian 0 S) :=
      ⟨by fun_prop, by simpa using TauCeti.Probability.map_inner_multivariateGaussian 0 u hS⟩
    refine (hlaw.comp hx).hasSubgaussianMGF.mono ?_
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_mul, NNReal.coe_pow, coe_nnNorm, coe_nnNorm]
    calc q ≤ ‖u‖ * ‖S.toEuclideanLin u‖ := real_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖S‖ * ‖u‖) := by
        gcongr
        exact S.l2_opNorm_mulVec u
      _ = ‖S‖ * ‖u‖ ^ 2 := by ring
  · rw [multivariateGaussian_of_not_posSemidef 0 hS] at hx
    have := hx.isProbabilityMeasure
    refine (HasSubgaussianMGF.zero.congr ?_).mono (by positivity)
    filter_upwards [hx.ae_eq_of_dirac] with ω hω
    simp [hω]

end ProbabilityTheory
