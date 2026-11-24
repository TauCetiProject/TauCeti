/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
public import TauCeti.Probability.Distributions.Gaussian.Conditional.BayesUpdate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.MeasureTheory.OptimalTransport.Disintegration
import TauCeti.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Moments.Covariance

/-!
# The Wasserstein distance from the data to a Gaussian noising of it

Let `X` have law `μ₀` on `EuclideanSpace ℝ ι` and let `Z` be a standard Gaussian vector independent
of `X`. The noised observation `c • X + s • Z` has the law `μ₀.bind (gaussianKernel c (s ^ 2))`.
The joint law of `(X, c • X + s • Z)` is the composition-product `μ₀ ⊗ₘ gaussianKernel c (s ^ 2)`,
a coupling of `μ₀` and the noised law, and its quadratic transport cost is computed exactly:

`E ‖X - (c • X + s • Z)‖² = (1 - c)² E ‖X‖² + s² d`, with `d` the dimension,

because `Z` is centered and independent of `X` and `E ‖Z‖² = d`. Consequently the quadratic
Wasserstein distance from the data to the noised law is at most `√((1 - c)² M + s² d)` whenever
`E ‖X‖² ≤ M`. No assumption is made on the support of `μ₀`. As `c → 1` and `s → 0` the bound tends
to `0`: a Gaussian noising of the data at a small noise level is close to the data in the
Wasserstein distance of order two.

## Main results

* `TauCeti.Probability.integral_norm_sub_sq_gaussianKernel`: the mean squared displacement of the
  Gaussian observation kernel, `∫ ‖x - y‖² ∂N(c • x, v) = (1 - c)² ‖x‖² + v d`.
* `TauCeti.Probability.eLpNorm_edist_compProd_gaussianKernel_sq`: the quadratic transport cost of
  the coupling `μ₀ ⊗ₘ gaussianKernel c v`, as an extended integral, with no moment assumption.
* `TauCeti.Probability.wassersteinEDist_bind_gaussianKernel_le`: the bound
  `W₂(μ₀, μ₀.bind (gaussianKernel c (s ^ 2))) ≤ √((1 - c)² M + s² d)` when `∫ ‖x‖² ∂μ₀ ≤ M`.

## References

* S. Chen, S. Chewi, J. Li, Y. Li, A. Salim and A. R. Zhang, *Sampling is as easy as learning the
  score: theory for diffusion models with minimal data assumptions*, ICLR 2023, arXiv:2209.11215,
  Appendix B, Lemma 20, first part (the Ornstein–Uhlenbeck path, for data in a ball).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The mean squared displacement of the Gaussian observation kernel: a point `x` and its noisy
observation `y ~ N(c • x, v)` are at mean squared distance `(1 - c)² ‖x‖² + v d`, where `d` is the
dimension. -/
theorem integral_norm_sub_sq_gaussianKernel (c : ℝ) {v : ℝ} (hv : 0 ≤ v)
    (x : EuclideanSpace ℝ ι) :
    ∫ y, ‖x - y‖ ^ 2 ∂(gaussianKernel c v x) = (1 - c) ^ 2 * ‖x‖ ^ 2 + v * Fintype.card ι := by
  have hS : (v • (1 : Matrix ι ι ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hv
  have hmean : c • x - x = (c - 1) • x := by rw [sub_smul, one_smul]
  simp_rw [norm_sub_rev x]
  rw [gaussianKernel_apply, integral_norm_sub_sq_eq_norm_integral_sub_sq_add_trace_covMatrix _
      IsGaussian.memLp_two_id, integral_id_multivariateGaussian,
    covMatrix_multivariateGaussian _ hS, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, hmean,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← neg_sub, neg_sq]

/-- **The quadratic cost of the noising coupling.** For a probability measure `μ₀`, the joint law
`μ₀ ⊗ₘ gaussianKernel c v` of a point and its Gaussian observation has squared `L²` transport cost
`(1 - c)² ∫ ‖x‖² ∂μ₀ + v d`, where `d` is the dimension. The second moment is an extended integral,
so no integrability is assumed and both sides may be infinite. -/
theorem eLpNorm_edist_compProd_gaussianKernel_sq (μ₀ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ₀] (c : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    eLpNorm (fun z ↦ edist z.1 z.2) 2 (μ₀ ⊗ₘ gaussianKernel c v) ^ 2 =
      ENNReal.ofReal ((1 - c) ^ 2) * ∫⁻ x, ‖x‖ₑ ^ 2 ∂μ₀ +
        ENNReal.ofReal (v * Fintype.card ι) := by
  have hinner (x : EuclideanSpace ℝ ι) :
      ∫⁻ y, ‖x - y‖ₑ ^ 2 ∂(gaussianKernel c v x) =
        ENNReal.ofReal ((1 - c) ^ 2) * ‖x‖ₑ ^ 2 + ENNReal.ofReal (v * Fintype.card ι) := by
    have hint : Integrable (fun y ↦ ‖x - y‖ ^ 2) (gaussianKernel c v x) := by
      have hX : MemLp id 2 (gaussianKernel c v x) := by
        rw [gaussianKernel_apply]
        exact IsGaussian.memLp_two_id
      exact (memLp_two_iff_integrable_sq_norm (by fun_prop)).1 ((memLp_const x).sub hX)
    simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ by positivity),
      integral_norm_sub_sq_gaussianKernel c hv x, ENNReal.ofReal_add (by positivity)
        (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [eLpNorm_two_sq_eq_lintegral (by fun_prop)]
  simp_rw [eNorm_eq_self]
  rw [Measure.lintegral_compProd (by fun_prop)]
  simp_rw [eDist_eq_eNorm_sub, hinner]
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const, measure_univ, mul_one]

/-- **The distance from the data.** Let `μ₀` be a probability measure on `EuclideanSpace ℝ ι`
with finite second moment `∫ ‖x‖² ∂μ₀ ≤ M`. For every signal level `c` and noise level `s`, the
quadratic Wasserstein distance from `μ₀` to its Gaussian noising
`μ₀.bind (gaussianKernel c (s ^ 2))`, the law of `c • X + s • Z`, is at most
`√((1 - c)² M + s² d)`, where `d` is the dimension. -/
theorem wassersteinEDist_bind_gaussianKernel_le (μ₀ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ₀] (hμ₀ : Integrable (fun x ↦ ‖x‖ ^ 2) μ₀) {M : ℝ}
    (hM : ∫ x, ‖x‖ ^ 2 ∂μ₀ ≤ M) (c s : ℝ) :
    wassersteinEDist 2 μ₀ (μ₀.bind (gaussianKernel c (s ^ 2))) ≤
      ENNReal.ofReal √((1 - c) ^ 2 * M + s ^ 2 * Fintype.card ι) := by
  have hM₀ : 0 ≤ M := (integral_nonneg fun x ↦ by positivity).trans hM
  refine (wassersteinEDist_le (isCoupling_compProd μ₀ (gaussianKernel c (s ^ 2))) 2).trans ?_
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero,
    eLpNorm_edist_compProd_gaussianKernel_sq μ₀ c (sq_nonneg s),
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (sq_nonneg (1 - c))]
  gcongr
  simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hμ₀ (.of_forall fun _ ↦ by positivity)]
  exact ENNReal.ofReal_le_ofReal hM

end TauCeti.Probability
