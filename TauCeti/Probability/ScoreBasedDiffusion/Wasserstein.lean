/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Basic
public import TauCeti.Probability.Distributions.Gaussian.Conditional.BayesUpdate
import TauCeti.MeasureTheory.OptimalTransport.Disintegration

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

* `TauCeti.Probability.wassersteinEDist_bind_gaussianKernel_le`: the bound
  `W₂(μ₀, μ₀.bind (gaussianKernel c (s ^ 2))) ≤ √((1 - c)² M + s² d)` when `∫ ‖x‖² ∂μ₀ ≤ M`.

It is a consequence of the exact quadratic transport cost of the coupling
`μ₀ ⊗ₘ gaussianKernel c v`, `TauCeti.Probability.eLpNorm_edist_compProd_gaussianKernel_sq`, proved
next to the Gaussian observation kernel in
`TauCeti.Probability.Distributions.Gaussian.Conditional.BayesUpdate`.

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
