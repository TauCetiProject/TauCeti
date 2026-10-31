/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Transforms
public import TauCeti.Probability.Distributions.Gaussian.Quantile

/-!
# Quantiles of proper complex Gaussian real projections

The real observable `Re (qᴴ z)` has mean `Re (qᴴ m)` and variance `Re (qᴴ C q) / 2`.
Its interior quantiles are the corresponding affine images of standard Gaussian quantiles.
The one-sided endpoint limits distinguish zero directional variance, with constant
quantiles, from positive directional variance, with infinite endpoints.

These results use the scalar projection law from `ProperComplex.Transforms` and the
real Gaussian quantile API, without requiring a nonsingular complex covariance.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped Matrix ComplexOrder

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An interior quantile of a proper complex Gaussian real projection is its mean plus
its standard deviation times the standard Gaussian quantile, including zero variance. -/
theorem quantile_map_re_dotProduct_properComplexGaussianMeasure (m q : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((properComplexGaussianMeasure m C).map (fun z ↦ (star q ⬝ᵥ z).re)).quantile u =
      (star q ⬝ᵥ m).re + √((star q ⬝ᵥ C *ᵥ q).re / 2) *
        (gaussianReal 0 1).quantile u := by
  rw [map_re_dotProduct_properComplexGaussianMeasure m q hC,
    quantile_gaussianReal_eq_add_mul _ _ hu]
  simp only [← RCLike.re_to_complex, hC.coe_toNNReal_re_dotProduct_div_two q]

/-- As the level tends to zero from above, the quantile function of a real projection
tends to `Re (qᴴ m)` when `Re (qᴴ C q) = 0`, and to minus infinity otherwise. -/
theorem tendsto_quantile_map_re_dotProduct_properComplexGaussianMeasure_nhdsGT_zero
    (m q : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    Tendsto (fun u ↦
        (((properComplexGaussianMeasure m C).map (fun z ↦ (star q ⬝ᵥ z).re)).quantile u : EReal))
      (𝓝[>] 0)
      (𝓝 (if (star q ⬝ᵥ C *ᵥ q).re = 0 then ((star q ⬝ᵥ m).re : EReal) else ⊥)) := by
  rw [map_re_dotProduct_properComplexGaussianMeasure m q hC]
  simpa only [← RCLike.re_to_complex, hC.toNNReal_re_dotProduct_div_two_eq_zero_iff q] using
    tendsto_quantile_gaussianReal_nhdsGT_zero
      (star q ⬝ᵥ m).re ((star q ⬝ᵥ C *ᵥ q).re / 2).toNNReal

/-- As the level tends to one from below, the quantile function of a real projection
tends to `Re (qᴴ m)` when `Re (qᴴ C q) = 0`, and to plus infinity otherwise. -/
theorem tendsto_quantile_map_re_dotProduct_properComplexGaussianMeasure_nhdsLT_one
    (m q : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    Tendsto (fun u ↦
        (((properComplexGaussianMeasure m C).map (fun z ↦ (star q ⬝ᵥ z).re)).quantile u : EReal))
      (𝓝[<] 1)
      (𝓝 (if (star q ⬝ᵥ C *ᵥ q).re = 0 then ((star q ⬝ᵥ m).re : EReal) else ⊤)) := by
  rw [map_re_dotProduct_properComplexGaussianMeasure m q hC]
  simpa only [← RCLike.re_to_complex, hC.toNNReal_re_dotProduct_div_two_eq_zero_iff q] using
    tendsto_quantile_gaussianReal_nhdsLT_one
      (star q ⬝ᵥ m).re ((star q ⬝ᵥ C *ᵥ q).re / 2).toNNReal

end TauCeti.Probability
