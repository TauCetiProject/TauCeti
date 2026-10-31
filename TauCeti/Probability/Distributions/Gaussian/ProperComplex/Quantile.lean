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
  have hnonneg : 0 ≤ (star q ⬝ᵥ C *ᵥ q).re / 2 :=
    div_nonneg (hC.re_dotProduct_nonneg q) (by norm_num)
  rw [map_re_dotProduct_properComplexGaussianMeasure m q hC,
    quantile_gaussianReal_eq_add_mul _ _ hu, Real.coe_toNNReal _ hnonneg]

/-- At level zero, a real projection tends to its constant value in a zero-variance
direction and to minus infinity otherwise. -/
theorem tendsto_quantile_map_re_dotProduct_properComplexGaussianMeasure_nhdsGT_zero
    (m q : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    Tendsto (fun u ↦
        (((properComplexGaussianMeasure m C).map (fun z ↦ (star q ⬝ᵥ z).re)).quantile u : EReal))
      (𝓝[>] 0)
      (𝓝 (if (star q ⬝ᵥ C *ᵥ q).re = 0 then ((star q ⬝ᵥ m).re : EReal) else ⊥)) := by
  have hnonneg : 0 ≤ (star q ⬝ᵥ C *ᵥ q).re := hC.re_dotProduct_nonneg q
  have hzero : ((star q ⬝ᵥ C *ᵥ q).re / 2).toNNReal = 0 ↔
      (star q ⬝ᵥ C *ᵥ q).re = 0 := by
    rw [Real.toNNReal_eq_zero, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    simp only [zero_mul]
    exact ⟨fun h ↦ le_antisymm h hnonneg, fun h ↦ h.le⟩
  rw [map_re_dotProduct_properComplexGaussianMeasure m q hC]
  simpa only [hzero] using tendsto_quantile_gaussianReal_nhdsGT_zero
    (star q ⬝ᵥ m).re ((star q ⬝ᵥ C *ᵥ q).re / 2).toNNReal

/-- At level one, a real projection tends to its constant value in a zero-variance
direction and to plus infinity otherwise. -/
theorem tendsto_quantile_map_re_dotProduct_properComplexGaussianMeasure_nhdsLT_one
    (m q : ι → ℂ) {C : Matrix ι ι ℂ} (hC : C.PosSemidef) :
    Tendsto (fun u ↦
        (((properComplexGaussianMeasure m C).map (fun z ↦ (star q ⬝ᵥ z).re)).quantile u : EReal))
      (𝓝[<] 1)
      (𝓝 (if (star q ⬝ᵥ C *ᵥ q).re = 0 then ((star q ⬝ᵥ m).re : EReal) else ⊤)) := by
  have hnonneg : 0 ≤ (star q ⬝ᵥ C *ᵥ q).re := hC.re_dotProduct_nonneg q
  have hzero : ((star q ⬝ᵥ C *ᵥ q).re / 2).toNNReal = 0 ↔
      (star q ⬝ᵥ C *ᵥ q).re = 0 := by
    rw [Real.toNNReal_eq_zero, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    simp only [zero_mul]
    exact ⟨fun h ↦ le_antisymm h hnonneg, fun h ↦ h.le⟩
  rw [map_re_dotProduct_properComplexGaussianMeasure m q hC]
  simpa only [hzero] using tendsto_quantile_gaussianReal_nhdsLT_one
    (star q ⬝ᵥ m).re ((star q ⬝ᵥ C *ᵥ q).re / 2).toNNReal

end TauCeti.Probability
