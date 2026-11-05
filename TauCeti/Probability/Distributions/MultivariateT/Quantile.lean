/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MultivariateT.Marginal
public import TauCeti.Probability.Distributions.StudentT.Quantile

/-!
# Endpoint limits for multivariate t projection quantiles

The quantile of a real linear projection of a multivariate t law is already identified as an
affine image of the scalar Student t quantile. This file records its one-sided endpoint limits.
In a direction of zero scale both limits are the constant directional location; otherwise the
lower and upper limits are respectively minus and plus infinity.

## Main results

* `TauCeti.Probability.tendsto_quantile_multivariateTMeasure_projection_nhdsGT_zero` gives the
  lower endpoint limit.
* `TauCeti.Probability.tendsto_quantile_multivariateTMeasure_projection_nhdsLT_one` gives the
  upper endpoint limit.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- As the level tends to zero, a multivariate t projection quantile tends to its directional
location in a zero-scale direction and to minus infinity otherwise. -/
theorem tendsto_quantile_multivariateTMeasure_projection_nhdsGT_zero
    (m θ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {ν : ℝ}
    (hν : 0 < ν) :
    Tendsto (fun u ↦
        (((multivariateTMeasure m S ν).map (fun x ↦ ⟪θ, x⟫)).quantile u : EReal))
      (𝓝[>] 0)
      (𝓝 (if ⟪θ, S.toEuclideanLin θ⟫ = 0 then (⟪θ, m⟫ : EReal) else ⊥)) := by
  have hnonneg := (Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right θ
  by_cases hzero : ⟪θ, S.toEuclideanLin θ⟫ = 0
  · rw [ite_eq_left hzero]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    rw [quantile_multivariateTMeasure_projection m θ hS hν hu, hzero, Real.sqrt_zero,
      zero_mul, add_zero]
  · rw [ite_eq_right hzero, EReal.tendsto_coe_nhds_bot_iff]
    have hscale : 0 < √⟪θ, S.toEuclideanLin θ⟫ :=
      Real.sqrt_pos.2 (lt_of_le_of_ne hnonneg (Ne.symm hzero))
    have hstudent := EReal.tendsto_coe_nhds_bot_iff.mp
      (tendsto_quantile_studentTMeasure_nhdsGT_zero hν)
    have haffine := tendsto_atBot_add_const_left _ ⟪θ, m⟫
      (hstudent.const_mul_atBot hscale)
    apply haffine.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    exact (quantile_multivariateTMeasure_projection m θ hS hν hu).symm

/-- As the level tends to one, a multivariate t projection quantile tends to its directional
location in a zero-scale direction and to plus infinity otherwise. -/
theorem tendsto_quantile_multivariateTMeasure_projection_nhdsLT_one
    (m θ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {ν : ℝ}
    (hν : 0 < ν) :
    Tendsto (fun u ↦
        (((multivariateTMeasure m S ν).map (fun x ↦ ⟪θ, x⟫)).quantile u : EReal))
      (𝓝[<] 1)
      (𝓝 (if ⟪θ, S.toEuclideanLin θ⟫ = 0 then (⟪θ, m⟫ : EReal) else ⊤)) := by
  have hnonneg := (Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right θ
  by_cases hzero : ⟪θ, S.toEuclideanLin θ⟫ = 0
  · rw [ite_eq_left hzero]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [quantile_multivariateTMeasure_projection m θ hS hν hu, hzero, Real.sqrt_zero,
      zero_mul, add_zero]
  · rw [ite_eq_right hzero, EReal.tendsto_coe_nhds_top_iff]
    have hscale : 0 < √⟪θ, S.toEuclideanLin θ⟫ :=
      Real.sqrt_pos.2 (lt_of_le_of_ne hnonneg (Ne.symm hzero))
    have hstudent := EReal.tendsto_coe_nhds_top_iff.mp
      (tendsto_quantile_studentTMeasure_nhdsLT_one hν)
    have haffine := tendsto_atTop_add_const_left _ ⟪θ, m⟫
      (hstudent.const_mul_atTop hscale)
    apply haffine.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    exact (quantile_multivariateTMeasure_projection m θ hS hν hu).symm

end TauCeti.Probability
