/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Nakagami.Basic
public import TauCeti.Probability.Distributions.Gamma.Quantile
import TauCeti.Probability.Quantile.Map

/-!
# Nakagami quantiles

Interior Nakagami quantiles are square roots of Gamma quantiles, expressed using the
inverse regularized Gamma function. Their one-sided endpoint limits are zero and
positive infinity, matching the support of the law.

## References

* M. Nakagami, *The m-distribution — A general formula of intensity distribution of
  rapid fading*, Statistical Methods in Radio Wave Propagation, Pergamon, 1960, pp. 3–36.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {m Ω u : ℝ}

/-- The interior Nakagami quantile in terms of the inverse regularized Gamma function. -/
@[simp]
theorem quantile_nakagamiMeasure (hm : 0 < m) (hΩ : 0 < Ω) (hu : u ∈ Ioo 0 1) :
    (nakagamiMeasure m Ω).quantile u = √(Ω / m * inverseRegularizedGamma m u) := by
  let _ := isProbabilityMeasure_gammaMeasure hm (div_pos hm hΩ)
  rw [nakagamiMeasure_of_pos hm hΩ,
    Measure.quantile_map_of_monotone (fun _ _ h ↦ sqrt_le_sqrt h) (by fun_prop) hu.1 hu.2,
    quantile_gammaMeasure hm (div_pos hm hΩ) hu]
  congr 1
  field_simp

/-- Nakagami quantiles tend to zero as the level decreases to zero. -/
theorem tendsto_quantile_nakagamiMeasure_nhdsGT_zero (hm : 0 < m) (hΩ : 0 < Ω) :
    Tendsto (fun u ↦ ((nakagamiMeasure m Ω).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hlim := (((tendsto_inverseRegularizedGamma_nhdsGT_zero hm).mono_right
      inf_le_left).const_mul (Ω / m)).sqrt
  simp only [mul_zero, sqrt_zero] at hlim
  apply (EReal.tendsto_coe.2 hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_nakagamiMeasure hm hΩ hu).symm

/-- Nakagami quantiles tend to positive infinity as the level increases to one. -/
theorem tendsto_quantile_nakagamiMeasure_nhdsLT_one (hm : 0 < m) (hΩ : 0 < Ω) :
    Tendsto (fun u ↦ ((nakagamiMeasure m Ω).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  rw [EReal.tendsto_coe_nhds_top_iff]
  have hlim := tendsto_sqrt_atTop.comp
    ((tendsto_inverseRegularizedGamma_nhdsLT_one hm).const_mul_atTop (div_pos hΩ hm))
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_nakagamiMeasure hm hΩ hu).symm

end TauCeti.Probability
