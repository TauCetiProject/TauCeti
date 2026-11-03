/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NoncentralT.PDF
public import TauCeti.Probability.Quantile
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Probability.Cdf.Density
import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Probability.Distributions.Mixture

/-!
# Cdfs and quantiles of noncentral t laws

For positive degrees `ν`, the cdf of the noncentral t law at `x` is the integral of
`Φ(x √(v / ν) - δ)` against the chi-squared law with `ν` degrees of freedom, where `Φ` is the
standard Gaussian cdf. Since the density is positive everywhere, the cdf is continuous and
strictly increasing on the whole line. Every interior quantile is therefore the unique real root
of this mixture cdf, and the quantile is continuous and strictly increasing on `(0, 1)`, with
limits minus and plus infinity at the endpoints.

## Main results

* `TauCeti.Probability.cdf_noncentralTMeasure_eq` — the cdf as a chi-squared mixture of standard
  Gaussian cdfs.
* `TauCeti.Probability.strictMono_cdf_noncentralTMeasure` and
  `TauCeti.Probability.continuous_cdf_noncentralTMeasure` — the cdf is a continuous strictly
  increasing function.
* `TauCeti.Probability.quantile_noncentralTMeasure_eq_iff` — the quantile is the unique root of
  the mixture cdf.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 31.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {ν δ u x : ℝ}

/-- For positive degrees, the cdf of the noncentral t law at `x` is the integral of
`Φ(x √(v / ν) - δ)` against the chi-squared law with `ν` degrees of freedom, where `Φ` is the
standard Gaussian cdf. -/
theorem cdf_noncentralTMeasure_eq (hν : 0 < ν) (δ x : ℝ) :
    cdf (noncentralTMeasure ν δ) x =
      ∫ v, cdf (gaussianReal 0 1) (x * √(v / ν) - δ) ∂chiSquaredMeasure ν := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  have hK : Measurable fun v ↦ (gaussianReal δ 1).map (· / √(v / ν)) :=
    TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry
      (f := fun v x ↦ x / √(v / ν)) (by fun_prop)
  rw [noncentralTMeasure_eq_bind hν, Measure.cdf_bind _ _ hK.aemeasurable
    (ae_of_all _ fun _ ↦ inferInstance) x]
  refine integral_congr_ae ?_
  filter_upwards [ae_pos_sqrt_div_chiSquaredMeasure hν] with v hv
  have hpre : (· / √(v / ν)) ⁻¹' Iic x = Iic (x * √(v / ν)) := by
    ext y
    simp [div_le_iff₀ hv]
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hpre, ← cdf_eq_real,
    cdf_gaussianReal_eq _ one_ne_zero, cdf_gaussianReal_eq _ one_ne_zero, sub_zero]

/-- For positive degrees, the cdf of the noncentral t law is strictly increasing. -/
theorem strictMono_cdf_noncentralTMeasure (hν : 0 < ν) (δ : ℝ) :
    StrictMono (cdf (noncentralTMeasure ν δ)) := by
  let _ := isProbabilityMeasure_noncentralTMeasure hν δ
  exact strictMono_cdf_of_eq_withDensity
    (by rw [noncentralTMeasure_eq_withDensity, funext (noncentralTPDF_eq_ofReal ν δ)])
    (measurable_noncentralTPDFReal ν δ).aemeasurable (noncentralTPDFReal_pos hν δ)

/-- For positive degrees, the cdf of the noncentral t law is continuous. -/
theorem continuous_cdf_noncentralTMeasure (hν : 0 < ν) (δ : ℝ) :
    Continuous (cdf (noncentralTMeasure ν δ)) := by
  let _ := isProbabilityMeasure_noncentralTMeasure hν δ
  exact Measure.continuous_cdf_of_noAtoms _

/-- For positive degrees, the noncentral t law has full topological support. -/
@[simp]
theorem support_noncentralTMeasure (hν : 0 < ν) (δ : ℝ) :
    (noncentralTMeasure ν δ).support = univ := by
  let _ := isProbabilityMeasure_noncentralTMeasure hν δ
  exact Measure.support_eq_univ_of_strictMono_cdf _ (strictMono_cdf_noncentralTMeasure hν δ)

/-- For positive degrees, every interior quantile of the noncentral t law is the unique real root
of the chi-squared mixture of standard Gaussian cdfs. -/
theorem quantile_noncentralTMeasure_eq_iff (hν : 0 < ν) (δ : ℝ) (hu : u ∈ Ioo 0 1) :
    (noncentralTMeasure ν δ).quantile u = x ↔
      ∫ v, cdf (gaussianReal 0 1) (x * √(v / ν) - δ) ∂chiSquaredMeasure ν = u := by
  rw [← cdf_noncentralTMeasure_eq hν]
  constructor
  · rintro rfl
    exact Measure.cdf_quantile _ (continuous_cdf_noncentralTMeasure hν δ) hu.1 hu.2
  · intro h
    rw [← h]
    exact Measure.quantile_cdf _ ((strictMono_cdf_noncentralTMeasure hν δ).strictMonoOn _)
      (by rw [h]; exact hu)

/-- For positive degrees, the noncentral t quantile is strictly increasing on `(0, 1)`. -/
theorem strictMonoOn_quantile_noncentralTMeasure (hν : 0 < ν) (δ : ℝ) :
    StrictMonoOn (noncentralTMeasure ν δ).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_noncentralTMeasure hν δ)

/-- For positive degrees, the noncentral t quantile is continuous on `(0, 1)`. -/
theorem continuousOn_quantile_noncentralTMeasure (hν : 0 < ν) (δ : ℝ) :
    ContinuousOn (noncentralTMeasure ν δ).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile _ (continuous_cdf_noncentralTMeasure hν δ)
    ((strictMono_cdf_noncentralTMeasure hν δ).strictMonoOn _)

/-- Noncentral t quantiles tend to minus infinity as the probability level tends to zero from
above. -/
theorem tendsto_quantile_noncentralTMeasure_nhdsGT_zero (hν : 0 < ν) (δ : ℝ) :
    Tendsto (fun u ↦ ((noncentralTMeasure ν δ).quantile u : EReal)) (𝓝[>] 0) (𝓝 ⊥) :=
  Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos _ fun x ↦
    (cdf_nonneg _ (x - 1)).trans_lt (strictMono_cdf_noncentralTMeasure hν δ (by linarith))

/-- Noncentral t quantiles tend to plus infinity as the probability level tends to one from
below. -/
theorem tendsto_quantile_noncentralTMeasure_nhdsLT_one (hν : 0 < ν) (δ : ℝ) :
    Tendsto (fun u ↦ ((noncentralTMeasure ν δ).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _ fun x ↦
    (strictMono_cdf_noncentralTMeasure hν δ (by linarith : x < x + 1)).trans_le
      (cdf_le_one _ (x + 1))

end TauCeti.Probability
