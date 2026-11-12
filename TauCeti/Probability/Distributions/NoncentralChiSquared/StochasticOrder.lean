/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Convolution
public import TauCeti.Probability.StochasticOrder

/-!
# Stochastic comparison of noncentral chi-squared laws

Increasing either the nonnegative degree or the noncentrality makes a noncentral chi-squared
variable stochastically larger. An independent noncentral chi-squared increment with the
parameter differences realizes both increases simultaneously. This construction retains equal
parameters, degree-zero mixed laws, and the double-zero Dirac boundary.

The reversed cdf inequality gives ordered interior quantiles and an almost surely ordered
common-uniform quantile coupling. The coupling's marginal laws are supplied by
`MeasureTheory.Measure.isCoupling_quantileCoupling`.

## References

* M. Shaked and J. G. Shanthikumar, *Stochastic Orders*, Springer, 2007, chapter 1.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal MeasureTheory

namespace TauCeti.Probability

variable {k₁ k₂ u : ℝ} {l₁ l₂ : ℝ≥0}

/-- Increasing degree and noncentrality decreases the cdf. Either parameter may remain fixed,
and the smaller degree may be zero. -/
theorem cdf_noncentralChiSquaredMeasure_le (hk₁ : 0 ≤ k₁) (hk : k₁ ≤ k₂) (hl : l₁ ≤ l₂)
    (x : ℝ) :
    cdf (noncentralChiSquaredMeasure k₂ l₂) x ≤
      cdf (noncentralChiSquaredMeasure k₁ l₁) x := by
  let μ := noncentralChiSquaredMeasure k₁ l₁
  let ν := noncentralChiSquaredMeasure (k₂ - k₁) (l₂ - l₁)
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hk₁ l₁
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure (sub_nonneg.mpr hk) (l₂ - l₁)
  have hfst : HasLaw Prod.fst μ (μ.prod ν) := measurePreserving_fst.hasLaw
  have hsum : HasLaw (fun z : ℝ × ℝ ↦ z.1 + z.2)
      (noncentralChiSquaredMeasure k₂ l₂) (μ.prod ν) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← Measure.conv, noncentralChiSquaredMeasure_conv_noncentralChiSquaredMeasure
      hk₁ (sub_nonneg.mpr hk), add_sub_cancel, add_tsub_cancel_of_le hl]
  refine hfst.cdf_le_of_ae_le hsum ?_ x
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_nonneg_noncentralChiSquaredMeasure (k₂ - k₁) (l₂ - l₁))] with z hz
  exact le_add_of_nonneg_right hz

/-- Interior quantiles increase with the degree and noncentrality, including at their zero
boundaries. -/
theorem quantile_noncentralChiSquaredMeasure_le (hk₁ : 0 ≤ k₁) (hk : k₁ ≤ k₂)
    (hl : l₁ ≤ l₂) (hu : u ∈ Set.Ioo 0 1) :
    (noncentralChiSquaredMeasure k₁ l₁).quantile u ≤
      (noncentralChiSquaredMeasure k₂ l₂).quantile u := by
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hk₁ l₁
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure (hk₁.trans hk) l₂
  exact (Measure.cdf_le_iff_quantile_le _ _).1
    (cdf_noncentralChiSquaredMeasure_le hk₁ hk hl) u hu.1 hu.2

/-- The common-uniform quantile coupling is almost surely ordered when degree and noncentrality
increase. Its marginals are the two indicated noncentral chi-squared laws. -/
theorem ae_fst_le_snd_quantileCoupling_noncentralChiSquaredMeasure
    (hk₁ : 0 ≤ k₁) (hk : k₁ ≤ k₂) (hl : l₁ ≤ l₂) :
    ∀ᵐ z ∂(noncentralChiSquaredMeasure k₁ l₁).quantileCoupling
      (noncentralChiSquaredMeasure k₂ l₂), z.1 ≤ z.2 := by
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hk₁ l₁
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure (hk₁.trans hk) l₂
  exact Measure.ae_fst_le_snd_quantileCoupling _ _
    (cdf_noncentralChiSquaredMeasure_le hk₁ hk hl)

end TauCeti.Probability
