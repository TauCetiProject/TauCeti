/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGaussian.Basic
public import TauCeti.Probability.Quantile

/-!
# Quantiles of inverse Gaussian laws

For positive mean and shape, the inverse Gaussian quantile at a level in `(0, 1)` is the
unique positive solution of its explicit Gaussian-cdf equation. The quantile is continuous
and strictly increasing in the level, with limits zero and positive infinity at the two
endpoints. This characterizes the inverse cdf without introducing a separate inverse function.

## References

* Hyperexponential quantile API: `TauCeti.Probability.Distributions.Hyperexponential.Quantile`.
* R. S. Chhikara, J. L. Folks, *The Inverse Gaussian Distribution: Theory, Methodology, and
  Applications*, Marcel Dekker (1989).
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {μ lam u x : ℝ}

/-- Every interior inverse Gaussian quantile is strictly positive. -/
theorem quantile_inverseGaussianMeasure_pos (hμ : 0 < μ) (hlam : 0 < lam)
    (hu : u ∈ Ioo 0 1) : 0 < (inverseGaussianMeasure μ lam).quantile u := by
  let _ := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  exact ordConnected_Ioi.quantile_mem (ae_pos_inverseGaussianMeasure μ lam) hu.1 hu.2

/-- The inverse Gaussian quantile is the unique positive solution of the explicit cdf equation,
where `cdf (gaussianReal 0 1)` is the standard Gaussian cdf. -/
theorem quantile_inverseGaussianMeasure_eq_iff (hμ : 0 < μ) (hlam : 0 < lam)
    (hu : u ∈ Ioo 0 1) :
    (inverseGaussianMeasure μ lam).quantile u = x ↔
      0 < x ∧ cdf (gaussianReal 0 1) (√(lam / x) * (x / μ - 1)) +
        exp (2 * lam / μ) * cdf (gaussianReal 0 1) (-(√(lam / x) * (x / μ + 1))) = u := by
  let _ := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  have hpos := quantile_inverseGaussianMeasure_pos hμ hlam hu
  have hroot := Measure.cdf_quantile (inverseGaussianMeasure μ lam)
    (Measure.continuous_cdf_of_noAtoms _) hu.1 hu.2
  constructor
  · rintro rfl
    exact ⟨hpos, (cdf_inverseGaussianMeasure_of_pos hμ hlam hpos).symm.trans hroot⟩
  · rintro ⟨hx, hcdf⟩
    apply (strictMonoOn_cdf_inverseGaussianMeasure hμ hlam).injOn hpos.le hx.le
    rw [hroot, cdf_inverseGaussianMeasure_of_pos hμ hlam hx, hcdf]

/-- Interior inverse Gaussian quantiles increase strictly with the probability level. -/
theorem strictMonoOn_quantile_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    StrictMonoOn (inverseGaussianMeasure μ lam).quantile (Ioo 0 1) := by
  let _ := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  exact Measure.strictMonoOn_quantile _ (Measure.continuous_cdf_of_noAtoms _)

/-- The inverse Gaussian quantile is continuous on the open unit interval. -/
theorem continuousOn_quantile_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    ContinuousOn (inverseGaussianMeasure μ lam).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Ioi
    ((strictMonoOn_cdf_inverseGaussianMeasure hμ hlam).mono Ioi_subset_Ici_self)
    (fun _ hu ↦ quantile_inverseGaussianMeasure_pos hμ hlam hu)

/-- As the level decreases to zero, the inverse Gaussian quantile tends to zero. -/
theorem tendsto_quantile_inverseGaussianMeasure_nhdsGT_zero (hμ : 0 < μ) (hlam : 0 < lam) :
    Tendsto (fun u ↦ ((inverseGaussianMeasure μ lam).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  let _ := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_pos_inverseGaussianMeasure μ lam).mono fun _ hx ↦ hx.le)
    (fun _ hx ↦ (cdf_inverseGaussianMeasure_pos_iff hμ hlam).2 hx)

/-- As the level increases to one, the inverse Gaussian quantile tends to positive infinity. -/
theorem tendsto_quantile_inverseGaussianMeasure_nhdsLT_one (hμ : 0 < μ) (hlam : 0 < lam) :
    Tendsto (fun u ↦ ((inverseGaussianMeasure μ lam).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _
    (cdf_inverseGaussianMeasure_lt_one hμ hlam)

end TauCeti.Probability
