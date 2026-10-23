/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedNormal.Cdf
public import TauCeti.Probability.Distributions.Gamma.Quantile

/-!
# Generalized normal quantiles

For positive scale and shape, the generalized normal quantile is a signed power
of the inverse regularized Gamma function, centered at the location `m`. The
median is handled separately because the inverse Gamma formula uses an interior
probability level. Quantiles are continuous on `(0, 1)`, with limits minus infinity
and plus infinity at its endpoints.

## References

* S. Nadarajah, *A generalized normal distribution*, Journal of Applied Statistics
  32(7), 685–694 (2005).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {m s p u x : ℝ}

/-- Every interior probability level has a unique generalized normal cdf root. -/
theorem quantile_generalizedNormalMeasure_eq_iff (hs : 0 < s) (hp : 0 < p)
    (hu : u ∈ Ioo 0 1) :
    (generalizedNormalMeasure m s p).quantile u = x ↔
      (1 + sign (x - m) * regularizedGamma p⁻¹ (|(x - m) / s| ^ p)) / 2 = u := by
  rw [← cdf_generalizedNormalMeasure_eq hs hp]
  constructor
  · rintro rfl
    exact Measure.cdf_quantile _ (continuous_cdf_generalizedNormalMeasure hs hp) hu.1 hu.2
  · intro h
    rw [← h]
    exact Measure.quantile_cdf _ ((strictMono_cdf_generalizedNormalMeasure hs hp).strictMonoOn _)
      (by rw [h]; exact hu)

/-- The median quantile of a valid generalized normal law is its location. -/
@[simp]
theorem quantile_generalizedNormalMeasure_half (hs : 0 < s) (hp : 0 < p) :
    (generalizedNormalMeasure m s p).quantile (2⁻¹) = m := by
  apply (quantile_generalizedNormalMeasure_eq_iff hs hp (by norm_num)).mpr
  simp

private theorem cdf_generalizedNormalMeasure_signed_inverse (hs : 0 < s) (hp : 0 < p)
    (hu : u ∈ Ioo 0 1) (hne : u ≠ 1 / 2) :
    cdf (generalizedNormalMeasure m s p)
        (m + s * sign (2 * u - 1) * inverseRegularizedGamma p⁻¹ |2 * u - 1| ^ p⁻¹) = u := by
  have ht : 2 * u - 1 ≠ 0 := by intro h; apply hne; linarith
  have hv : |2 * u - 1| ∈ Ioo (0 : ℝ) 1 :=
    ⟨abs_pos.mpr ht, abs_lt.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩
  set b := inverseRegularizedGamma p⁻¹ |2 * u - 1| with hb
  have hbpos : 0 < b := inverseRegularizedGamma_pos (inv_pos.mpr hp) hv
  have hpow : 0 < b ^ p⁻¹ := rpow_pos_of_pos hbpos _
  have hG : regularizedGamma p⁻¹ b = |2 * u - 1| :=
    regularizedGamma_inverseRegularizedGamma (inv_pos.mpr hp) hv
  rw [cdf_generalizedNormalMeasure_eq hs hp]
  rcases lt_or_gt_of_ne ht with ht | ht
  · simp [sign_of_neg ht, sign_neg, sign_of_pos (mul_pos hs hpow),
      abs_mul, abs_div, abs_of_pos hs, abs_of_pos hpow, hs.ne',
      rpow_inv_rpow hbpos.le hp.ne', hG, abs_of_neg ht]
  · simp [sign_of_pos ht, sign_of_pos (mul_pos hs hpow), abs_of_pos hpow, hs.ne',
      rpow_inv_rpow hbpos.le hp.ne', hG, abs_of_pos ht]

/-- The generalized normal quantile at an interior probability level. Away from
the median it is the signed `p⁻¹` power of an inverse regularized Gamma value. -/
@[simp]
theorem quantile_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) (hu : u ∈ Ioo 0 1) :
    (generalizedNormalMeasure m s p).quantile u =
      if u = 1 / 2 then m else
        m + s * sign (2 * u - 1) * inverseRegularizedGamma p⁻¹ |2 * u - 1| ^ p⁻¹ := by
  split_ifs with hhalf
  · rw [hhalf, one_div, quantile_generalizedNormalMeasure_half hs hp]
  · apply (quantile_generalizedNormalMeasure_eq_iff hs hp hu).mpr
    rw [← cdf_generalizedNormalMeasure_eq hs hp]
    exact cdf_generalizedNormalMeasure_signed_inverse hs hp hu hhalf

/-- Generalized normal quantiles vary continuously with interior probability levels. -/
theorem continuousOn_quantile_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) :
    ContinuousOn (generalizedNormalMeasure m s p).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile _ (continuous_cdf_generalizedNormalMeasure hs hp)
    ((strictMono_cdf_generalizedNormalMeasure hs hp).strictMonoOn _)

/-- Generalized normal quantiles tend to minus infinity as the level decreases to zero. -/
theorem tendsto_quantile_generalizedNormalMeasure_nhdsGT_zero (hs : 0 < s) (hp : 0 < p) :
    Tendsto (fun u ↦ ((generalizedNormalMeasure m s p).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) :=
  Measure.tendsto_quantile_nhdsGT_zero_of_strictMono_cdf _
    (strictMono_cdf_generalizedNormalMeasure hs hp)

/-- Generalized normal quantiles tend to plus infinity as the level increases to one. -/
theorem tendsto_quantile_generalizedNormalMeasure_nhdsLT_one (hs : 0 < s) (hp : 0 < p) :
    Tendsto (fun u ↦ ((generalizedNormalMeasure m s p).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_strictMono_cdf _
    (strictMono_cdf_generalizedNormalMeasure hs hp)

end TauCeti.Probability
