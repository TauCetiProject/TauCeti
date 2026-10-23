/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.StudentT.Cdf
public import TauCeti.Probability.Quantile

/-!
# Quantiles of Student's t laws

For positive degree `ν`, this file inverts the Student t cdf using the inverse regularized
incomplete Beta function with shapes `ν / 2` and `1 / 2`. The lower and upper halves use levels
`2 * u` and `2 * (1 - u)` respectively, and the median quantile is zero. The quantile is continuous
and strictly increasing on the interior probability levels, with limits minus and plus infinity.

## Main results

* `quantile_studentTMeasure` gives the explicit formula at every level `0 < u < 1`.
* `quantile_studentTMeasure_half` gives its value at the median.
* `tendsto_quantile_studentTMeasure_nhdsGT_zero` and
  `tendsto_quantile_studentTMeasure_nhdsLT_one` give the endpoint limits in `EReal`.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 28.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {ν u : ℝ}

private theorem studentT_betaArgument_sqrt (hν : 0 < ν) {b : ℝ} (hb : b ∈ Ioo 0 1) :
    ν / (ν + (sqrt (ν * (1 / b - 1))) ^ 2) = b := by
  have h : 0 < 1 / b - 1 := by
    rw [sub_pos, lt_div_iff₀ hb.1]
    simpa using hb.2
  rw [Real.sq_sqrt (mul_pos hν h).le]
  field_simp [hb.1.ne', hν.ne']
  ring

/-- The median quantile of a positive-degree Student t law is zero. -/
@[simp]
theorem quantile_studentTMeasure_half (hν : 0 < ν) :
    (studentTMeasure ν).quantile (2⁻¹) = 0 := by
  have hF : cdf (studentTMeasure ν) 0 = 2⁻¹ := by
    have harg : ν / (ν + (0 : ℝ) ^ 2) = 1 := by simp [hν.ne']
    rw [cdf_studentTMeasure_eq hν, ite_eq_right (by norm_num), harg,
      regularizedIncompleteBeta_eq_one_of_one_le (by linarith : 0 ≤ ν / 2) one_half_pos le_rfl]
    ring
  rw [← hF]
  exact Measure.quantile_cdf _ ((strictMono_cdf_studentTMeasure hν).strictMonoOn _)
    (by rw [hF]; norm_num)

/-- Student t quantiles are strictly positive at probability levels above the median. -/
theorem quantile_studentTMeasure_pos (hν : 0 < ν) (hu : u ∈ Ioo 2⁻¹ 1) :
    0 < (studentTMeasure ν).quantile u := by
  have h := Measure.strictMonoOn_quantile _ (continuous_cdf_studentTMeasure hν)
    (by norm_num : (2⁻¹ : ℝ) ∈ Ioo 0 1)
    (by constructor <;> linarith [hu.1, hu.2] : u ∈ Ioo 0 1) hu.1
  simpa only [quantile_studentTMeasure_half hν] using h

private theorem quantile_studentTMeasure_of_lt_half (hν : 0 < ν) (hu0 : 0 < u)
    (huHalf : u < 1 / 2) :
    (studentTMeasure ν).quantile u =
      -sqrt (ν * (1 / inverseRegularizedIncompleteBeta (ν / 2) (1 / 2) (2 * u) - 1)) := by
  have ha : 0 < ν / 2 := by linarith
  have hv : 2 * u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set b := inverseRegularizedIncompleteBeta (ν / 2) (1 / 2) (2 * u)
  have hb := inverseRegularizedIncompleteBeta_mem_Ioo ha one_half_pos hv.1 hv.2
  have hpos : 0 < ν * (1 / b - 1) := by
    apply mul_pos hν
    rw [sub_pos, lt_div_iff₀ hb.1]
    simpa using hb.2
  have hF : cdf (studentTMeasure ν) (-sqrt (ν * (1 / b - 1))) = u := by
    rw [cdf_studentTMeasure_eq hν, ite_eq_left (neg_neg_of_pos (sqrt_pos.2 hpos)), neg_sq,
      studentT_betaArgument_sqrt hν hb, regularizedIncompleteBeta_inverse ha one_half_pos hv.1 hv.2]
    ring
  rw [← hF]
  exact Measure.quantile_cdf _ ((strictMono_cdf_studentTMeasure hν).strictMonoOn _)
    (by rw [hF]; exact ⟨hu0, by linarith⟩)

private theorem quantile_studentTMeasure_of_half_lt (hν : 0 < ν) (hu1 : u < 1)
    (huHalf : 1 / 2 < u) :
    (studentTMeasure ν).quantile u =
      sqrt (ν * (1 / inverseRegularizedIncompleteBeta (ν / 2) (1 / 2) (2 * (1 - u)) - 1)) := by
  have ha : 0 < ν / 2 := by linarith
  have hv : 2 * (1 - u) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  set b := inverseRegularizedIncompleteBeta (ν / 2) (1 / 2) (2 * (1 - u))
  have hb := inverseRegularizedIncompleteBeta_mem_Ioo ha one_half_pos hv.1 hv.2
  have hF : cdf (studentTMeasure ν) (sqrt (ν * (1 / b - 1))) = u := by
    rw [cdf_studentTMeasure_eq hν, ite_eq_right (not_lt.2 (sqrt_nonneg _)),
      studentT_betaArgument_sqrt hν hb, regularizedIncompleteBeta_inverse ha one_half_pos hv.1 hv.2]
    ring
  rw [← hF]
  exact Measure.quantile_cdf _ ((strictMono_cdf_studentTMeasure hν).strictMonoOn _)
    (by rw [hF]; exact ⟨by linarith, hu1⟩)

/-- The lower quantile of a Student t law at an interior probability level, in terms of the inverse
regularized incomplete Beta function. The median is zero; the two other branches have opposite
signs and use complementary Beta levels. -/
theorem quantile_studentTMeasure (hν : 0 < ν) (hu : u ∈ Ioo 0 1) :
    (studentTMeasure ν).quantile u =
      if u < 1 / 2 then
        -sqrt (ν * (1 / inverseRegularizedIncompleteBeta (ν / 2) (1 / 2) (2 * u) - 1))
      else if u = 1 / 2 then 0 else
        sqrt (ν * (1 / inverseRegularizedIncompleteBeta (ν / 2) (1 / 2) (2 * (1 - u)) - 1)) := by
  split_ifs with hlt heq
  · exact quantile_studentTMeasure_of_lt_half hν hu.1 hlt
  · rw [heq, one_div, quantile_studentTMeasure_half hν]
  · exact quantile_studentTMeasure_of_half_lt hν hu.2 (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm heq))

/-- Student t quantiles tend to minus infinity as the probability level tends to zero from above. -/
theorem tendsto_quantile_studentTMeasure_nhdsGT_zero (hν : 0 < ν) :
    Tendsto (fun u ↦ ((studentTMeasure ν).quantile u : EReal)) (𝓝[>] 0) (𝓝 ⊥) :=
  Measure.tendsto_quantile_nhdsGT_zero_of_strictMono_cdf _ (strictMono_cdf_studentTMeasure hν)

/-- Student t quantiles tend to plus infinity as the probability level tends to one from below. -/
theorem tendsto_quantile_studentTMeasure_nhdsLT_one (hν : 0 < ν) :
    Tendsto (fun u ↦ ((studentTMeasure ν).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_strictMono_cdf _ (strictMono_cdf_studentTMeasure hν)

end TauCeti.Probability
