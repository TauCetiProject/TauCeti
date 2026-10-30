/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.HalfStudentT.Basic
public import TauCeti.Probability.Distributions.StudentT.Quantile

/-!
# Cdfs and quantiles of half-Student t laws

The cdf of a half-Student t variable at a nonnegative point is twice the Student t cdf at the
standardized point minus one. Its interior quantile is the Student t quantile at level
`(1 + u) / 2`, multiplied by the scale. This applies to the half-Cauchy specialization too.
The quantile is continuous and strictly increasing, with endpoint limits zero and infinity.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ν s u x : ℝ}

private theorem cdf_halfStudentTMeasure_eq_cdf_map_abs (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    cdf (halfStudentTMeasure ν s) x = cdf ((studentTMeasure ν).map (|·|)) (x / s) := by
  let _ := isProbabilityMeasure_studentTMeasure hν
  rw [halfStudentTMeasure_eq_map_abs hν hs]
  simpa only [zero_add, sub_zero] using
    cdf_map_affine_of_pos (μ := (studentTMeasure ν).map (|·|)) (a := 0) hs x

private theorem quantile_halfStudentTMeasure_eq_quantile_map_abs (hν : 0 < ν) (hs : 0 < s)
    (hu : u ∈ Ioo 0 1) :
    (halfStudentTMeasure ν s).quantile u = s * ((studentTMeasure ν).map (|·|)).quantile u := by
  let _ := isProbabilityMeasure_studentTMeasure hν
  rw [halfStudentTMeasure_eq_map_abs hν hs]
  simpa only [zero_add] using
    quantile_map_affine_pos (μ := (studentTMeasure ν).map (|·|)) (a := 0) hs hu.1 hu.2

/-- The half-Student t cdf on the nonnegative half-line is obtained by folding the Student t
cdf and rescaling its argument. -/
theorem cdf_halfStudentTMeasure_of_nonneg (hν : 0 < ν) (hs : 0 < s) (hx : 0 ≤ x) :
    cdf (halfStudentTMeasure ν s) x = 2 * cdf (studentTMeasure ν) (x / s) - 1 := by
  let _ := isProbabilityMeasure_studentTMeasure hν
  rw [cdf_halfStudentTMeasure_eq_cdf_map_abs hν hs,
    Measure.cdf_map_abs_of_isNegInvariant _ (div_nonneg hx hs.le)]

/-- Below zero the half-Student t cdf vanishes. -/
@[simp]
theorem cdf_halfStudentTMeasure_of_neg (hν : 0 < ν) (hs : 0 < s) (hx : x < 0) :
    cdf (halfStudentTMeasure ν s) x = 0 := by
  let _ := isProbabilityMeasure_studentTMeasure hν
  rw [cdf_halfStudentTMeasure_eq_cdf_map_abs hν hs,
    Measure.cdf_map_abs_of_neg _ (div_neg_of_neg_of_pos hx hs)]

/-- The cdf of the half-Student t law, including its zero extension below the support. -/
theorem cdf_halfStudentTMeasure_eq (hν : 0 < ν) (hs : 0 < s) (x : ℝ) :
    cdf (halfStudentTMeasure ν s) x =
      if x < 0 then 0 else 2 * cdf (studentTMeasure ν) (x / s) - 1 := by
  split_ifs with hx
  · exact cdf_halfStudentTMeasure_of_neg hν hs hx
  · exact cdf_halfStudentTMeasure_of_nonneg hν hs (le_of_not_gt hx)

/-- Every valid half-Student t law has a continuous cdf. -/
theorem continuous_cdf_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) :
    Continuous (cdf (halfStudentTMeasure ν s)) := by
  let _ := isProbabilityMeasure_halfStudentTMeasure hν hs
  exact Measure.continuous_cdf_of_noAtoms _

/-- The half-Student t cdf is strictly increasing on its nonnegative support. -/
theorem strictMonoOn_cdf_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) :
    StrictMonoOn (cdf (halfStudentTMeasure ν s)) (Ici 0) := by
  intro x hx y hy hxy
  rw [cdf_halfStudentTMeasure_of_nonneg hν hs hx,
    cdf_halfStudentTMeasure_of_nonneg hν hs hy]
  have h := strictMono_cdf_studentTMeasure hν ((div_lt_div_iff_of_pos_right hs).2 hxy)
  linarith

/-- The interior half-Student t quantile is a rescaled upper-half Student t quantile. -/
@[simp]
theorem quantile_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (halfStudentTMeasure ν s).quantile u = s * (studentTMeasure ν).quantile ((1 + u) / 2) := by
  let _ := isProbabilityMeasure_studentTMeasure hν
  rw [quantile_halfStudentTMeasure_eq_quantile_map_abs hν hs hu, Measure.quantile_map_abs _ hu.1]

/-- Interior half-Student t quantiles are strictly positive. -/
theorem quantile_halfStudentTMeasure_pos (hν : 0 < ν) (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    0 < (halfStudentTMeasure ν s).quantile u := by
  rw [quantile_halfStudentTMeasure hν hs hu]
  exact mul_pos hs (quantile_studentTMeasure_pos hν (by constructor <;> linarith [hu.1, hu.2]))

/-- The half-Student t quantile is strictly increasing on interior probability levels. -/
theorem strictMonoOn_quantile_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) :
    StrictMonoOn (halfStudentTMeasure ν s).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_halfStudentTMeasure hν hs)

/-- The half-Student t quantile is continuous on interior probability levels. -/
theorem continuousOn_quantile_halfStudentTMeasure (hν : 0 < ν) (hs : 0 < s) :
    ContinuousOn (halfStudentTMeasure ν s).quantile (Ioo 0 1) := by
  apply Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Ici
    (strictMonoOn_cdf_halfStudentTMeasure hν hs)
  intro u hu
  exact (quantile_halfStudentTMeasure_pos hν hs hu).le

/-- Half-Student t quantiles tend to zero as the probability level tends to zero from above. -/
theorem tendsto_quantile_halfStudentTMeasure_nhdsGT_zero (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun u ↦ ((halfStudentTMeasure ν s).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hcont := Measure.continuousOn_quantile _ (continuous_cdf_studentTMeasure hν)
    ((strictMono_cdf_studentTMeasure hν).strictMonoOn _)
  have hhalf : (2⁻¹ : ℝ) ∈ Ioo 0 1 := by norm_num
  have hlim : Tendsto (fun u : ℝ ↦ (1 + u) / 2) (𝓝[>] 0) (𝓝 (2⁻¹ : ℝ)) := by
    have hfun : Continuous (fun u : ℝ ↦ (1 + u) / 2) := by fun_prop
    simpa using (hfun.tendsto 0).mono_left nhdsWithin_le_nhds
  have hq := (hcont.continuousAt (isOpen_Ioo.mem_nhds hhalf)).tendsto.comp hlim
  have hscaled := hq.const_mul s
  rw [quantile_studentTMeasure_half hν, mul_zero] at hscaled
  apply (EReal.tendsto_coe.2 hscaled).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_halfStudentTMeasure hν hs hu).symm

/-- Half-Student t quantiles tend to infinity as the probability level tends to one from below. -/
theorem tendsto_quantile_halfStudentTMeasure_nhdsLT_one (hν : 0 < ν) (hs : 0 < s) :
    Tendsto (fun u ↦ ((halfStudentTMeasure ν s).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  rw [EReal.tendsto_coe_nhds_top_iff]
  have harg : Tendsto (fun u : ℝ ↦ (1 + u) / 2) (𝓝[<] 1) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hfun : Continuous (fun u : ℝ ↦ (1 + u) / 2) := by fun_prop
      simpa using (hfun.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [mem_Iio] at *
      linarith
  have hlim := ((EReal.tendsto_coe_nhds_top_iff.1
    (tendsto_quantile_studentTMeasure_nhdsLT_one hν)).comp harg).const_mul_atTop hs
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_halfStudentTMeasure hν hs hu).symm

end TauCeti.Probability
