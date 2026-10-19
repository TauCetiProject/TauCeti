/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Cdf

/-!
# Quantiles of the generalized extreme-value law

For positive scale and an interior probability level `u`, the generalized extreme-value
quantile in the maximum convention is

`m + s * ((-log u) ^ (-ξ) - 1) / ξ`

at nonzero shape, and the Gumbel quantile `m - s * log (-log u)` at shape zero. The proof
uses the exact cdf formula and strict increase on the interior of the support, so the result
characterizes the lower quantile rather than merely exhibiting a point with the right cdf.

## Main results

* `quantile_generalizedExtremeValueMeasure_of_shape_ne_zero` gives the nonzero-shape formula.
* `quantile_generalizedExtremeValueMeasure` gives the formula for every shape.
* `continuousOn_quantile_generalizedExtremeValueMeasure` proves continuity in the probability
  level.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {s ξ u : ℝ}

private theorem cdf_preimage_Ioo_subset_generalizedExtremeValueSupportInterior
    (hs : 0 < s) (hξ : ξ ≠ 0) (m : ℝ) :
    cdf (generalizedExtremeValueMeasure m s ξ) ⁻¹' Ioo 0 1 ⊆
      {x | 0 < 1 + ξ * (x - m) / s} := by
  intro x hx
  by_contra hsupport
  have hnonpos : 1 + ξ * (x - m) / s ≤ 0 := not_lt.mp hsupport
  rcases lt_or_gt_of_ne hξ with hξ | hξ
  · have hone := cdf_generalizedExtremeValueMeasure_eq_one hs hξ hnonpos
    exact hx.2.ne hone
  · have hzero := cdf_generalizedExtremeValueMeasure_eq_zero hs hξ hnonpos
    exact hx.1.ne' hzero

/-- The lower quantile of a positive-scale, nonzero-shape generalized extreme-value law is
`m + s * ((-log u) ^ (-ξ) - 1) / ξ` at every interior probability level. -/
theorem quantile_generalizedExtremeValueMeasure_of_shape_ne_zero (hs : 0 < s) (hξ : ξ ≠ 0)
    (m : ℝ) (hu : u ∈ Ioo 0 1) :
    (generalizedExtremeValueMeasure m s ξ).quantile u =
      m + s * ((-Real.log u) ^ (-ξ) - 1) / ξ := by
  have hlog : 0 < -Real.log u := neg_pos.mpr (Real.log_neg hu.1 hu.2)
  let q := m + s * ((-Real.log u) ^ (-ξ) - 1) / ξ
  have hsupport_eq : 1 + ξ * (q - m) / s = (-Real.log u) ^ (-ξ) := by
    dsimp only [q]
    field_simp [hs.ne', hξ]
    ring
  have hsupport : 0 < 1 + ξ * (q - m) / s := by
    rw [hsupport_eq]
    exact Real.rpow_pos_of_pos hlog _
  have hexponent : (-ξ) * (-1 / ξ) = 1 := by
    field_simp [hξ]
  have hpower : ((-Real.log u) ^ (-ξ)) ^ (-1 / ξ) = -Real.log u := by
    rw [← Real.rpow_mul hlog.le, hexponent, Real.rpow_one]
  have hcdf : cdf (generalizedExtremeValueMeasure m s ξ) q = u := by
    rw [cdf_generalizedExtremeValueMeasure_eq_of_pos hs hξ hsupport, hsupport_eq,
      hpower, neg_neg, Real.exp_log hu.1]
  have hstrict : StrictMonoOn (cdf (generalizedExtremeValueMeasure m s ξ))
      (cdf (generalizedExtremeValueMeasure m s ξ) ⁻¹' Ioo 0 1) :=
    (strictMonoOn_cdf_generalizedExtremeValueMeasure hs hξ m).mono
      (cdf_preimage_Ioo_subset_generalizedExtremeValueSupportInterior hs hξ m)
  change (generalizedExtremeValueMeasure m s ξ).quantile u = q
  rw [← hcdf]
  exact Measure.quantile_cdf _ hstrict (by rw [hcdf]; exact hu)

/-- The lower quantile of a positive-scale generalized extreme-value law. At shape zero this is
the Gumbel quantile; at nonzero shape it is the power formula. -/
theorem quantile_generalizedExtremeValueMeasure (hs : 0 < s) (m ξ : ℝ) (hu : u ∈ Ioo 0 1) :
    (generalizedExtremeValueMeasure m s ξ).quantile u =
      if ξ = 0 then m - s * Real.log (-Real.log u)
      else m + s * ((-Real.log u) ^ (-ξ) - 1) / ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ, quantile_gumbelMeasure hs m hu]
  · rw [ite_eq_right hξ,
      quantile_generalizedExtremeValueMeasure_of_shape_ne_zero hs hξ m hu]

/-- Generalized extreme-value quantiles vary continuously with the probability level on the
open unit interval. -/
theorem continuousOn_quantile_generalizedExtremeValueMeasure (hs : 0 < s) (m ξ : ℝ) :
    ContinuousOn (generalizedExtremeValueMeasure m s ξ).quantile (Ioo 0 1) := by
  by_cases hξ : ξ = 0
  · have hcont : ContinuousOn (fun v : ℝ ↦ m - s * Real.log (-Real.log v)) (Ioo 0 1) := by
      apply continuousOn_of_forall_continuousAt
      intro v hv
      have hv0 : v ≠ 0 := hv.1.ne'
      have hlog : -Real.log v ≠ 0 :=
        (neg_pos.mpr (Real.log_neg hv.1 hv.2)).ne'
      fun_prop
    refine hcont.congr fun v hv ↦ ?_
    simpa [hξ] using quantile_gumbelMeasure hs m hv
  · have hcont : ContinuousOn
        (fun v : ℝ ↦ m + s * ((-Real.log v) ^ (-ξ) - 1) / ξ) (Ioo 0 1) := by
      apply continuousOn_of_forall_continuousAt
      intro v hv
      have hv0 : v ≠ 0 := hv.1.ne'
      have hlog : -Real.log v ≠ 0 :=
        (neg_pos.mpr (Real.log_neg hv.1 hv.2)).ne'
      have hbase : ContinuousAt (fun w : ℝ ↦ -Real.log w) v := by fun_prop
      exact continuousAt_const.add
        ((continuousAt_const.mul
          ((hbase.rpow_const (Or.inl hlog)).sub continuousAt_const)).div_const ξ)
    refine hcont.congr fun v hv ↦ ?_
    exact quantile_generalizedExtremeValueMeasure_of_shape_ne_zero hs hξ m hv

end TauCeti.Probability
