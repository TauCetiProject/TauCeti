/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Laplace.Basic
public import TauCeti.Probability.Quantile
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Quantiles of Laplace laws

For positive scale `b`, the Laplace quantile at an interior level `u` is obtained by inverting
the appropriate exponential branch of the cdf. It is `μ + b * log (2 * u)` below the median and
`μ - b * log (2 * (1 - u))` above it.

The one-sided limits in `EReal` are the support endpoints `⊥` and `⊤`. These limits concern
interior levels, independently of the totalized quantile values at `0` and `1`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 24.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {μ b : ℝ}

/-- The quantile of a Laplace law with positive scale. -/
theorem quantile_laplaceMeasure (hb : 0 < b) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (laplaceMeasure μ b).quantile u =
      if u ≤ 1 / 2 then μ + b * log (2 * u) else μ - b * log (2 * (1 - u)) := by
  let := isProbabilityMeasure_laplaceMeasure hb μ
  by_cases hhalf : u ≤ 1 / 2
  · rw [ite_eq_left hhalf]
    have h2u : 0 < 2 * u := mul_pos (by norm_num) hu.1
    have hlog : log (2 * u) ≤ 0 := (log_nonpos_iff h2u.le).2 (by linarith)
    have hq : μ + b * log (2 * u) ≤ μ :=
      add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hb.le hlog)
    refine eq_of_forall_ge_iff fun x ↦ ?_
    rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_laplaceMeasure_eq hb]
    by_cases hx : x < μ
    · rw [ite_eq_left hx]
      calc
        u ≤ exp ((x - μ) / b) / 2 ↔ 2 * u ≤ exp ((x - μ) / b) := by
          constructor <;> intro h <;> linarith
        _ ↔ log (2 * u) ≤ (x - μ) / b := (log_le_iff_le_exp h2u).symm
        _ ↔ μ + b * log (2 * u) ≤ x := by
          rw [le_div_iff₀ hb]
          constructor <;> intro h <;> linarith
    · rw [ite_eq_right hx]
      have harg : -(x - μ) / b ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr (not_lt.mp hx))) hb.le
      exact iff_of_true (by linarith [exp_le_one_iff.mpr harg]) (hq.trans (not_lt.mp hx))
  · rw [ite_eq_right hhalf]
    have hhalf' : 1 / 2 < u := lt_of_not_ge hhalf
    have h2u : 0 < 2 * (1 - u) := mul_pos (by norm_num) (sub_pos.mpr hu.2)
    have hlog : log (2 * (1 - u)) < 0 :=
      (log_neg_iff h2u).2 (by linarith)
    have hq : μ < μ - b * log (2 * (1 - u)) := by
      nlinarith
    refine eq_of_forall_ge_iff fun x ↦ ?_
    rw [Measure.quantile_le_iff _ hu.1 hu.2, cdf_laplaceMeasure_eq hb]
    by_cases hx : x < μ
    · rw [ite_eq_left hx]
      have harg : (x - μ) / b < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hx) hb
      exact iff_of_false (by linarith [exp_lt_one_iff.mpr harg]) (not_le.mpr (hx.trans hq))
    · rw [ite_eq_right hx]
      calc
        u ≤ 1 - exp (-(x - μ) / b) / 2 ↔
            exp (-(x - μ) / b) ≤ 2 * (1 - u) := by
          constructor <;> intro h <;> linarith
        _ ↔ -(x - μ) / b ≤ log (2 * (1 - u)) :=
          (le_log_iff_exp_le h2u).symm
        _ ↔ μ - b * log (2 * (1 - u)) ≤ x := by
          rw [div_le_iff₀ hb]
          constructor <;> intro h <;> linarith

/-- Laplace quantiles tend to minus infinity as the level tends to `0` from above. -/
theorem tendsto_quantile_laplaceMeasure_nhdsGT_zero (hb : 0 < b) :
    Tendsto (fun u ↦ ((laplaceMeasure μ b).quantile u : EReal)) (𝓝[>] 0) (𝓝 ⊥) := by
  let := isProbabilityMeasure_laplaceMeasure hb μ
  apply EReal.tendsto_coe_nhds_bot_iff.2
  refine tendsto_atBot.2 fun x ↦ ?_
  have hx : 0 < cdf (laplaceMeasure μ b) x := by
    rw [cdf_laplaceMeasure_eq hb]
    split_ifs with hxm
    · exact div_pos (exp_pos _) (by norm_num)
    · have harg : -(x - μ) / b ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (sub_nonneg.mpr (not_lt.mp hxm))) hb.le
      linarith [exp_le_one_iff.mpr harg]
  filter_upwards [Ioo_mem_nhdsGT hx] with u hu
  exact (Measure.quantile_le_iff _ hu.1
    (hu.2.trans_le (cdf_le_one (laplaceMeasure μ b) x))).2 hu.2.le

/-- Laplace quantiles tend to plus infinity as the level tends to `1` from below. -/
theorem tendsto_quantile_laplaceMeasure_nhdsLT_one (hb : 0 < b) :
    Tendsto (fun u ↦ ((laplaceMeasure μ b).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  let := isProbabilityMeasure_laplaceMeasure hb μ
  apply EReal.tendsto_coe_nhds_top_iff.2
  refine tendsto_atTop.2 fun x ↦ ?_
  have hx : cdf (laplaceMeasure μ b) x < 1 := by
    rw [cdf_laplaceMeasure_eq hb]
    split_ifs with hxm
    · have harg : (x - μ) / b < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hxm) hb
      linarith [exp_lt_one_iff.mpr harg]
    · exact sub_lt_self 1 (div_pos (exp_pos _) (by norm_num))
  filter_upwards [Ioo_mem_nhdsLT hx] with u hu
  exact ((Measure.lt_quantile_iff _
    ((cdf_nonneg (laplaceMeasure μ b) x).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
