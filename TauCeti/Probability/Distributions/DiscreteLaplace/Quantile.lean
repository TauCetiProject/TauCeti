/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.DiscreteLaplace.Cdf
public import TauCeti.Probability.Quantile.Discrete
import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of discrete Laplace laws

The real-cast lower quantile is the least integer crossing of the explicit geometric
cumulative masses. Equality at a jump selects the smaller integer, as required for a lower
quantile. At `q = 0` every interior quantile is the center. For positive `q`, the one-sided
limits at levels zero and one are minus and plus infinity, respectively.

## References

* S. Inusah and T. J. Kozubowski, *A discrete analogue of the Laplace distribution*, Journal of
  Statistical Planning and Inference 136 (2006), 1090–1102.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- An integer is the discrete Laplace lower quantile exactly when it is the least crossing
of the geometric cumulative masses. The non-strict crossing retains cumulative jump levels. -/
theorem quantile_map_intCast_discreteLaplaceMeasure_eq_iff (m : ℤ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℤ) :
    ((discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)).quantile u = k ↔
      IsLeast {j : ℤ | u ≤ if j < m then q ^ (m - j).toNat / (1 + q)
        else 1 - q ^ ((j - m).toNat + 1) / (1 + q)} k := by
  have := isProbabilityMeasure_discreteLaplaceMeasure m hq0 hq1
  rw [Measure.quantile_map_intCast_eq_iff _ hu]
  simp_rw [discreteLaplaceMeasure_real_Iic m hq0 hq1]

/-- The point-mass boundary has constant interior quantile equal to the integer center. -/
theorem quantile_map_intCast_discreteLaplaceMeasure_zero (m : ℤ) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    ((discreteLaplaceMeasure m 0).map (Int.cast : ℤ → ℝ)).quantile u = m := by
  simp [Measure.quantile_dirac _ hu.1 hu.2.le]

/-- The lower support endpoint is minus infinity for positive `q`, and the center for `q = 0`.
The limit concerns interior levels, independently of the totalized quantile at zero. -/
theorem tendsto_quantile_map_intCast_discreteLaplaceMeasure_nhdsGT_zero (m : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun u ↦
      (((discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if q = 0 then ((m : ℝ) : EReal) else ⊥)) := by
  by_cases hq : q = 0
  · subst q
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    simp only [quantile_map_intCast_discreteLaplaceMeasure_zero m hu]
  · rw [ite_eq_right hq]
    have := isProbabilityMeasure_discreteLaplaceMeasure m hq0 hq1
    have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    refine Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos _ fun b ↦ ?_
    rw [cdf_map_intCast_discreteLaplaceMeasure m hq0 hq1]
    split_ifs
    · positivity
    · have hpow : q ^ ((⌊b⌋ - m).toNat + 1) ≤ 1 := pow_le_one₀ hq0 hq1.le
      have hdiv : q ^ ((⌊b⌋ - m).toNat + 1) / (1 + q) < 1 :=
        (div_lt_one (by positivity)).2 (by linarith)
      linarith

/-- The upper support endpoint is plus infinity for positive `q`, and the center for `q = 0`.
The limit is from below level one and includes the degenerate law. -/
theorem tendsto_quantile_map_intCast_discreteLaplaceMeasure_nhdsLT_one (m : ℤ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun u ↦
      (((discreteLaplaceMeasure m q).map (Int.cast : ℤ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (if q = 0 then ((m : ℝ) : EReal) else ⊤)) := by
  by_cases hq : q = 0
  · subst q
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    simp only [quantile_map_intCast_discreteLaplaceMeasure_zero m hu]
  · rw [ite_eq_right hq]
    have := isProbabilityMeasure_discreteLaplaceMeasure m hq0 hq1
    have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    refine Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _ fun b ↦ ?_
    rw [cdf_map_intCast_discreteLaplaceMeasure m hq0 hq1]
    split_ifs
    · have hpow : q ^ (m - ⌊b⌋).toNat ≤ 1 := pow_le_one₀ hq0 hq1.le
      exact (div_lt_one (by positivity)).2 (by linarith)
    · exact sub_lt_self _ (by positivity)

end TauCeti.Probability
