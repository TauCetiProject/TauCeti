/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.IrwinHall.Cdf
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of Irwin–Hall laws

For `n > 0` and `0 < u < 1`, the Irwin–Hall quantile is the unique root in `(0, n)`
of its alternating truncated-power cdf. The quantile is continuous and strictly increasing
in `u`, with one-sided limits `0` and `n`. Order zero has constant interior quantile zero.
No choice of a polynomial branch or radical expression is needed at integer knots.

The inverse characterizations and regularity use the shared measure-level quantile API,
together with the exact support and cdf of the Irwin–Hall law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {n : ℕ} {u x : ℝ}

/-- Interior quantiles of positive-order Irwin–Hall laws lie strictly between `0` and `n`. -/
theorem quantile_irwinHallMeasure_mem_Ioo (hn : 0 < n) (hu : u ∈ Ioo 0 1) :
    (irwinHallMeasure n).quantile u ∈ Ioo 0 (n : ℝ) := by
  have hroot := Measure.cdf_quantile _ (continuous_cdf_irwinHallMeasure hn) hu.1 hu.2
  exact ⟨(cdf_irwinHallMeasure_pos_iff hn).1 (hroot.symm ▸ hu.1),
    (cdf_irwinHallMeasure_lt_one_iff hn).1 (hroot.symm ▸ hu.2)⟩

/-- An interior Irwin–Hall quantile is the unique root of the alternating truncated-power
cdf. Every root lies in `(0, n)`, and the formula applies at integer knots as well. -/
theorem quantile_irwinHallMeasure_eq_iff (hn : 0 < n) (hu : u ∈ Ioo 0 1) :
    (irwinHallMeasure n).quantile u = x ↔
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
        max (x - k) 0 ^ n) / n.factorial = u := by
  have hq := quantile_irwinHallMeasure_mem_Ioo hn hu
  have hroot := Measure.cdf_quantile _ (continuous_cdf_irwinHallMeasure hn) hu.1 hu.2
  rw [← cdf_irwinHallMeasure_eq hn]
  constructor
  · rintro rfl
    exact hroot
  · intro hxroot
    have hx : x ∈ Ioo 0 (n : ℝ) :=
      ⟨(cdf_irwinHallMeasure_pos_iff hn).1 (hxroot.symm ▸ hu.1),
        (cdf_irwinHallMeasure_lt_one_iff hn).1 (hxroot.symm ▸ hu.2)⟩
    exact (strictMonoOn_cdf_irwinHallMeasure hn).injOn (Ioo_subset_Icc_self hq)
      (Ioo_subset_Icc_self hx) (hroot.trans hxroot.symm)

/-- Irwin–Hall quantiles increase strictly at interior probability levels. -/
theorem strictMonoOn_quantile_irwinHallMeasure (hn : 0 < n) :
    StrictMonoOn (irwinHallMeasure n).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_irwinHallMeasure hn)

/-- The Irwin–Hall quantile is continuous on interior probability levels. -/
theorem continuousOn_quantile_irwinHallMeasure (hn : 0 < n) :
    ContinuousOn (irwinHallMeasure n).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Icc
    (strictMonoOn_cdf_irwinHallMeasure hn)
    (fun _ hu ↦ Ioo_subset_Icc_self (quantile_irwinHallMeasure_mem_Ioo hn hu))

/-- The empty-sum law has constant interior quantile zero. -/
theorem quantile_irwinHallMeasure_zero (hu : u ∈ Ioo 0 1) :
    (irwinHallMeasure 0).quantile u = 0 := by
  rw [irwinHallMeasure_zero, Measure.quantile_dirac _ hu.1 hu.2.le]

/-- Irwin–Hall quantiles tend to zero as the level tends to zero from above,
including at order zero. -/
theorem tendsto_quantile_irwinHallMeasure_nhdsGT_zero (n : ℕ) :
    Tendsto (irwinHallMeasure n).quantile (𝓝[>] 0) (𝓝 0) := by
  by_cases hn : n = 0
  · subst n
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    exact (quantile_irwinHallMeasure_zero hu).symm
  apply EReal.tendsto_coe.1
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_mem_Icc_irwinHallMeasure n).mono fun _ hx ↦ hx.1)
    (fun _ hx ↦ (cdf_irwinHallMeasure_pos_iff (Nat.pos_of_ne_zero hn)).2 hx)

/-- Irwin–Hall quantiles tend to `n` as the level tends to one from below,
including at order zero. -/
theorem tendsto_quantile_irwinHallMeasure_nhdsLT_one (n : ℕ) :
    Tendsto (irwinHallMeasure n).quantile (𝓝[<] 1) (𝓝 (n : ℝ)) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    exact (quantile_irwinHallMeasure_zero hu).symm
  have hn' := Nat.pos_of_ne_zero hn
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · have ha' := (cdf_irwinHallMeasure_lt_one_iff hn').2 ha
    filter_upwards [Ioo_mem_nhdsLT ha'] with u hu
    exact (Measure.lt_quantile_iff _ ((cdf_nonneg _ a).trans_lt hu.1) hu.2).2 hu.1
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    exact (quantile_irwinHallMeasure_mem_Ioo hn' hu).2.trans hb

end TauCeti.Probability
