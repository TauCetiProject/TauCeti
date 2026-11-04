/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Bates.Basic
public import TauCeti.Probability.Distributions.IrwinHall.Quantile

/-!
# Quantiles of Bates laws

At positive order and an interior probability level, the Bates quantile is the unique root
of the alternating truncated-power cdf, and lies in `(0, 1)`. These quantiles are continuous
and strictly increasing in the level, with one-sided limits `0` and `1`.
The root characterization applies at the polynomial knots as well; it does not require
choosing a polynomial branch or an arbitrary-degree radical formula.

The results transport the Irwin–Hall quantile theory through the existing scaling identity
`quantile_batesMeasure`. Order zero is the zero measure, not a probability boundary law;
only continuity and the lower endpoint limit below include that totalized case.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 26.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti.Probability

variable {n : ℕ} {u x : ℝ}

/-- Interior quantiles of positive-order Bates laws lie strictly between zero and one. -/
theorem quantile_batesMeasure_mem_Ioo (hn : 0 < n) (hu : u ∈ Ioo 0 1) :
    (batesMeasure n).quantile u ∈ Ioo 0 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hq := quantile_irwinHallMeasure_mem_Ioo hn hu
  rw [quantile_batesMeasure]
  exact ⟨div_pos hq.1 hnR, (div_lt_one hnR).2 hq.2⟩

/-- A Bates quantile at an interior level is the unique real root of the alternating
truncated-power cdf. Every root lies in `(0, 1)`, including roots at polynomial knots. -/
theorem quantile_batesMeasure_eq_iff (hn : 0 < n) (hu : u ∈ Ioo 0 1) :
    (batesMeasure n).quantile u = x ↔
      (∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * (n.choose k : ℝ) *
        max (n * x - k) 0 ^ n) / n.factorial = u := by
  rw [quantile_batesMeasure, div_eq_iff (Nat.cast_ne_zero.mpr hn.ne'), mul_comm x,
    quantile_irwinHallMeasure_eq_iff hn hu]

/-- Bates quantiles are strictly increasing on interior probability levels at positive order. -/
theorem strictMonoOn_quantile_batesMeasure (hn : 0 < n) :
    StrictMonoOn (batesMeasure n).quantile (Ioo 0 1) := by
  intro u hu v hv huv
  simpa only [quantile_batesMeasure] using
    (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hn : (0 : ℝ) < n)).2
      (strictMonoOn_quantile_irwinHallMeasure hn hu hv huv)

/-- Bates quantiles are continuous at interior probability levels, including for the
order-zero zero measure. -/
theorem continuousOn_quantile_batesMeasure (n : ℕ) :
    ContinuousOn (batesMeasure n).quantile (Ioo 0 1) := by
  rw [funext (quantile_batesMeasure n)]
  exact (continuousOn_quantile_irwinHallMeasure n).div_const (n : ℝ)

/-- Bates quantiles tend to zero as the level decreases to zero, including for the
order-zero zero measure. No value at level zero is asserted. -/
theorem tendsto_quantile_batesMeasure_nhdsGT_zero (n : ℕ) :
    Tendsto (batesMeasure n).quantile (𝓝[>] 0) (𝓝 0) := by
  rw [funext (quantile_batesMeasure n)]
  simpa only [zero_div] using
    (tendsto_quantile_irwinHallMeasure_nhdsGT_zero n).div_const (n : ℝ)

/-- Positive-order Bates quantiles tend to one as the level increases to one.
No value at level one is asserted. -/
theorem tendsto_quantile_batesMeasure_nhdsLT_one (hn : 0 < n) :
    Tendsto (batesMeasure n).quantile (𝓝[<] 1) (𝓝 1) := by
  rw [funext (quantile_batesMeasure n)]
  simpa only [div_self (Nat.cast_ne_zero.mpr hn.ne' : (n : ℝ) ≠ 0)] using
    (tendsto_quantile_irwinHallMeasure_nhdsLT_one n).div_const (n : ℝ)

end TauCeti.Probability
