/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Zipf.Cdf
public import TauCeti.Probability.Quantile.Discrete

/-!
# Quantiles of Zipf laws

An interior lower quantile of a real-cast Zipf law is the least natural index whose normalized
power sum reaches the level. Equality at a cumulative jump belongs to the lower index. The
quantile is one through the first-atom mass `1 / ζ(s)`; its one-sided endpoint limits are one
and positive infinity.

The crossing characterization specializes `Measure.quantile_map_natCast_eq_iff`. The initial
constant segment follows the argument for Yule–Simon quantiles in
`TauCeti.Probability.Distributions.YuleSimon.Quantile`; the infinite endpoint uses
`Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, on zeta distributions.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {s u : ℝ}

/-- A natural number is the Zipf lower quantile exactly when it is the least crossing of the
explicit normalized power sum. Equality at a cumulative jump is included. -/
theorem quantile_map_cast_zipfMeasure_eq_iff (hs : 1 < s) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {n : ℕ | u ≤ ∑ j ∈ Finset.Iic n,
        (j : ℝ) ^ (-s) / (riemannZeta s).re} k := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  rw [Measure.quantile_map_natCast_eq_iff _ hu]
  simp only [zipfMeasure_real_Iic hs]

/-- A positive Zipf quantile is characterized by its two adjacent cumulative power sums: the
preceding sum is strictly below the level and the next sum reaches it. -/
theorem quantile_map_cast_zipfMeasure_eq_succ_iff (hs : 1 < s) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)).quantile u = (k + 1 : ℕ) ↔
      (∑ j ∈ Finset.Iic k, (j : ℝ) ^ (-s) / (riemannZeta s).re) < u ∧
        u ≤ ∑ j ∈ Finset.Iic (k + 1), (j : ℝ) ^ (-s) / (riemannZeta s).re := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  rw [Measure.quantile_map_natCast_eq_succ_iff _ hu]
  simp only [zipfMeasure_real_Iic hs]

/-- The first constant segment of a Zipf quantile includes the full mass `1 / ζ(s)` at one. -/
@[simp]
theorem quantile_map_cast_zipfMeasure_eq_one_iff (hs : 1 < s) (hu : u ∈ Ioo 0 1) :
    ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)).quantile u = 1 ↔
      u ≤ 1 / (riemannZeta s).re := by
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs).ne'
  simpa [← Nat.range_succ_eq_Iic, Finset.sum_range_succ, hs0, hu.1] using
    (quantile_map_cast_zipfMeasure_eq_succ_iff hs hu 0)

/-- As the level tends to zero from above, Zipf quantiles tend to the lower support endpoint
one. This does not assert a value for the totalized quantile at zero. -/
theorem tendsto_quantile_map_cast_zipfMeasure_nhdsGT_zero (hs : 1 < s) :
    Tendsto (fun u ↦ (((zipfMeasure s).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 1) := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  have hmass : 0 < 1 / (riemannZeta s).re := by
    simpa only [zipfWeightReal_def, Nat.cast_one, Real.one_rpow] using
      (zipfWeightReal_pos_iff hs 1).2 Nat.one_ne_zero
  have hmass_le : 1 / (riemannZeta s).re ≤ 1 := by
    have h := measureReal_le_one (μ := zipfMeasure s) (s := {1})
    rw [zipfMeasure_real_singleton hs, zipfWeightReal_def] at h
    simpa only [Nat.cast_one, Real.one_rpow] using h
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hmass] with u hu
  have hq := (quantile_map_cast_zipfMeasure_eq_one_iff hs
    ⟨hu.1, hu.2.trans_le hmass_le⟩).2 hu.2.le
  simpa using congrArg (fun x : ℝ ↦ (x : EReal)) hq.symm

/-- As the level tends to one from below, Zipf quantiles tend to positive infinity, since
every finite cutoff leaves a positive upper tail. -/
theorem tendsto_quantile_map_cast_zipfMeasure_nhdsLT_one (hs : 1 < s) :
    Tendsto (fun u ↦ (((zipfMeasure s).map (Nat.cast : ℕ → ℝ)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  exact Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _
    (cdf_map_cast_zipfMeasure_lt_one hs)

end TauCeti.Probability
