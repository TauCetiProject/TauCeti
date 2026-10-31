/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Zipf.Basic
public import TauCeti.Probability.Cdf

/-!
# Cumulative probabilities of Zipf laws

The native cumulative mass of a Zipf law is the partial sum of its normalized power weights.
The cdf of the real cast vanishes below one and uses the natural floor at nonnegative cutoffs.
Every finite cutoff leaves positive mass above it, so the cdf is always strictly less than one.
These formulas give the cumulative crossings used to characterize discrete quantiles.

The cumulative-sum interface follows
`TauCeti.Probability.Distributions.BetaBinomial.Cdf` and the natural-cast bridge in
`TauCeti.Probability.Cdf`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, on zeta distributions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {s x : ℝ}

/-- A Zipf cumulative mass is the partial sum of the normalized power weights. The term at
zero vanishes for every valid exponent. -/
theorem zipfMeasure_real_Iic (hs : 1 < s) (k : ℕ) :
    (zipfMeasure s).real (Iic k) =
      ∑ j ∈ Finset.Iic k, (j : ℝ) ^ (-s) / (riemannZeta s).re := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  simp_rw [← zipfWeightReal_def, ← zipfMeasure_real_singleton hs]
  simp

/-- At a nonnegative cutoff, the real-cast Zipf cdf sums the power weights through the natural
floor. -/
theorem cdf_map_cast_zipfMeasure (hs : 1 < s) (hx : 0 ≤ x) :
    cdf ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) x =
      ∑ j ∈ Finset.Iic ⌊x⌋₊, (j : ℝ) ^ (-s) / (riemannZeta s).re := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  rw [Measure.cdf_map_natCast _ hx, zipfMeasure_real_Iic hs]

/-- The real-cast Zipf cdf vanishes below the first positive integer. In particular, negative
cutoffs are handled before taking the natural floor. -/
theorem cdf_map_cast_zipfMeasure_of_lt_one (hs : 1 < s) (hx : x < 1) :
    cdf ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  by_cases hx0 : x < 0
  · exact Measure.cdf_map_natCast_of_neg _ hx0
  · rw [Measure.cdf_map_natCast _ (le_of_not_gt hx0), Nat.floor_eq_zero.mpr hx]
    have hzero : (Iic 0 : Set ℕ) = {0} := Iic_bot
    simp [hzero, measureReal_def]

/-- Every real-cast Zipf cdf is strictly below one at every finite cutoff, because positive
integers above that cutoff have positive mass. -/
theorem cdf_map_cast_zipfMeasure_lt_one (hs : 1 < s) (x : ℝ) :
    cdf ((zipfMeasure s).map (Nat.cast : ℕ → ℝ)) x < 1 := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  by_cases hx : x < 0
  · rw [Measure.cdf_map_natCast_of_neg _ hx]
    exact zero_lt_one
  rw [Measure.cdf_map_natCast _ (le_of_not_gt hx)]
  have hmass : 0 < (zipfMeasure s).real {⌊x⌋₊ + 1} := by
    rw [zipfMeasure_real_singleton hs]
    exact (zipfWeightReal_pos_iff hs _).2 (Nat.succ_ne_zero _)
  have hle : (zipfMeasure s).real {⌊x⌋₊ + 1} ≤
      (zipfMeasure s).real (Iic ⌊x⌋₊)ᶜ :=
    measureReal_mono (by simp)
  have hcompl := probReal_add_probReal_compl (μ := zipfMeasure s)
    (s := Iic ⌊x⌋₊) (.of_discrete)
  linarith

end TauCeti.Probability
