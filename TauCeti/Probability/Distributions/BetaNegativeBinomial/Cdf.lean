/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaNegativeBinomial.Basic
public import TauCeti.Probability.Cdf

/-!
# Cumulative probabilities of beta-negative-binomial laws

Cumulative masses are finite sums of the Gamma–Beta weights. The cdf of the real cast
vanishes below zero and uses the natural floor at nonnegative cutoffs. At positive
negative-binomial shape every finite cutoff leaves positive mass above it.

These formulas supply explicit cumulative crossings for quantiles. They use the existing
natural-cast cdf bridge in `TauCeti.Probability.Cdf`.

## Reference

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {r a b : ℝ}

/-- A beta-negative-binomial cumulative mass is the finite sum of its Gamma–Beta weights,
including the shape-zero Dirac boundary. -/
theorem betaNegativeBinomialMeasure_real_Iic (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (k : ℕ) :
    (betaNegativeBinomialMeasure r a b).real (Iic k) =
      ∑ j ∈ Finset.Iic k, betaNegativeBinomialWeightReal r a b j := by
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  simp_rw [← betaNegativeBinomialMeasure_real_singleton hr ha hb]
  simp

/-- At nonnegative cutoffs, the real-cast cdf sums the masses through the natural floor. -/
theorem cdf_map_cast_betaNegativeBinomialMeasure (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    {x : ℝ} (hx : 0 ≤ x) :
    cdf ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) x =
      ∑ j ∈ Finset.Iic ⌊x⌋₊, betaNegativeBinomialWeightReal r a b j := by
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  rw [Measure.cdf_map_natCast _ hx, betaNegativeBinomialMeasure_real_Iic hr ha hb]

/-- The real-cast cdf vanishes at negative cutoffs. -/
theorem cdf_map_cast_betaNegativeBinomialMeasure_of_neg (hr : 0 ≤ r) (ha : 0 < a)
    (hb : 0 < b) {x : ℝ} (hx : x < 0) :
    cdf ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr ha hb
  exact Measure.cdf_map_natCast_of_neg _ hx

/-- At positive shape, every finite natural cutoff leaves a strictly positive upper tail. -/
theorem betaNegativeBinomialMeasure_real_Iic_lt_one (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (k : ℕ) : (betaNegativeBinomialMeasure r a b).real (Iic k) < 1 := by
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr.le ha hb
  have htail : 0 < (betaNegativeBinomialMeasure r a b).real (Iic k)ᶜ := by
    apply lt_of_lt_of_le _ (measureReal_mono (s₁ := {k + 1}) (by simp))
    rw [betaNegativeBinomialMeasure_real_singleton hr.le ha hb]
    exact betaNegativeBinomialWeightReal_pos_of_pos hr ha hb _
  rw [probReal_compl_eq_one_sub measurableSet_Iic] at htail
  linarith

end TauCeti.Probability
