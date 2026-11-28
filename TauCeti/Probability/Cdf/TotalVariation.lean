/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Distribution functions and the total variation distance

For real probability measures, the distribution functions differ at each point by at most half
the total variation distance `tvDist`, since `cdf μ t` is the mass of the ray `Iic t`.

## Main results

* `ProbabilityTheory.abs_cdf_sub_cdf_le_tvDist_div_two`: for probability measures,
  `|cdf μ t - cdf ν t| ≤ tvDist μ ν / 2` at every point `t`.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

/-- For probability measures, the discrepancy of the distribution functions at each point is at
most half the total variation distance. -/
theorem abs_cdf_sub_cdf_le_tvDist_div_two (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (t : ℝ) : |cdf μ t - cdf ν t| ≤ tvDist μ ν / 2 := by
  rw [cdf_eq_real, cdf_eq_real]
  exact abs_measureReal_sub_le_tvDist_div_two (by simp) (Iic t)

end ProbabilityTheory
