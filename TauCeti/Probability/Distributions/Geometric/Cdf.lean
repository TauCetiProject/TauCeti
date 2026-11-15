/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Cdf
public import TauCeti.Probability.Distributions.Geometric.Basic

import TauCeti.Probability.Distributions.Dirac

/-!
# The geometric cumulative distribution function

This file computes the cumulative distribution function of the real-valued pushforward of
Mathlib's geometric law.  At a nonnegative point it is the native cumulative mass through the
natural floor; below the origin it vanishes by the generic
`MeasureTheory.Measure.cdf_map_natCast_of_neg`.

Mathlib totalizes success probability zero as a point mass at zero.  That boundary therefore has
the step-function cdf of a Dirac measure, rather than the formula for a positive success
probability.

## Main results

* `TauCeti.Probability.cdf_map_cast_geometricMeasure` computes the cdf for nonzero success
  probability at a nonnegative point;
* `TauCeti.Probability.cdf_map_cast_geometricMeasure_zero` gives the zero-parameter boundary.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley, 2005, Chapter 5.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The cdf of the real-valued geometric law at a nonnegative point is its geometric partial-sum
formula evaluated at the natural floor of that point. -/
theorem cdf_map_cast_geometricMeasure {p : unitInterval} (hp : p ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    cdf ((geometricMeasure p).map (Nat.cast : ℕ → ℝ)) x =
      1 - (1 - (p : ℝ)) ^ (⌊x⌋₊ + 1) := by
  rw [Measure.cdf_map_natCast _ hx]
  simpa only [Iic_def] using geometricMeasure_real_Iic hp ⌊x⌋₊

/-- At success probability zero, the real-valued geometric law has the step-function cdf of the
Dirac measure at zero. -/
@[simp]
theorem cdf_map_cast_geometricMeasure_zero (x : ℝ) :
    cdf ((geometricMeasure (0 : unitInterval)).map (Nat.cast : ℕ → ℝ)) x =
      if 0 ≤ x then 1 else 0 := by
  rw [geometricMeasure_zero, Measure.map_dirac, Nat.cast_zero, cdf_dirac]

end TauCeti.Probability
