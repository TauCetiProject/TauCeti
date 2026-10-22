/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Levy.Basic
public import TauCeti.Analysis.SpecialFunctions.Erf
public import Mathlib.Probability.CDF
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma
import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.InverseGamma.Cdf

/-!
# Cumulative distribution function of the Lévy distribution

The Lévy law with location `m` and scale `c > 0` has cdf

`F(x) = erfc (√(c / (2 (x - m))))`

above its location and zero at or below it. This file derives it from the inverse-gamma cdf: at
shape `1 / 2`, the regularized lower incomplete Gamma function is the error function of the
square root, `Real.erf_eq_regularizedGamma_half_sq`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {m c : ℝ}

/-- **The cdf of a Lévy law** with positive scale is `erfc (√(c / (2 (x - m))))` above the
location `m` and zero at or below it. -/
@[simp]
theorem cdf_levyMeasure_eq (hc : 0 < c) (m x : ℝ) :
    cdf (levyMeasure m c) x = if x ≤ m then 0 else Real.erfc (√(c / (2 * (x - m)))) := by
  let _ := isProbabilityMeasure_inverseGammaMeasure one_half_pos (half_pos hc)
  have hmap : levyMeasure m c = (inverseGammaMeasure (1 / 2) (c / 2)).map (fun y ↦ m + 1 * y) := by
    simp_rw [one_mul]
    exact levyMeasure_def m c
  rw [hmap, cdf_map_affine_of_pos one_pos, div_one,
    cdf_inverseGammaMeasure_eq one_half_pos (half_pos hc)]
  by_cases hx : x ≤ m
  · rw [ite_eq_left (sub_nonpos.mpr hx), ite_eq_left hx]
  · have hxm : 0 < x - m := sub_pos.mpr (not_le.mp hx)
    rw [ite_eq_right (not_le.mpr hxm), ite_eq_right hx, Real.erfc_def,
      Real.erf_eq_regularizedGamma_half_sq (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_nonneg hc.le (mul_pos two_pos hxm).le), div_div]

end Probability

end TauCeti
