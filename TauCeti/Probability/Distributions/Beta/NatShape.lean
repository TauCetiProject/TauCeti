/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
import TauCeti.Probability.Distributions.Beta.Basic

/-!
# Beta laws with integer shape parameters

For natural numbers `k` and `m`, the beta law with shape parameters `k + 1` and `m + 1` has the
polynomial density `(k + m + 1)! / (k! m!) u ^ k (1 - u) ^ m` on the unit interval, since the
beta function at these arguments is `k! m! / (k + m + 1)!`. These are the laws of the order
statistics of a unit-uniform sample.

The result is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Inference/Families.lean`.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The beta law with integer shape parameters `k + 1` and `m + 1` has density
`(k + m + 1)! / (k! m!) u ^ k (1 - u) ^ m` with respect to Lebesgue measure on `[0, 1]`. -/
theorem betaMeasure_natCast_add_one_eq_withDensity (k m : ℕ) :
    betaMeasure ((k : ℝ) + 1) ((m : ℝ) + 1) =
      (volume.restrict (Icc (0 : ℝ) 1)).withDensity fun u ↦ ENNReal.ofReal
        ((k + m + 1).factorial / (k.factorial * m.factorial) * u ^ k * (1 - u) ^ m) := by
  rw [betaMeasure_eq_withDensity_restrict_Ioo, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hbeta : beta ((k : ℝ) + 1) ((m : ℝ) + 1) =
      (k.factorial * m.factorial) / (k + m + 1).factorial := by
    -- The sum of the shapes is `(k + m + 1) + 1`, the form `Real.Gamma_nat_eq_factorial` needs.
    have hsum : (k : ℝ) + 1 + ((m : ℝ) + 1) = ((k + m + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      ring
    rw [beta, hsum, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
      Real.Gamma_nat_eq_factorial]
  simp only [betaPDF, betaPDFReal, hu.1, hu.2, and_self, ite_true, hbeta, one_div, inv_div,
    add_sub_cancel_right, Real.rpow_natCast]

end TauCeti.Probability
