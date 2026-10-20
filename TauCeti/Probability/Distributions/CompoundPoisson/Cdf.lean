/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic
public import TauCeti.Probability.Cdf
import TauCeti.Probability.Distributions.Dirac

/-!
# Compound Poisson cumulative probabilities and masses

The cdf of a real compound Poisson law is the Poisson-weighted series of the cdfs of its
convolution powers. The empty sum contributes an atom of mass at least `exp (-r)` at zero;
nonempty sums may contribute further mass there. No density or absence of other atoms is assumed.

The same series computes native singleton masses and cumulative probabilities for natural and
integer jumps. Real casts use natural floor only at nonnegative cutoffs, and integer floor at
arbitrary cutoffs. The `HasSum` statements certify convergence of these nonnegative series.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, ch. XII, §2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat

namespace TauCeti.Probability

/-- The Poisson-weighted convolution-power cdf series converges to the compound Poisson cdf,
including the zeroth convolution power, which is a point mass at zero. -/
theorem hasSum_cdf_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    HasSum (fun n : ℕ => (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
      cdf (μ.convolutionPower n) x) (cdf (compoundPoissonMeasure r μ) x) := by
  simpa only [cdf_eq_real] using
    hasSum_compoundPoissonMeasure_real_apply r μ (s := Iic x) measurableSet_Iic

/-- The compound Poisson cdf, with the empty-sum atom separated from the nonempty sums. -/
theorem cdf_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    cdf (compoundPoissonMeasure r μ) x = (if 0 ≤ x then exp (-(r : ℝ)) else 0) +
      ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1) !) *
        cdf (μ.convolutionPower (n + 1)) x := by
  rw [← (hasSum_cdf_compoundPoissonMeasure r μ x).tsum_eq,
    (hasSum_cdf_compoundPoissonMeasure r μ x).summable.tsum_eq_zero_add]
  simp [cdf_dirac, mul_ite]

/-- The cdf of the real cast of a natural-valued compound Poisson law. The negative branch is
taken before applying natural floor. -/
theorem cdf_map_natCast_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure ℕ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    cdf ((compoundPoissonMeasure r μ).map (Nat.cast : ℕ → ℝ)) x =
      if 0 ≤ x then
        ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
          (μ.convolutionPower n).real (Iic ⌊x⌋₊)
      else 0 := by
  split_ifs with hx
  · rw [Measure.cdf_map_natCast _ hx]
    exact (hasSum_compoundPoissonMeasure_real_apply r μ measurableSet_Iic).tsum_eq.symm
  · exact Measure.cdf_map_natCast_of_neg _ (lt_of_not_ge hx)

/-- The cdf of the real cast of an integer-valued compound Poisson law, using integer floor
also for negative cutoffs. -/
theorem cdf_map_intCast_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure ℤ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    cdf ((compoundPoissonMeasure r μ).map (Int.cast : ℤ → ℝ)) x =
      ∑' n : ℕ, (exp (-(r : ℝ)) * (r : ℝ) ^ n / n !) *
        (μ.convolutionPower n).real (Iic ⌊x⌋) := by
  rw [Measure.cdf_map_intCast]
  exact (hasSum_compoundPoissonMeasure_real_apply r μ measurableSet_Iic).tsum_eq.symm

end TauCeti.Probability
