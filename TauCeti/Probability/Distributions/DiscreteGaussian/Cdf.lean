/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.DiscreteGaussian.Basic
public import TauCeti.Probability.Cdf
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Cumulative probabilities of the discrete Gaussian

The cumulative mass of an integer Gaussian is the absolutely convergent series of its
normalized Gaussian weights through the integer cutoff. The CDF of its real cast uses the
integer floor, including at negative arguments. Every finite cutoff has cumulative mass
strictly between zero and one, since every integer has positive mass. These bounds provide
the infinite endpoints for the law's quantiles.

The series formula uses `Measure.tsum_indicator_apply_singleton` to sum the native masses.

## References

* C. L. Canonne, G. Kamath and T. Steinke, *The Discrete Gaussian for Differential Privacy*,
  2020, arXiv:2004.00010.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The cumulative series of normalized Gaussian masses converges to the native cumulative
mass. Its terms are nonnegative, so the convergence is also absolute. -/
theorem hasSum_discreteGaussianMeasure_real_Iic (c : ℝ) {s : ℝ} (hs : 0 < s) (k : ℤ) :
    HasSum (fun n : ℤ ↦ if n ≤ k then
      exp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) / gaussianLatticeSum c s else 0)
      ((discreteGaussianMeasure c s).real (Iic k)) := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  have hmass := (discreteGaussianMeasure c s).tsum_indicator_apply_singleton (Iic k)
    measurableSet_Iic
  have hsum := (ENNReal.summable.hasSum_iff.mpr hmass).toReal (measure_ne_top _ _)
  rw [← measureReal_def] at hsum
  convert hsum using 1
  funext n
  simp only [indicator_apply, mem_Iic]
  split_ifs <;> simp [← measureReal_def, discreteGaussianMeasure_real_singleton c hs,
    discreteGaussianWeightReal_def]

/-- The cumulative mass of a discrete Gaussian is its convergent Gaussian mass series. -/
theorem discreteGaussianMeasure_real_Iic (c : ℝ) {s : ℝ} (hs : 0 < s) (k : ℤ) :
    (discreteGaussianMeasure c s).real (Iic k) =
      ∑' n : ℤ, if n ≤ k then
        exp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) / gaussianLatticeSum c s else 0 :=
  (hasSum_discreteGaussianMeasure_real_Iic c hs k).tsum_eq.symm

/-- The real-cast CDF sums the Gaussian masses through the integer floor of its argument. -/
theorem cdf_map_intCast_discreteGaussianMeasure (c : ℝ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    cdf ((discreteGaussianMeasure c s).map (Int.cast : ℤ → ℝ)) x =
      ∑' n : ℤ, if n ≤ ⌊x⌋ then
        exp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) / gaussianLatticeSum c s else 0 := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  rw [Measure.cdf_map_intCast, discreteGaussianMeasure_real_Iic c hs]

/-- Every integer cutoff has positive cumulative mass at positive width. -/
theorem discreteGaussianMeasure_real_Iic_pos (c : ℝ) {s : ℝ} (hs : 0 < s) (k : ℤ) :
    0 < (discreteGaussianMeasure c s).real (Iic k) := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  have hmass : 0 < (discreteGaussianMeasure c s).real {k} := by
    rw [discreteGaussianMeasure_real_singleton c hs]
    exact discreteGaussianWeightReal_pos c hs.ne' k
  exact hmass.trans_le (measureReal_mono (singleton_subset_iff.mpr (by simp)))

/-- Every integer cutoff leaves positive mass above it at positive width. -/
theorem discreteGaussianMeasure_real_Iic_lt_one (c : ℝ) {s : ℝ} (hs : 0 < s) (k : ℤ) :
    (discreteGaussianMeasure c s).real (Iic k) < 1 := by
  have := isProbabilityMeasure_discreteGaussianMeasure c hs
  have hmass : 0 < (discreteGaussianMeasure c s).real {k + 1} := by
    rw [discreteGaussianMeasure_real_singleton c hs]
    exact discreteGaussianWeightReal_pos c hs.ne' _
  have htail : 0 < (discreteGaussianMeasure c s).real (Iic k)ᶜ :=
    hmass.trans_le (measureReal_mono (singleton_subset_iff.mpr (by simp)))
  rw [measureReal_compl measurableSet_Iic, probReal_univ] at htail
  linarith

end TauCeti.Probability
