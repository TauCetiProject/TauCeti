/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Basic
public import TauCeti.Analysis.SpecialFunctions.Exp.Negative

/-!
# Extended nonnegative Laplace transform of a Poisson count

The negative exponential convention at infinity makes the transform valid for every
extended nonnegative parameter, including the void-probability parameter `∞`.
This is the scalar input to the Laplace functional of a Poisson random measure.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- The extended nonnegative Laplace transform of a Poisson count, including parameter `∞`. -/
theorem lintegral_expNeg_mul_natCast_poissonMeasure (r : ℝ≥0) (c : ℝ≥0∞) :
    ∫⁻ k : ℕ, (ENNReal.expNeg (c * k) : ℝ≥0∞) ∂poissonMeasure r =
      (ENNReal.expNeg ((r : ℝ≥0∞) * (1 - (ENNReal.expNeg c : ℝ≥0∞))) : ℝ≥0∞) := by
  simp_rw [ENNReal.expNeg_mul_natCast]
  have hpow (k : ℕ) : ((ENNReal.expNeg c : ℝ≥0) ^ k : ℝ≥0∞) =
      ENNReal.ofReal ((ENNReal.expNeg c : ℝ) ^ k) := by simp
  simp_rw [ENNReal.coe_pow, hpow]
  rw [lintegral_ofReal_poissonMeasure (fun _ => by positivity) r
    (hasSum_pow_poissonMeasure r (ENNReal.expNeg c : ℝ))]
  have harg : (r : ℝ≥0∞) * (1 - (ENNReal.expNeg c : ℝ≥0∞)) =
      ((r * (1 - ENNReal.expNeg c) : ℝ≥0) : ℝ≥0∞) := by simp [ENNReal.coe_sub]
  rw [harg, ENNReal.expNeg_coe]
  congr 2
  push_cast [NNReal.coe_sub (ENNReal.expNeg_le_one c)]
  ring

end TauCeti.Probability
