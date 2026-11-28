/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Mean and variance of real Gaussian random variables

This file transports the mean and variance formulas for `gaussianReal m v` to random variables
with that law.

## Main results

* `ProbabilityTheory.HasLaw.integral_gaussianReal` identifies the expectation with `m`.
* `ProbabilityTheory.HasLaw.variance_gaussianReal` identifies the variance with `v`.
-/

public section

namespace ProbabilityTheory.HasLaw

open MeasureTheory
open scoped ENNReal Nat NNReal Real

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0}

/-- The expectation of a real Gaussian random variable is its mean parameter. -/
theorem integral_gaussianReal (hX : HasLaw X (gaussianReal m v) P) :
    ∫ ω, X ω ∂P = m := by
  rw [hX.integral_eq, integral_id_gaussianReal]

/-- The variance of a real Gaussian random variable is its variance parameter. -/
theorem variance_gaussianReal (hX : HasLaw X (gaussianReal m v) P) :
    variance X P = v := by
  rw [hX.variance_eq, variance_id_gaussianReal]

end ProbabilityTheory.HasLaw
