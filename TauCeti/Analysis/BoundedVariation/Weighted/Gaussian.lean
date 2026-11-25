/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# The measure of the Gaussian weight

The measure `e^{−W} · volume` of the Gaussian weight `W = TauCeti.gaussianWeight E` is the standard
Gaussian measure `ProbabilityTheory.stdGaussian E`
(`TauCeti.withDensity_exp_neg_gaussianWeight`), so the Gaussian perimeter
`TauCeti.gaussianPerimeter` is the weighted perimeter of this measure. The density comes from
`TauCeti.Probability.stdGaussian_eq_withDensity_norm`.
-/

public section

open MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The measure of the Gaussian weight is the standard Gaussian measure. -/
theorem withDensity_exp_neg_gaussianWeight :
    (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-gaussianWeight E x))) =
      ProbabilityTheory.stdGaussian E := by
  rw [Probability.stdGaussian_eq_withDensity_norm]
  congr 1 with x
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add, gaussianWeight_def]
  congr 2
  ring

end TauCeti
