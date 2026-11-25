/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import TauCeti.Probability.Distributions.Gaussian.Basic
import TauCeti.Probability.Distributions.Gaussian.Density

/-!
# The measure of the Gaussian weight

The measure `e^{−W} · volume` of the Gaussian weight `W = TauCeti.gaussianWeight E` is the standard
Gaussian measure `ProbabilityTheory.stdGaussian E`
(`TauCeti.withDensity_exp_neg_gaussianWeight`), so the Gaussian perimeter
`TauCeti.gaussianPerimeter` is the weighted perimeter of this measure. The density comes from
`TauCeti.Probability.stdGaussian_eq_withDensity_norm`. On the line, `e^{−W}` is the standard
normal density `φ` (`TauCeti.Real.exp_neg_gaussianWeight`).
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

/-- On the line, the Gaussian density `e^{−W}` is the standard normal density `φ`. -/
theorem Real.exp_neg_gaussianWeight (x : ℝ) :
    Real.exp (-gaussianWeight ℝ x) = ProbabilityTheory.gaussianPDFReal 0 1 x := by
  rw [exp_neg_gaussianWeight_of_norm_eq (Real.norm_eq_abs x), Probability.gaussianPDFReal_zero_one]
  simp [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi), neg_div]

end TauCeti
