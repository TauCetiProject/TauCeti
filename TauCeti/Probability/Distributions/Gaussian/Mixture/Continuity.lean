/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Mixture.Basic
public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.Mixture.Continuity

/-!
# Weak continuity of Gaussian mixtures

Finite scalar Gaussian mixtures depend jointly weakly continuously on their weights, means,
and nonnegative variances. Zero weights and zero variances are included: components may
vanish from the mixture or collapse to Dirac masses in the limit.

This follows from joint weak continuity of scalar Gaussian laws and preservation of weak
convergence by finite mixtures with converging simplex weights.
-/

public section

noncomputable section

open Convexity MeasureTheory
open scoped NNReal

namespace TauCeti.Probability

variable {I : Type*} [Fintype I]

/-- Gaussian mixtures vary jointly weakly continuously with their simplex weights, means,
and nonnegative variances, including vanishing weights and Dirac components. -/
theorem continuous_gaussianMixtureMeasure :
    Continuous (fun q : StdSimplex ℝ≥0 I × (I → ℝ) × (I → ℝ≥0) ↦
      (gaussianMixtureMeasure q.1 q.2.1 q.2.2).toProbabilityMeasure) := by
  have hK (i : I) : Continuous
      (fun q : StdSimplex ℝ≥0 I × (I → ℝ) × (I → ℝ≥0) ↦
        (ProbabilityTheory.gaussianReal (q.2.1 i) (q.2.2 i)).toProbabilityMeasure) := by
    fun_prop
  simpa only [Measure.coe_toProbabilityMeasure, gaussianMixtureMeasure_def,
    finiteMixtureMeasure_def] using
    continuous_finiteMixtureMeasure continuous_fst hK

end TauCeti.Probability
