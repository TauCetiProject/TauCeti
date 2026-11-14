/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Canonical pre-Brownian measure on product path space

Combining `ProbabilityTheory.BrownianReal.projectiveFamily` with Kolmogorov's extension theorem
`MeasureTheory.projectiveLimit` yields `TauCeti.Probability.gaussianLimit`, the canonical
probability measure on `(ℝ≥0 → ℝ)` (with the product `σ`-algebra) under which coordinate evaluation
satisfies `ProbabilityTheory.IsPreBrownianReal`.

## Main declarations

* `TauCeti.Probability.gaussianLimit`: Kolmogorov projective limit of
  `BrownianReal.projectiveFamily`.
* `TauCeti.Probability.isProjectiveLimit_gaussianLimit`: projective-limit property of
  `gaussianLimit`.
* `TauCeti.Probability.isPreBrownianReal_eval_gaussianLimit`: coordinate evaluation `(t, ω) ↦ ω t`
  is a scalar pre-Brownian motion under `gaussianLimit`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory ProbabilityTheory.BrownianReal
open scoped NNReal

namespace TauCeti.Probability

/-- The canonical probability measure on `ℝ≥0 → ℝ` obtained as the Kolmogorov projective limit of
`ProbabilityTheory.BrownianReal.projectiveFamily`. -/
def gaussianLimit : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit projectiveFamily isProjectiveMeasureFamily_projectiveFamily

instance isProbabilityMeasure_gaussianLimit : IsProbabilityMeasure gaussianLimit := by
  unfold gaussianLimit; infer_instance

/-- `gaussianLimit` is the projective limit of `BrownianReal.projectiveFamily`. -/
theorem isProjectiveLimit_gaussianLimit : IsProjectiveLimit gaussianLimit projectiveFamily :=
  isProjectiveLimit_projectiveLimit isProjectiveMeasureFamily_projectiveFamily

/-- Under `gaussianLimit`, coordinate evaluation `(t, ω) ↦ ω t` is a scalar pre-Brownian motion. -/
theorem isPreBrownianReal_eval_gaussianLimit :
    IsPreBrownianReal (fun t (ω : ℝ≥0 → ℝ) ↦ ω t) gaussianLimit :=
  ⟨fun I ↦ ⟨(Finset.measurable_restrict I).aemeasurable, isProjectiveLimit_gaussianLimit I⟩⟩

end TauCeti.Probability
