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

`Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily` constructs the consistent
finite-dimensional Gaussian distributions `ProbabilityTheory.BrownianReal.projectiveFamily` of
scalar Brownian motion, and `Mathlib.MeasureTheory.Constructions.KolmogorovExtension` provides the
Kolmogorov extension `MeasureTheory.projectiveLimit` on arbitrary products of Polish Borel spaces.
Combining the two yields `TauCeti.Probability.gaussianLimit`, the canonical probability
measure on `ℝ≥0 → ℝ` under which the coordinate evaluations form a scalar pre-Brownian motion
(`TauCeti.Probability.isPreBrownianReal_eval_gaussianLimit`).

Note that `ℝ≥0 → ℝ` carries the product `σ`-algebra rather than a continuous-path space: this
measure witnesses `ProbabilityTheory.IsPreBrownianReal` unconditionally without continuous-path
selection.

## Main declarations

* `TauCeti.Probability.gaussianLimit`: Kolmogorov projective limit of
  `ProbabilityTheory.BrownianReal.projectiveFamily` on `ℝ≥0 → ℝ`.
* `TauCeti.Probability.isProjectiveLimit_gaussianLimit`: `gaussianLimit` is the projective limit of
  `BrownianReal.projectiveFamily`.
* `TauCeti.Probability.isPreBrownianReal_eval_gaussianLimit`: coordinate evaluation `(t, ω) ↦ ω t`
  satisfies `ProbabilityTheory.IsPreBrownianReal` under `gaussianLimit`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory ProbabilityTheory.BrownianReal
open scoped NNReal

namespace TauCeti.Probability

/-- The canonical probability measure on `ℝ≥0 → ℝ` obtained as the Kolmogorov projective limit of
the Brownian finite-dimensional Gaussian distributions
`ProbabilityTheory.BrownianReal.projectiveFamily`. -/
def gaussianLimit : Measure (ℝ≥0 → ℝ) :=
  projectiveLimit projectiveFamily isProjectiveMeasureFamily_projectiveFamily

instance isProbabilityMeasure_gaussianLimit : IsProbabilityMeasure gaussianLimit := by
  unfold gaussianLimit
  infer_instance

/-- `gaussianLimit` is the projective limit of `BrownianReal.projectiveFamily`. -/
theorem isProjectiveLimit_gaussianLimit :
    IsProjectiveLimit gaussianLimit projectiveFamily :=
  isProjectiveLimit_projectiveLimit isProjectiveMeasureFamily_projectiveFamily

/-- Under `gaussianLimit`, the coordinate process `(t, ω) ↦ ω t` on `ℝ≥0 → ℝ` is a scalar
pre-Brownian motion. -/
theorem isPreBrownianReal_eval_gaussianLimit :
    IsPreBrownianReal (fun t (ω : ℝ≥0 → ℝ) ↦ ω t) gaussianLimit where
  hasLaw I := ⟨(Finset.measurable_restrict I).aemeasurable, isProjectiveLimit_gaussianLimit I⟩

end TauCeti.Probability
