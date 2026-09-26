/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Beta

import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.MeasureTheory.Measure.Measurability
/-!
# Parameter measurability for the Beta distribution

Joint measurability in the two shape parameters lets measurable parameter maps produce
measurable measure-valued Beta families, in particular kernels.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability
/-- `ProbabilityTheory.beta` is measurable in its two parameters.

It is `Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)`. No positivity is assumed;
measurability concerns the total function, including junk values at the poles of `Real.Gamma`. -/
@[fun_prop] theorem measurable_beta : Measurable fun p : ℝ × ℝ => beta p.1 p.2 := by
  unfold beta
  fun_prop
/-- The Beta density is measurable jointly in its two shapes and the point. -/
@[fun_prop] theorem measurable_uncurry_betaPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => betaPDF q.1.1 q.1.2 q.2 := by
  simp only [betaPDF, betaPDFReal]
  refine (Measurable.ite ?_ (by fun_prop) measurable_const).ennreal_ofReal
  exact (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_const)
/-- **The Beta family is measurable in its parameters.** -/
@[fun_prop] theorem measurable_betaMeasure : Measurable fun p : ℝ × ℝ => betaMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_betaPDF
end TauCeti.Probability
