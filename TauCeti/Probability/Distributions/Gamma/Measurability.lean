/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Gamma

import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.MeasureTheory.Measure.Measurability
/-!
# Parameter measurability for the Gamma distribution

Joint measurability in shape and rate lets measurable parameter maps produce measurable
measure-valued Gamma families, in particular kernels.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace TauCeti.Probability
/-- The Gamma density is measurable jointly in its shape, its rate and the point. -/
@[fun_prop] theorem measurable_uncurry_gammaPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => gammaPDF q.1.1 q.1.2 q.2 := by
  simp only [gammaPDF, gammaPDFReal]
  exact (Measurable.ite (measurableSet_le measurable_const measurable_snd)
    (by fun_prop) measurable_const).ennreal_ofReal
/-- **The Gamma family is measurable in its parameters.** -/
@[fun_prop] theorem measurable_gammaMeasure :
    Measurable fun p : ℝ × ℝ => gammaMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_gammaPDF
end TauCeti.Probability
