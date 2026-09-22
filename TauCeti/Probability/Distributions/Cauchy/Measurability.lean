/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.Measurability
public import Mathlib.Probability.Distributions.Cauchy
/-! # Parameter measurability for the Cauchy distribution -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace TauCeti.Probability
/-- The Cauchy density is measurable jointly in its location, its scale and the point. -/
@[fun_prop] theorem measurable_uncurry_cauchyPDF :
    Measurable fun q : (ℝ × ℝ≥0) × ℝ => cauchyPDF q.1.1 q.1.2 q.2 := by
  simp only [cauchyPDF, cauchyPDFReal]
  fun_prop
/-- **The Cauchy family is measurable in its location and scale.**

The zero-scale fibre is a Dirac measure and is split off. -/
@[fun_prop] theorem measurable_cauchyMeasure :
    Measurable fun p : ℝ × ℝ≥0 => cauchyMeasure p.1 p.2 := by
  simp only [cauchyMeasure]
  refine Measurable.ite ?_ (Measure.measurable_dirac.comp measurable_fst)
    (measurable_withDensity (μ := volume) measurable_uncurry_cauchyPDF)
  exact measurable_snd (measurableSet_singleton 0)
end TauCeti.Probability
