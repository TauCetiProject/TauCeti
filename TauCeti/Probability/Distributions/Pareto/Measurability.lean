/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.Measurability
public import Mathlib.Probability.Distributions.Pareto
/-! # Parameter measurability for the Pareto distribution -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability
/-- The Pareto density is measurable jointly in its threshold, its shape and the point. -/
@[fun_prop] theorem measurable_uncurry_paretoPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ => paretoPDF q.1.1 q.1.2 q.2 := by
  simp only [paretoPDF, paretoPDFReal]
  exact (Measurable.ite (measurableSet_le measurable_fst.fst measurable_snd)
    (by fun_prop) measurable_const).ennreal_ofReal
/-- **The Pareto family is measurable in its parameters.** -/
@[fun_prop] theorem measurable_paretoMeasure :
    Measurable fun p : ℝ × ℝ => paretoMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_paretoPDF
end TauCeti.Probability
