/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Cauchy.Affine
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# Weak continuity of Cauchy laws

Cauchy laws depend jointly weakly continuously on their location and nonnegative scale.
This includes convergence to the Dirac law at the location when the scale tends to zero.
The statements use the weak topology on `ProbabilityMeasure ℝ`.

The family is realized by the continuous affine maps `x ↦ m + γ * x` of a single standard
Cauchy variable. `MeasureTheory.ProbabilityMeasure.continuous_map_of_forall_continuous`
applies even though a positive-scale Cauchy variable has no integrable first moment.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Cauchy laws depend jointly weakly continuously on location and nonnegative scale,
including the zero-scale Dirac boundary. -/
theorem continuous_cauchyMeasure :
    Continuous (fun p : ℝ × ℝ≥0 ↦ (cauchyMeasure p.1 p.2).toProbabilityMeasure) := by
  let P := (cauchyMeasure 0 1).toProbabilityMeasure
  have h := P.continuous_map_of_forall_continuous
    (f := fun p : ℝ × ℝ≥0 ↦ fun x ↦ p.1 + (p.2 : ℝ) * x)
    (fun _ ↦ by fun_prop) (fun _ ↦ by fun_prop)
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, P, Measure.coe_toProbabilityMeasure,
    cauchyMeasure_map_affine, mul_zero, add_zero, mul_one]
  congr 1
  exact NNReal.coe_injective (by simp)

/-- Shrinking the nonnegative Cauchy scale to zero gives the Dirac law at the location. -/
theorem tendsto_cauchyMeasure_nhds_zero_dirac (m : ℝ) :
    Tendsto (fun γ : ℝ≥0 ↦ (cauchyMeasure m γ).toProbabilityMeasure) (𝓝 0)
      (𝓝 (Measure.dirac m).toProbabilityMeasure) := by
  have h := (continuous_cauchyMeasure.comp
    (continuous_const.prodMk continuous_id : Continuous fun γ : ℝ≥0 ↦ (m, γ))).tendsto 0
  simpa only [Function.comp_def, cauchyMeasure_zero_scale] using h

end TauCeti.Probability
