/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.LogitNormal.Basic

/-!
# Weak continuity of logit-normal laws

Logit-normal laws depend jointly weakly continuously on their Gaussian location and nonnegative
variance. This includes convergence to the Dirac law at `sigmoid m` as the variance tends to
zero.

The result follows by pushing the weakly continuous Gaussian family forward along the fixed
continuous sigmoid map. It covers the singular boundary without imposing a positive-variance
hypothesis.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Logit-normal laws depend jointly weakly continuously on Gaussian location and nonnegative
variance, including the zero-variance Dirac boundary. -/
theorem continuous_logitNormalMeasure :
    Continuous (fun p : ℝ × ℝ≥0 ↦ (logitNormalMeasure p.1 p.2).toProbabilityMeasure) := by
  have h := (ProbabilityMeasure.continuous_map continuous_sigmoid).comp
    continuous_gaussianReal
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Function.comp_apply]
  rw [ProbabilityMeasure.toMeasure_map]
  exact (logitNormalMeasure_def p.1 p.2).symm

/-- As the Gaussian variance tends to zero, the logit-normal law converges weakly to the point
mass at `sigmoid m`. -/
theorem tendsto_logitNormalMeasure_nhds_zero_dirac (m : ℝ) :
    Tendsto (fun v : ℝ≥0 ↦ (logitNormalMeasure m v).toProbabilityMeasure) (nhds 0)
      (nhds (Measure.dirac (Real.sigmoid m)).toProbabilityMeasure) := by
  have h := (continuous_logitNormalMeasure.comp
    (continuous_const.prodMk continuous_id : Continuous fun v : ℝ≥0 ↦ (m, v))).tendsto 0
  simpa only [Function.comp_def, logitNormalMeasure_zero_var] using h

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous Gaussian location and nonnegative variance parameters give a weakly continuous
logit-normal law, including at zero variance. -/
@[fun_prop]
theorem logitNormalMeasure {m : T → ℝ} {v : T → ℝ≥0}
    (hm : Continuous m) (hv : Continuous v) :
    Continuous (fun t ↦
      (TauCeti.Probability.logitNormalMeasure (m t) (v t)).toProbabilityMeasure) := by
  simpa only [Function.comp_def] using
    TauCeti.Probability.continuous_logitNormalMeasure.comp (hm.prodMk hv)

end Continuous
