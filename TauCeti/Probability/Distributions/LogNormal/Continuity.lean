/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.LogNormal.Basic

/-!
# Weak continuity of log-normal laws

Log-normal laws depend jointly weakly continuously on their log-mean and nonnegative
log-variance. This includes convergence to the Dirac law at `exp m` as the log-variance tends
to zero.

The result follows by pushing the weakly continuous Gaussian family forward along the fixed
continuous exponential map. No moment convergence is asserted: positive exponential moments of
nondegenerate log-normal laws do not exist.
-/

public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Log-normal laws depend jointly weakly continuously on log-mean and nonnegative log-variance,
including the zero-variance Dirac boundary. -/
theorem continuous_logNormalMeasure :
    Continuous (fun p : ℝ × ℝ≥0 ↦ (logNormalMeasure p.1 p.2).toProbabilityMeasure) := by
  have h := (ProbabilityMeasure.continuous_map Real.continuous_exp).comp
    continuous_gaussianReal
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Function.comp_apply]
  rw [ProbabilityMeasure.toMeasure_map]
  exact (logNormalMeasure_map_exp p.1 p.2).symm

/-- As the log-variance tends to zero, the log-normal law converges weakly to the point mass at
`exp m`. -/
theorem tendsto_logNormalMeasure_nhds_zero_dirac (m : ℝ) :
    Tendsto (fun v : ℝ≥0 ↦ (logNormalMeasure m v).toProbabilityMeasure) (nhds 0)
      (nhds (Measure.dirac (Real.exp m)).toProbabilityMeasure) := by
  have h := (continuous_logNormalMeasure.comp
    (continuous_const.prodMk continuous_id : Continuous fun v : ℝ≥0 ↦ (m, v))).tendsto 0
  simpa only [Function.comp_def, logNormalMeasure_zero_var] using h

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous log-mean and nonnegative log-variance parameters give a weakly continuous
log-normal law, including at zero variance. -/
@[fun_prop]
theorem logNormalMeasure {m : T → ℝ} {v : T → ℝ≥0}
    (hm : Continuous m) (hv : Continuous v) :
    Continuous (fun t ↦
      (TauCeti.Probability.logNormalMeasure (m t) (v t)).toProbabilityMeasure) := by
  simpa only [Function.comp_def] using
    TauCeti.Probability.continuous_logNormalMeasure.comp (hm.prodMk hv)

end Continuous
