/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.MultivariateLogNormal.Basic

/-!
# Weak continuity of multivariate log-normal laws

Multivariate log-normal laws depend jointly weakly continuously on their log-mean and positive
semidefinite log-covariance. The covariance may be singular or zero, and the coordinate type may
be empty. In particular, collapsing log-covariances give the point mass at the coordinatewise
exponential of the log-mean.

The statements use `ProbabilityMeasure` and the inherited topology on the positive semidefinite
cone. They follow from `TauCeti.Probability.continuous_multivariateGaussian` and Mathlib's
`ProbabilityMeasure.continuous_map`, applied to the fixed coordinatewise exponential map.
-/

public section

open Filter MeasureTheory Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multivariate log-normal laws depend jointly weakly continuously on log-mean and positive
semidefinite log-covariance, including singular and zero covariances. -/
theorem continuous_multivariateLogNormalMeasure :
    Continuous (fun p : EuclideanSpace ℝ ι × {S : Matrix ι ι ℝ // S.PosSemidef} ↦
      (multivariateLogNormalMeasure p.1 p.2.1).toProbabilityMeasure) := by
  have hexp : Continuous (fun x : EuclideanSpace ℝ ι ↦
      WithLp.toLp 2 (fun i ↦ Real.exp (x i))) := by
    fun_prop
  have h := (ProbabilityMeasure.continuous_map hexp).comp continuous_multivariateGaussian
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map,
    Measure.coe_toProbabilityMeasure]
  exact (multivariateLogNormalMeasure_def p.1 p.2.1).symm

/-- As the positive semidefinite log-covariance tends to zero, the multivariate log-normal law
converges weakly to the point mass at the coordinatewise exponential of its log-mean. -/
theorem tendsto_multivariateLogNormalMeasure_nhds_zero_dirac (m : EuclideanSpace ℝ ι) :
    Tendsto (fun S : {S : Matrix ι ι ℝ // S.PosSemidef} ↦
      (multivariateLogNormalMeasure m S.1).toProbabilityMeasure)
      (𝓝 ⟨0, Matrix.PosSemidef.zero⟩)
      (𝓝 (Measure.dirac (WithLp.toLp 2 (fun i ↦ Real.exp (m i)))).toProbabilityMeasure) := by
  have h := (continuous_multivariateLogNormalMeasure.comp
    (continuous_const.prodMk continuous_id : Continuous fun
      S : {S : Matrix ι ι ℝ // S.PosSemidef} ↦ (m, S))).tendsto
        ⟨0, Matrix.PosSemidef.zero⟩
  simpa only [Function.comp_def, multivariateLogNormalMeasure_zero] using h

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous log-means and positive semidefinite log-covariances give a weakly continuous
multivariate log-normal family, including at singular covariances. -/
@[fun_prop]
theorem multivariateLogNormalMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : T → EuclideanSpace ℝ ι} {S : T → Matrix ι ι ℝ}
    (hm : Continuous m) (hS : Continuous S) (hPSD : ∀ t, (S t).PosSemidef) :
    Continuous (fun t ↦
      (TauCeti.Probability.multivariateLogNormalMeasure (m t) (S t)).toProbabilityMeasure) := by
  simpa only [Function.comp_def] using
    TauCeti.Probability.continuous_multivariateLogNormalMeasure.comp
      (hm.prodMk (hS.subtype_mk hPSD))

end Continuous
