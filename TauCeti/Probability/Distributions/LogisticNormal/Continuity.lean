/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.LogisticNormal.Basic

/-!
# Weak continuity of simplex logistic-normal laws

For a fixed reference category, simplex logistic-normal laws depend jointly weakly continuously
on their Gaussian mean and positive semidefinite covariance. This includes singular covariances,
the zero-covariance point mass at the logistic chart of the mean, and the one-category law.

The statements use `ProbabilityMeasure` and the inherited topology on the positive semidefinite
cone. They follow from `TauCeti.Probability.continuous_multivariateGaussian` and Mathlib's
`ProbabilityMeasure.continuous_map`, applied to `logisticNormalChart`.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

open Filter MeasureTheory Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a fixed reference category, simplex logistic-normal laws depend jointly weakly
continuously on the Gaussian mean and positive semidefinite covariance, including singular
and zero covariances. -/
theorem continuous_logisticNormalMeasure (r : ι) :
    Continuous (fun p : EuclideanSpace ℝ {i // i ≠ r} ×
        {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ // S.PosSemidef} ↦
      (logisticNormalMeasure r p.1 p.2.1).toProbabilityMeasure) := by
  have h := (ProbabilityMeasure.continuous_map (continuous_logisticNormalChart r)).comp
    continuous_multivariateGaussian
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map,
    Measure.coe_toProbabilityMeasure]
  exact (logisticNormalMeasure_def r p.1 p.2.1).symm

/-- As the positive semidefinite Gaussian covariance tends to zero, the simplex logistic-normal
law converges weakly to the point mass at the logistic chart of its mean. -/
theorem tendsto_logisticNormalMeasure_nhds_zero_dirac (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) :
    Tendsto (fun S : {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ // S.PosSemidef} ↦
      (logisticNormalMeasure r m S.1).toProbabilityMeasure)
      (𝓝 ⟨0, Matrix.PosSemidef.zero⟩)
      (𝓝 (Measure.dirac (logisticNormalChart r m)).toProbabilityMeasure) := by
  have h := ((continuous_logisticNormalMeasure r).comp
    (continuous_const.prodMk continuous_id : Continuous fun
      S : {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ // S.PosSemidef} ↦ (m, S))).tendsto
        ⟨0, Matrix.PosSemidef.zero⟩
  simpa only [Function.comp_def, logisticNormalMeasure_zero] using h

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous Gaussian means and positive semidefinite covariances give a weakly continuous
simplex logistic-normal family with a fixed reference category. -/
@[fun_prop]
theorem logisticNormalMeasure {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι}
    {m : T → EuclideanSpace ℝ {i // i ≠ r}}
    {S : T → Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hm : Continuous m) (hS : Continuous S) (hPSD : ∀ t, (S t).PosSemidef) :
    Continuous (fun t ↦
      (TauCeti.Probability.logisticNormalMeasure r (m t) (S t)).toProbabilityMeasure) := by
  simpa only [Function.comp_def] using
    (TauCeti.Probability.continuous_logisticNormalMeasure r).comp
      (hm.prodMk (hS.subtype_mk hPSD))

end Continuous
