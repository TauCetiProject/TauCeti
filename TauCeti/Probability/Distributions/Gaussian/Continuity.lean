/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Weak continuity of Gaussian laws

Scalar Gaussian laws depend jointly weakly continuously on their mean and nonnegative variance.
Multivariate Gaussian laws depend jointly weakly continuously on their mean and positive
semidefinite covariance matrix. The covariance may be singular, zero, or indexed by an empty
type. In particular, these results allow limits in which the covariance loses rank.

The statements use `ProbabilityMeasure`, with its topology of weak convergence, and the
inherited topology on the positive semidefinite cone. No continuity across Mathlib's invalid
covariance fallback is asserted.

The proofs use Mathlib's Gaussian characteristic functions and Lévy convergence theorem
`ProbabilityMeasure.tendsto_of_tendsto_charFun`.
-/

public section

open Filter Matrix MeasureTheory ProbabilityTheory Topology
open scoped NNReal RealInnerProductSpace

namespace TauCeti.Probability

/-- Scalar Gaussian laws depend jointly weakly continuously on mean and variance, including
the zero-variance Dirac boundary. -/
theorem continuous_gaussianReal :
    Continuous (fun p : ℝ × ℝ≥0 ↦ (gaussianReal p.1 p.2).toProbabilityMeasure) := by
  apply continuous_iff_seqContinuous.2
  intro p a hp
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have h : Continuous (fun p : ℝ × ℝ≥0 ↦
      Complex.exp ((t : ℂ) * p.1 * Complex.I - (p.2 : ℂ) * (t : ℂ) ^ 2 / 2)) := by
    fun_prop
  simpa only [Function.comp_def, Measure.coe_toProbabilityMeasure, charFun_gaussianReal] using
    (h.tendsto a).comp hp

/-- Multivariate Gaussian laws depend jointly weakly continuously on mean and positive
semidefinite covariance, including every singular covariance and the zero covariance. -/
theorem continuous_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fun p : EuclideanSpace ℝ ι × {S : Matrix ι ι ℝ // S.PosSemidef} ↦
      (multivariateGaussian p.1 p.2.1).toProbabilityMeasure) := by
  -- Matrices carry the entrywise product topology.
  have : FirstCountableTopology
      (EuclideanSpace ℝ ι × {S : Matrix ι ι ℝ // S.PosSemidef}) :=
    inferInstanceAs (FirstCountableTopology
      (EuclideanSpace ℝ ι × {S : ι → ι → ℝ // (Matrix.of S).PosSemidef}))
  apply continuous_iff_seqContinuous.2
  intro p a hp
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hquad : Continuous (fun p :
      EuclideanSpace ℝ ι × {S : Matrix ι ι ℝ // S.PosSemidef} ↦
        (t ⬝ᵥ p.2.1 *ᵥ t : ℝ)) :=
    continuous_const.dotProduct
      ((continuous_subtype_val.comp continuous_snd).matrix_mulVec continuous_const)
  have hmean : Continuous (fun p :
      EuclideanSpace ℝ ι × {S : Matrix ι ι ℝ // S.PosSemidef} ↦ (⟪t, p.1⟫ : ℝ)) :=
    continuous_const.inner continuous_fst
  have h : Continuous (fun p : EuclideanSpace ℝ ι × {S : Matrix ι ι ℝ // S.PosSemidef} ↦
      Complex.exp ((⟪t, p.1⟫ : ℝ) * Complex.I -
        (t ⬝ᵥ p.2.1 *ᵥ t : ℝ) / 2)) := by
    exact Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp hmean).mul_const Complex.I).sub
        ((Complex.continuous_ofReal.comp hquad).div_const 2))
  simpa only [Function.comp_def, Measure.coe_toProbabilityMeasure,
    charFun_multivariateGaussian (p _).2.2, charFun_multivariateGaussian a.2.2] using
    (h.tendsto a).comp hp

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous scalar mean and nonnegative variance parameters give a weakly continuous
Gaussian law, including at zero variance. -/
@[fun_prop]
theorem gaussianReal {m : T → ℝ} {v : T → ℝ≥0}
    (hm : Continuous m) (hv : Continuous v) :
    Continuous (fun t ↦ (ProbabilityTheory.gaussianReal (m t) (v t)).toProbabilityMeasure) := by
  simpa only [Function.comp_def] using
    TauCeti.Probability.continuous_gaussianReal.comp (hm.prodMk hv)

/-- Continuous mean and covariance parameters give a weakly continuous multivariate Gaussian
law when every covariance is positive semidefinite. -/
@[fun_prop]
theorem multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : T → EuclideanSpace ℝ ι} {S : T → Matrix ι ι ℝ}
    (hm : Continuous m) (hS : Continuous S) (hPSD : ∀ t, (S t).PosSemidef) :
    Continuous (fun t ↦
      (ProbabilityTheory.multivariateGaussian (m t) (S t)).toProbabilityMeasure) := by
  simpa only [Function.comp_def] using
    TauCeti.Probability.continuous_multivariateGaussian.comp
      (hm.prodMk (hS.subtype_mk hPSD))

end Continuous
