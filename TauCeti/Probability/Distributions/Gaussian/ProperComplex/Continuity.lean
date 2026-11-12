/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Basic

/-!
# Weak continuity of proper complex Gaussian laws

Proper complex Gaussian laws depend jointly weakly continuously on their mean and Hermitian
positive semidefinite covariance. Singular and zero covariances, and empty coordinate types,
are included. In particular, collapsing covariances give the point mass at the mean.

The statements use `ProbabilityMeasure` and the inherited topology on the positive semidefinite
cone. Realification and its inverse are continuous, so weak continuity follows from
`TauCeti.Probability.continuous_multivariateGaussian` and Mathlib's
`ProbabilityMeasure.continuous_map`.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A, for the realification convention of the proper complex Gaussian.
-/

public section

open Filter MeasureTheory Topology
open scoped ComplexOrder

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Proper complex Gaussian laws depend jointly weakly continuously on the mean and positive
semidefinite covariance, including singular and zero covariances. -/
theorem continuous_properComplexGaussianMeasure :
    Continuous (fun p : (ι → ℂ) × {C : Matrix ι ι ℂ // C.PosSemidef} ↦
      (properComplexGaussianMeasure p.1 p.2.1).toProbabilityMeasure) := by
  have hmean : Continuous (fun p : (ι → ℂ) × {C : Matrix ι ι ℂ // C.PosSemidef} ↦
      complexToRealEuclidean ι p.1) :=
    (complexToRealEuclidean ι).continuous.comp continuous_fst
  have hcov : Continuous (fun p : (ι → ℂ) × {C : Matrix ι ι ℂ // C.PosSemidef} ↦
      complexGaussianRealCovariance p.2.1) :=
    continuous_complexGaussianRealCovariance.comp (continuous_subtype_val.comp continuous_snd)
  have h := (ProbabilityMeasure.continuous_map (complexToRealEuclidean ι).symm.continuous).comp
    (hmean.multivariateGaussian hcov fun p ↦
      (posSemidef_complexGaussianRealCovariance_iff p.2.1).2 p.2.2)
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map,
    Measure.coe_toProbabilityMeasure]
  exact (properComplexGaussianMeasure_def p.1 p.2.1).symm

/-- As the positive semidefinite covariance tends to zero, the proper complex Gaussian law
converges weakly to the point mass at its mean. -/
theorem tendsto_properComplexGaussianMeasure_nhds_zero_dirac (m : ι → ℂ) :
    Tendsto (fun C : {C : Matrix ι ι ℂ // C.PosSemidef} ↦
      (properComplexGaussianMeasure m C.1).toProbabilityMeasure)
      (𝓝 ⟨0, Matrix.PosSemidef.zero⟩) (𝓝 (Measure.dirac m).toProbabilityMeasure) := by
  have h := (continuous_properComplexGaussianMeasure.comp
    (continuous_const.prodMk continuous_id : Continuous fun
      C : {C : Matrix ι ι ℂ // C.PosSemidef} ↦ (m, C))).tendsto
        ⟨0, Matrix.PosSemidef.zero⟩
  simpa only [Function.comp_def, properComplexGaussianMeasure_zero] using h

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous means and positive semidefinite covariances give a weakly continuous proper
complex Gaussian family, including at singular covariances. -/
@[fun_prop]
theorem properComplexGaussianMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : T → ι → ℂ} {C : T → Matrix ι ι ℂ}
    (hm : Continuous m) (hC : Continuous C) (hPSD : ∀ t, (C t).PosSemidef) :
    Continuous (fun t ↦
      (TauCeti.Probability.properComplexGaussianMeasure (m t) (C t)).toProbabilityMeasure) := by
  simpa only [Function.comp_def] using
    TauCeti.Probability.continuous_properComplexGaussianMeasure.comp
      (hm.prodMk (hC.subtype_mk hPSD))

end Continuous
