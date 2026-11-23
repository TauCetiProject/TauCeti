/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.MeasureTheory.Measure.LogarithmicPotential.InProbability

import TauCeti.Analysis.Matrix.SpectralMeasure.Continuous

/-!
# Logarithmic potentials of empirical eigenvalue measures

For a complex square matrix the empirical eigenvalue measure is a finite weighted sum of
Dirac masses. Its logarithmic potential is locally integrable and its distributional
Laplacian recovers the measure, counting eigenvalues with algebraic multiplicity.
This is the distributional step in Tao's *Topics in Random Matrix Theory*, §2.8.3.
For sequences of random matrices, the potential continuity theorem converts pointwise
potential limits into weak spectral limits almost surely or in probability.
-/

public section

namespace Matrix

open Filter InnerProductSpace MeasureTheory Topology
open scoped BoundedContinuousFunction ENNReal Laplacian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every normed-group-valued function is integrable against the empirical eigenvalue measure
of a matrix. -/
theorem integrable_eigenvalueMeasure (A : Matrix ι ι ℂ) {E : Type*} [NormedAddCommGroup E]
    (f : ℂ → E) :
    Integrable f (A.eigenvalueMeasure : Measure ℂ) := by
  rw [eigenvalueMeasure_def, ← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
    TauCeti.Probability.toFiniteMeasure_empiricalMeasureOfFintype,
    TauCeti.Probability.empiricalFiniteMeasure_toMeasure, integrable_finsetSum_measure]
  intro i _
  have : Nonempty A.charpoly.roots.ToType := ⟨i⟩
  apply (integrable_dirac (by simp)).smul_measure
  apply ENNReal.inv_ne_top.mpr
  exact_mod_cast (Fintype.card_ne_zero (α := A.charpoly.roots.ToType))

/-- The logarithmic potential of a complex matrix's eigenvalue measure is locally integrable
with respect to planar Lebesgue measure. -/
theorem locallyIntegrable_logarithmicPotential_eigenvalueMeasure (A : Matrix ι ι ℂ) :
    LocallyIntegrable (A.eigenvalueMeasure : Measure ℂ).logarithmicPotential :=
  Measure.locallyIntegrable_logarithmicPotential _ (A.integrable_eigenvalueMeasure _)

/-- The distributional Laplacian of a matrix's logarithmic potential is 2π times its
empirical eigenvalue measure. -/
theorem integral_laplacian_mul_logarithmicPotential_eigenvalueMeasure (A : Matrix ι ι ℂ)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∫ z, Δ f z * (A.eigenvalueMeasure : Measure ℂ).logarithmicPotential z =
      (2 * Real.pi) * ∫ z, f z ∂(A.eigenvalueMeasure : Measure ℂ) :=
  Measure.integral_laplacian_mul_logarithmicPotential _ (A.integrable_eigenvalueMeasure _) hf hc

variable {ιs : ℕ → Type*} [∀ n, Fintype (ιs n)] [∀ n, DecidableEq (ιs n)]
  [∀ n, Nonempty (ιs n)] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {A : ∀ n, Ω → Matrix (ιs n) (ιs n) ℂ} {μ : ProbabilityMeasure ℂ}

/-- Almost-sure convergence of empirical logarithmic potentials at almost every observation
point gives almost-sure weak convergence of the empirical eigenvalue measures. -/
theorem ae_tendsto_eigenvalueMeasure_of_ae_ae_tendsto_logarithmicPotential [SFinite P]
    (hA : ∀ n, AEMeasurable (A n) P)
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ ((A n ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z)
      atTop (𝓝 ((μ : Measure ℂ).logarithmicPotential z))) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (A n ω).eigenvalueMeasure) atTop (𝓝 μ) :=
  ProbabilityMeasure.ae_tendsto_of_ae_ae_tendsto_logarithmicPotential
    (fun n ↦ measurable_eigenvalueMeasure.comp_aemeasurable (hA n))
    (ae_of_all _ fun ω n ↦ (A n ω).integrable_eigenvalueMeasure _) hμ h

/-- Convergence in probability of empirical logarithmic potentials at almost every observation
point gives convergence in probability of each bounded continuous eigenvalue statistic. -/
theorem tendstoInMeasure_integral_eigenvalueMeasure_of_ae_tendstoInMeasure_logarithmicPotential
    [IsFiniteMeasure P] (hA : ∀ n, AEMeasurable (A n) P)
    (hμ : Integrable (fun w : ℂ ↦ Real.posLog ‖w‖) (μ : Measure ℂ))
    (h : ∀ᵐ z ∂volume, TendstoInMeasure P
      (fun n ω ↦ ((A n ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z)
      atTop (fun _ ↦ (μ : Measure ℂ).logarithmicPotential z))
    (f : ℂ →ᵇ ℝ) :
    TendstoInMeasure P (fun n ω ↦ ∫ z, f z ∂((A n ω).eigenvalueMeasure : Measure ℂ))
      atTop (fun _ ↦ ∫ z, f z ∂(μ : Measure ℂ)) :=
  ProbabilityMeasure.tendstoInMeasure_integral_of_ae_tendstoInMeasure_logarithmicPotential
    (fun n ↦ measurable_eigenvalueMeasure.comp_aemeasurable (hA n))
    (ae_of_all _ fun ω n ↦ (A n ω).integrable_eigenvalueMeasure _) hμ h f

end Matrix
