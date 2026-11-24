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
Laplacian recovers the measure, counting eigenvalues with algebraic multiplicity. This is the
distributional step in Tao's *Topics in Random Matrix Theory*, §2.8.3.
For sequences of random matrices, the potential continuity theorem converts pointwise
potential limits into weak spectral limits almost surely or in probability.

The replacement principle compares two sequences of random matrices: if their eigenvalue potentials
become asymptotically equal at almost every point, then the difference of their empirical
eigenvalue measures tends to zero vaguely, almost surely or in probability, and a weak limit of one
sequence is a weak limit of the other. This is the replacement principle of Tao and Vu, with
eigenvalue potentials in place of normalized log-determinants; their bound on the normalized
Frobenius norms is not needed for these conclusions.

## References

* T. Tao, *Topics in Random Matrix Theory*, §2.8.
* T. Tao, V. Vu, *Random matrices: universality of ESDs and the circular law*, with an appendix
  by M. Krishnapur, Ann. Probab. 38 (2010); arXiv:0807.4898, Theorem 2.1.
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

variable {ιs κs : ℕ → Type*} [∀ n, Fintype (ιs n)] [∀ n, DecidableEq (ιs n)]
  [∀ n, Nonempty (ιs n)] [∀ n, Fintype (κs n)] [∀ n, DecidableEq (κs n)]
  [∀ n, Nonempty (κs n)] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {A : ∀ n, Ω → Matrix (ιs n) (ιs n) ℂ} {B : ∀ n, Ω → Matrix (κs n) (κs n) ℂ}
  {μ : ProbabilityMeasure ℂ}

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

/-- **Replacement principle for random matrices, almost-sure form.** If, at almost every point,
the logarithmic potentials of the empirical eigenvalue measures of `A n` and `B n` almost surely
become asymptotically equal, then almost surely the integrals of every continuous compactly
supported function against these eigenvalue measures become asymptotically equal. -/
theorem ae_tendsto_integral_eigenvalueMeasure_sub_of_ae_ae_tendsto_logarithmicPotential_sub
    [SFinite P] (hA : ∀ n, AEMeasurable (A n) P) (hB : ∀ n, AEMeasurable (B n) P)
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ ((A n ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z -
        ((B n ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n ↦ ∫ z, f z ∂((A n ω).eigenvalueMeasure : Measure ℂ) -
        ∫ z, f z ∂((B n ω).eigenvalueMeasure : Measure ℂ)) atTop (𝓝 0) :=
  ProbabilityMeasure.ae_tendsto_integral_sub_integral_of_ae_ae_tendsto_logarithmicPotential_sub
    (fun n ↦ measurable_eigenvalueMeasure.comp_aemeasurable (hA n))
    (fun n ↦ measurable_eigenvalueMeasure.comp_aemeasurable (hB n))
    (ae_of_all _ fun ω n ↦ (A n ω).integrable_eigenvalueMeasure _)
    (ae_of_all _ fun ω n ↦ (B n ω).integrable_eigenvalueMeasure _) h

/-- **Replacement principle for random matrices with a limit.** If almost surely the empirical
eigenvalue measures of `B n` converge weakly to `μ`, and at almost every point the logarithmic
potentials of the eigenvalue measures of `A n` and `B n` almost surely become asymptotically
equal, then almost surely the empirical eigenvalue measures of `A n` converge weakly to `μ`. -/
theorem ae_tendsto_eigenvalueMeasure_of_ae_tendsto_of_ae_ae_tendsto_logarithmicPotential_sub
    [SFinite P] (hA : ∀ n, AEMeasurable (A n) P) (hB : ∀ n, AEMeasurable (B n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (B n ω).eigenvalueMeasure) atTop (𝓝 μ))
    (h : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ ((A n ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z -
        ((B n ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (A n ω).eigenvalueMeasure) atTop (𝓝 μ) :=
  ProbabilityMeasure.ae_tendsto_of_ae_tendsto_of_ae_ae_tendsto_logarithmicPotential_sub
    (fun n ↦ measurable_eigenvalueMeasure.comp_aemeasurable (hA n))
    (fun n ↦ measurable_eigenvalueMeasure.comp_aemeasurable (hB n))
    (ae_of_all _ fun ω n ↦ (A n ω).integrable_eigenvalueMeasure _)
    (ae_of_all _ fun ω n ↦ (B n ω).integrable_eigenvalueMeasure _) hlim h

-- The measure-level theorem's name does not fit on one line with its namespace prefix.
open ProbabilityMeasure in
/-- **Replacement principle for random matrices, in-probability form.** If, at almost every
point, the difference of the logarithmic potentials of the empirical eigenvalue measures of `A n`
and `B n` converges to zero in probability, then for every continuous compactly supported `f` the
difference of the integrals of `f` against these eigenvalue measures converges to zero in
probability. -/
theorem
    tendstoInMeasure_integral_eigenvalueMeasure_sub_of_ae_tendstoInMeasure_logarithmicPotential_sub
    [IsFiniteMeasure P] (hA : ∀ n, AEMeasurable (A n) P) (hB : ∀ n, AEMeasurable (B n) P)
    (h : ∀ᵐ z ∂volume, TendstoInMeasure P
      (fun n ω ↦ ((A n ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z -
        ((B n ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z) atTop 0)
    {f : ℂ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoInMeasure P (fun n ω ↦ ∫ z, f z ∂((A n ω).eigenvalueMeasure : Measure ℂ) -
      ∫ z, f z ∂((B n ω).eigenvalueMeasure : Measure ℂ)) atTop 0 :=
  tendstoInMeasure_integral_sub_integral_of_ae_tendstoInMeasure_logarithmicPotential_sub
    (fun n ↦ measurable_eigenvalueMeasure.comp_aemeasurable (hA n))
    (fun n ↦ measurable_eigenvalueMeasure.comp_aemeasurable (hB n))
    (ae_of_all _ fun ω n ↦ (A n ω).integrable_eigenvalueMeasure _)
    (ae_of_all _ fun ω n ↦ (B n ω).integrable_eigenvalueMeasure _) h hf hc

end Matrix
