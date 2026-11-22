/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.SampleCovariance.Measurable

import TauCeti.Analysis.Matrix.MeasurableSpace
import TauCeti.MeasureTheory.Integral.Bind
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cdf

/-!
# The expected sample covariance spectral measure

The expected empirical spectral measure of a random sample covariance is the mixture of the
samplewise spectral measures with respect to the data law. Its cumulative distribution
function is the mean of the random cumulative distribution function. Integrating against it
allows deterministic weak convergence to be studied before controlling random fluctuations.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

namespace TauCeti.Probability

variable {Ω p n 𝕜 : Type*} [MeasurableSpace Ω] [Fintype p] [DecidableEq p] [Nonempty p]
  [Fintype n] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  {P : Measure Ω} {X : Ω → Matrix p n 𝕜}

/-- Bounded continuous test integrals of a sample covariance spectrum are almost everywhere
strongly measurable in the data. -/
theorem aestronglyMeasurable_integral_spectralMeasure_sampleCovariance
    (hX : AEMeasurable X P) (f : ℝ →ᵇ ℝ) :
    AEStronglyMeasurable (fun ω ↦ ∫ x, f x ∂((X ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)) P := by
  have hcov := measurable_sampleCovariance.comp_aemeasurable hX
  have hHermitian := hcov.subtype_mk (s := {A | A.IsHermitian})
    (hfs := fun ω ↦ isHermitian_sampleCovariance (X ω))
  exact ((continuous_integral_spectralMeasure f.continuous).measurable.comp_aemeasurable
    hHermitian).aestronglyMeasurable

/-- Bounded continuous test integrals of a sample covariance spectrum are integrable under
a finite data law. -/
theorem integrable_integral_spectralMeasure_sampleCovariance [IsFiniteMeasure P]
    (hX : AEMeasurable X P) (f : ℝ →ᵇ ℝ) :
    Integrable (fun ω ↦ ∫ x, f x ∂((X ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)) P :=
  Integrable.of_bound (aestronglyMeasurable_integral_spectralMeasure_sampleCovariance hX f)
    ‖f‖ (.of_forall fun _ ↦ f.norm_integral_le_norm _)

variable [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
private theorem aemeasurable_covarianceMeasure (hX : AEMeasurable X P) :
    AEMeasurable (fun ω ↦ ((X ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance (X ω)) : Measure ℝ)) P :=
  measurable_subtypeVal.comp_aemeasurable
    (Matrix.measurable_spectralMeasure_sampleCovariance.comp_aemeasurable hX)

/-- The probability measure obtained by averaging the empirical covariance spectral measures. -/
def expectedCovarianceSpectralMeasure (hX : AEMeasurable X P) : ProbabilityMeasure ℝ :=
  ⟨P.bind (fun ω ↦ ((X ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance (X ω)) : Measure ℝ)),
    isProbabilityMeasure_bind (aemeasurable_covarianceMeasure hX)
      (.of_forall fun _ ↦ inferInstance)⟩

/-- The expected covariance spectral measure is the mixture of the samplewise measures. -/
theorem toMeasure_expectedCovarianceSpectralMeasure (hX : AEMeasurable X P) :
    (expectedCovarianceSpectralMeasure hX : Measure ℝ) =
      P.bind (fun ω ↦ ((X ω).sampleCovariance.spectralMeasure
        (Matrix.isHermitian_sampleCovariance (X ω)) : Measure ℝ)) := (rfl)

/-- The expected measure of a measurable set is the average of its samplewise masses. -/
theorem expectedCovarianceSpectralMeasure_apply (hX : AEMeasurable X P)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (expectedCovarianceSpectralMeasure hX : Measure ℝ) s =
      ∫⁻ ω, ((X ω).sampleCovariance.spectralMeasure
        (Matrix.isHermitian_sampleCovariance (X ω)) : Measure ℝ) s ∂P := by
  rw [toMeasure_expectedCovarianceSpectralMeasure, Measure.bind_apply hs
    (aemeasurable_covarianceMeasure hX)]

/-- The expected covariance spectral measure is supported on the nonnegative half-line. -/
theorem ae_nonneg_expectedCovarianceSpectralMeasure (hX : AEMeasurable X P) :
    ∀ᵐ x ∂(expectedCovarianceSpectralMeasure hX : Measure ℝ), 0 ≤ x := by
  have hs : MeasurableSet {x : ℝ | ¬0 ≤ x} := by
    simpa only [not_le, id_eq] using
      measurableSet_lt measurable_id (measurable_const (a := (0 : ℝ)))
  rw [ae_iff, expectedCovarianceSpectralMeasure_apply hX hs]
  exact lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall fun ω ↦
    ae_iff.1 (Matrix.posSemidef_sampleCovariance (X ω)).ae_mem_Ici_spectralMeasure)

/-- The CDF of the expected covariance spectral measure is the mean of the samplewise CDFs. -/
theorem cdf_expectedCovarianceSpectralMeasure (hX : AEMeasurable X P) (x : ℝ) :
    cdf (expectedCovarianceSpectralMeasure hX : Measure ℝ) x =
      ∫ ω, cdf ((X ω).sampleCovariance.spectralMeasure
        (Matrix.isHermitian_sampleCovariance (X ω)) : Measure ℝ) x ∂P := by
  simp only [cdf_eq_real]
  rw [toMeasure_expectedCovarianceSpectralMeasure]
  exact Measure.bind_apply_real (aemeasurable_covarianceMeasure hX) measurableSet_Iic
    (.of_forall fun _ ↦ measure_ne_top _ _)

/-- Integrating against the expected measure averages the samplewise spectral statistics. -/
theorem integral_expectedCovarianceSpectralMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hX : AEMeasurable X P) {f : ℝ → E}
    (hf : Integrable f (expectedCovarianceSpectralMeasure hX : Measure ℝ)) :
    ∫ x, f x ∂(expectedCovarianceSpectralMeasure hX : Measure ℝ) =
      ∫ ω, ∫ x, f x ∂((X ω).sampleCovariance.spectralMeasure
        (Matrix.isHermitian_sampleCovariance (X ω)) : Measure ℝ) ∂P := by
  rw [toMeasure_expectedCovarianceSpectralMeasure] at hf ⊢
  exact Measure.integral_bind (aemeasurable_covarianceMeasure hX) hf

omit [Fintype p] [DecidableEq p] [Nonempty p] [Fintype n] in
/-- Almost sure weak convergence implies convergence of the expected covariance measures to
the same deterministic law, with no independence or moments required. -/
theorem tendsto_expectedCovarianceSpectralMeasure_of_ae_tendsto
    {p n : ℕ → Type*} [∀ m, Fintype (p m)] [∀ m, DecidableEq (p m)]
    [∀ m, Nonempty (p m)] [∀ m, Fintype (n m)]
    {X : (m : ℕ) → Ω → Matrix (p m) (n m) 𝕜} (hX : ∀ m, AEMeasurable (X m) P)
    {μ : ProbabilityMeasure ℝ}
    (h : ∀ᵐ ω ∂P, Tendsto (fun m ↦ (X m ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance (X m ω))) atTop (𝓝 μ)) :
    Tendsto (fun m ↦ expectedCovarianceSpectralMeasure (hX m)) atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_continuousAt_tendsto_cdf.2
  intro x hx
  simp only [cdf_expectedCovarianceSpectralMeasure]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m ↦ cdf ((X m ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance (X m ω)) : Measure ℝ) x) atTop
        (𝓝 (cdf (μ : Measure ℝ) x)) :=
    h.mono fun _ hω ↦ ProbabilityMeasure.tendsto_cdf_of_tendsto_of_continuousAt hω hx
  have hi (m : ℕ) : AEStronglyMeasurable (fun ω ↦ cdf ((X m ω).sampleCovariance.spectralMeasure
      (Matrix.isHermitian_sampleCovariance (X m ω)) : Measure ℝ) x) P := by
    simp only [cdf_eq_real, measureReal_def]
    exact (((Measure.measurable_coe measurableSet_Iic).comp_aemeasurable
      (aemeasurable_covarianceMeasure (hX m))).ennreal_toReal).aestronglyMeasurable
  simpa using tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ)) hi
    (integrable_const _) (fun _ ↦ .of_forall fun _ ↦
      (Real.norm_of_nonneg (cdf_nonneg _ _)).trans_le (cdf_le_one _ _)) hlim

end TauCeti.Probability
