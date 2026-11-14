/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.CovariancePerturbation
public import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
public import Mathlib.Probability.IdentDistrib

/-!
# Bounded approximation of sample covariance matrices

Cutting off the entries of a data matrix at a fixed norm level approximates its covariance
spectral statistics in probability, uniformly in both matrix dimensions. Only a finite second
absolute moment of the common entry law is needed; the entries need not be independent.

The tests are Lipschitz functions of the square roots of covariance eigenvalues. These are
the singular values of the normalized data matrix, with row normalization and all forced
zeros retained. The deterministic weak-convergence criterion identifies this test family
with weak convergence of the covariance spectral laws themselves.

The finite perturbation bound applies to any coupling of two data matrices. Its common-error-law
form is consumed by the cutoff estimate and its uniform limit. Cutoff zero and empty samples
are included. Centering the cutoff entries is a separate operation.

## References

* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  second edition, Springer, 2010, §3.3 and Appendix A.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Frobenius NNReal Topology ENNReal

namespace TauCeti.Probability

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p n : Type*} [Fintype p] [Fintype n] [DecidableEq p] [Nonempty p]

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
/-- A mean squared data perturbation controls the probability of a change in any Lipschitz
square-root covariance statistic. No independence or measurability of the two matrices is
needed beyond integrability of their squared Frobenius difference. -/
theorem measureReal_norm_integral_sqrt_sampleCovariance_sub_ge_le
    (X Y : Ω → Matrix p n 𝕜) (hXY : Integrable (fun ω ↦ ‖X ω - Y ω‖ ^ 2) P)
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ ‖∫ x, f (Real.sqrt x)
        ∂((X ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) -
      ∫ x, f (Real.sqrt x)
        ∂((Y ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)‖}
      ≤ (K : ℝ) ^ 2 * (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P) /
        (Fintype.card p * Fintype.card n * ε ^ 2) := by
  let g (ω : Ω) := (K : ℝ) ^ 2 * ‖X ω - Y ω‖ ^ 2 /
    (Fintype.card p * Fintype.card n)
  have hg : Integrable g P := (hXY.const_mul _).div_const _
  have hsub : {ω | ε ≤ ‖∫ x, f (Real.sqrt x)
        ∂((X ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) -
      ∫ x, f (Real.sqrt x)
        ∂((Y ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)‖}
      ⊆ {ω | ε ^ 2 ≤ g ω} := by
    intro ω hω
    exact (pow_le_pow_left₀ hε.le hω 2).trans
      (Matrix.sq_norm_integral_sqrt_sampleCovariance_sub_le (X ω) (Y ω) hf)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := g) (Eventually.of_forall fun _ ↦ by positivity) hg (ε ^ 2)
  rw [← div_div]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  calc
    _ ≤ P.real {ω | ε ^ 2 ≤ g ω} * ε ^ 2 :=
      mul_le_mul_of_nonneg_right
        (measureReal_mono hsub (hg.measure_ge_lt_top (sq_pos_of_pos hε)).ne) (sq_nonneg ε)
    _ ≤ ∫ ω, g ω ∂P := by linarith
    _ = _ := by simp only [g, integral_div, integral_const_mul]

/-- If every entrywise error has one common square-integrable law, the approximation bound
is independent of both matrix dimensions. No independence between entries is required. -/
theorem measureReal_norm_integral_sqrt_sampleCovariance_sub_ge_le_of_identDistrib
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {Z : Ω' → 𝕜}
    (X Y : Ω → Matrix p n 𝕜) (hZ : MemLp Z 2 Q)
    (hid : ∀ i j, IdentDistrib (fun ω ↦ X ω i j - Y ω i j) Z P Q)
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ ‖∫ x, f (Real.sqrt x)
        ∂((X ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) -
      ∫ x, f (Real.sqrt x)
        ∂((Y ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)‖}
      ≤ (K : ℝ) ^ 2 * (∫ ω, ‖Z ω‖ ^ 2 ∂Q) / ε ^ 2 := by
  have hsq (ω : Ω) : ‖X ω - Y ω‖ ^ 2 = ∑ i, ∑ j, ‖X ω i j - Y ω i j‖ ^ 2 := by
    simp only [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.rpow_two]
    exact Real.sq_sqrt (by positivity)
  have hint (i : p) (j : n) : Integrable (fun ω ↦ ‖X ω i j - Y ω i j‖ ^ 2) P :=
    ((hid i j).memLp_iff.mpr hZ).norm.integrable_sq
  have hXY : Integrable (fun ω ↦ ‖X ω - Y ω‖ ^ 2) P := by
    simp_rw [hsq]
    exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j
  have heq : ∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P =
      (Fintype.card p * Fintype.card n : ℝ) * ∫ ω, ‖Z ω‖ ^ 2 ∂Q := by
    have heach (i : p) (j : n) :
        ∫ ω, ‖X ω i j - Y ω i j‖ ^ 2 ∂P = ∫ ω, ‖Z ω‖ ^ 2 ∂Q :=
      ((hid i j).comp (by fun_prop : Measurable (fun z : 𝕜 ↦ ‖z‖ ^ 2))).integral_eq
    simp_rw [hsq]
    rw [integral_finsetSum _ (fun i _ ↦
      integrable_finsetSum _ fun j _ ↦ hint i j)]
    simp_rw [integral_finsetSum _ (fun j _ ↦ hint _ j), heach]
    simp [mul_assoc]
  have h := measureReal_norm_integral_sqrt_sampleCovariance_sub_ge_le X Y hXY hf hε
  rw [heq] at h
  cases isEmpty_or_nonempty n
  · exact h.trans (by
      simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, mul_zero, zero_mul, div_zero]
      positivity)
  · convert h using 1
    have hp : (Fintype.card p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hn : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp

/-- Cutting off a common square-integrable entry law gives a dimension-free bound, expressed
by the discarded second moment. Entries can have arbitrary dependence. -/
theorem measureReal_norm_integral_sqrt_sampleCovariance_sub_cutoff_ge_le
    {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {Z : Ω' → 𝕜}
    (X : Ω → Matrix p n 𝕜) (hZ : MemLp Z 2 Q)
    (hid : ∀ i j, IdentDistrib (fun ω ↦ X ω i j) Z P Q) (R : ℝ)
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ ‖∫ x, f (Real.sqrt x)
        ∂((X ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) -
      ∫ x, f (Real.sqrt x)
        ∂((Matrix.sampleCovariance (fun i j ↦ if ‖X ω i j‖ ≤ R then X ω i j else 0)).spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)‖}
      ≤ (K : ℝ) ^ 2 * (∫ ω, ‖Z ω - (if ‖Z ω‖ ≤ R then Z ω else 0)‖ ^ 2 ∂Q) / ε ^ 2 := by
  have hcut : MemLp (fun ω ↦ if ‖Z ω‖ ≤ R then Z ω else 0) 2 Q := by
    exact MemLp.ae_eq (Eventually.of_forall fun ω ↦ Set.indicator_apply _ _ ω)
      (hZ.indicator
        (nullMeasurableSet_le hZ.aestronglyMeasurable.norm.aemeasurable aemeasurable_const))
  apply measureReal_norm_integral_sqrt_sampleCovariance_sub_ge_le_of_identDistrib
    X (fun ω i j ↦ if ‖X ω i j‖ ≤ R then X ω i j else 0) (hZ.sub hcut) _ hf hε
  intro i j
  exact (hid i j).comp (measurable_id.sub
    (measurable_id.ite (measurableSet_le measurable_norm measurable_const) measurable_const))

omit [Fintype p] [Fintype n] [DecidableEq p] [Nonempty p] in
/-- Bounded cutoff approximation is uniform over an arbitrarily indexed family of matrix
dimensions. The entry law only needs a finite second absolute moment, with no independence,
centering or restriction on aspect ratios. -/
theorem tendsto_iSup_measureReal_norm_integral_sqrt_sampleCovariance_sub_cutoff
    {ι Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'} {Z : Ω' → 𝕜}
    {p n : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (p i)] [∀ i, Nonempty (p i)]
    (X : (i : ι) → Ω → Matrix (p i) (n i) 𝕜) (hZ : MemLp Z 2 Q)
    (hid : ∀ i j k, IdentDistrib (fun ω ↦ X i ω j k) Z P Q)
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ ↦ ⨆ i, P.real {ω | ε ≤ ‖∫ x, f (Real.sqrt x)
        ∂((X i ω).sampleCovariance.spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ) -
      ∫ x, f (Real.sqrt x)
        ∂((Matrix.sampleCovariance
          (fun j k ↦ if ‖X i ω j k‖ ≤ R then X i ω j k else 0)).spectralMeasure
          (Matrix.isHermitian_sampleCovariance _) : Measure ℝ)‖}) atTop (𝓝 0) := by
  have htail : Tendsto (fun R : ℝ ↦
      ∫ ω, ‖Z ω - (if ‖Z ω‖ ≤ R then Z ω else 0)‖ ^ 2 ∂Q) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hZ.tendsto_lintegral_eNorm_ite_sub_rpow (by norm_num) (by norm_num))
    simp only [Function.comp_def, ENNReal.toReal_zero] at h
    convert h using 1
    ext R
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ sq_nonneg _) ?_]
    · congr 1
      apply lintegral_congr
      intro ω
      simp [norm_sub_rev, ← ofReal_norm, ENNReal.ofReal_pow]
    · have hcut : AEStronglyMeasurable
          (fun ω ↦ if ‖Z ω‖ ≤ R then Z ω else 0) Q := by
        exact (hZ.aestronglyMeasurable.indicator₀
          (nullMeasurableSet_le hZ.aestronglyMeasurable.norm.aemeasurable aemeasurable_const)).congr
            (Eventually.of_forall fun ω ↦ Set.indicator_apply _ _ ω)
      exact (hZ.aestronglyMeasurable.sub hcut).norm.pow 2
  cases isEmpty_or_nonempty ι
  · simp
  apply squeeze_zero (fun R ↦ Real.iSup_nonneg fun i ↦ measureReal_nonneg)
    (fun R ↦ ciSup_le fun i ↦
      measureReal_norm_integral_sqrt_sampleCovariance_sub_cutoff_ge_le (X i) hZ (hid i) R hf hε)
  simpa using ((tendsto_const_nhds (x := (K : ℝ) ^ 2)).mul htail).div_const (ε ^ 2)

end TauCeti.Probability
