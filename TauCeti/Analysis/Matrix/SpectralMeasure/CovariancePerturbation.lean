/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.SingularValues
public import TauCeti.Analysis.Matrix.SampleSecondMoment
public import TauCeti.MeasureTheory.Measure.Real

/-!
# Perturbing sample covariance spectral measures

The square-root image of the spectral measure of `X Xᴴ / n` is the singular-value measure of
`Xᴴ / √n`, normalized by the number of rows of `X`. The singular-value Hoffman–Wielandt
inequality therefore bounds the squared change in every Lipschitz square-root spectral
statistic by the mean squared entrywise change in `X`.

This estimate permits bounded approximation of data with only a finite second moment: no
fourth moments of the covariance entries are needed. The row normalization retains zero
eigenvalues when the number of rows exceeds the number of columns. Empty samples are allowed;
the row index must be nonempty to define the spectral probability measure.

## References

* Z. Bai and J. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  second edition, Springer, 2010, Appendix A, the singular-value perturbation inequality.
-/

public section

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Frobenius NNReal

namespace Matrix

variable {m n 𝕜 E : Type*} [Fintype m] [Fintype n] [DecidableEq n] [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq n] in
/-- Square roots of the covariance eigenvalues have the singular-value law of `Xᴴ / √n`.
The empirical probability normalization is the number of rows, including zero eigenvalues. -/
theorem map_spectralMeasure_sampleCovariance_sqrt [DecidableEq m] [Nonempty m]
    (X : Matrix m n 𝕜) :
    ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X)).map Real.sqrt =
      ((Real.sqrt (Fintype.card n))⁻¹ • Xᴴ).singularValueMeasure := by
  have hgram : (((Real.sqrt (Fintype.card n))⁻¹ • Xᴴ)ᴴ *
      ((Real.sqrt (Fintype.card n))⁻¹ • Xᴴ)) = sampleCovariance X := by
    rw [sampleCovariance_def, conjTranspose_smul, conjTranspose_conjTranspose,
      smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    simp [← sq, Real.sq_sqrt (Nat.cast_nonneg (Fintype.card n))]
  simpa only [hgram] using
    map_spectralMeasure_conjTranspose_mul_self_sqrt ((Real.sqrt (Fintype.card n))⁻¹ • Xᴴ)

omit [DecidableEq n] in
/-- Lipschitz tests of the square roots of covariance eigenvalues are stable in the average
squared entrywise error. This requires second moments of the data rather than fourth moments. -/
theorem sq_norm_integral_sqrt_sampleCovariance_sub_le [DecidableEq m] [Nonempty m]
    (X Y : Matrix m n 𝕜) {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) :
    ‖∫ x, f (Real.sqrt x)
          ∂((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X) : Measure ℝ) -
        ∫ x, f (Real.sqrt x)
          ∂((sampleCovariance Y).spectralMeasure
            (isHermitian_sampleCovariance Y) : Measure ℝ)‖ ^ 2 ≤
      (K : ℝ) ^ 2 * ‖X - Y‖ ^ 2 / (Fintype.card m * Fintype.card n) := by
  have hint (A : Matrix m n 𝕜) :
      ∫ x, f (Real.sqrt x)
        ∂((sampleCovariance A).spectralMeasure (isHermitian_sampleCovariance A) : Measure ℝ) =
      ∫ x, f x ∂((((Real.sqrt (Fintype.card n))⁻¹ • Aᴴ).singularValueMeasure) : Measure ℝ) := by
    rw [← map_spectralMeasure_sampleCovariance_sqrt, ProbabilityMeasure.toMeasure_map,
      integral_map (by fun_prop) hf.continuous.aestronglyMeasurable]
  rw [hint X, hint Y]
  have h := sq_norm_integral_singularValueMeasure_sub_le
    ((Real.sqrt (Fintype.card n))⁻¹ • Xᴴ)
    ((Real.sqrt (Fintype.card n))⁻¹ • Yᴴ) hf
  rw [← smul_sub, ← conjTranspose_sub, norm_smul, frobenius_norm_conjTranspose,
    mul_pow, Real.norm_of_nonneg (by positivity), inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg (Fintype.card n))] at h
  convert h using 1; ring

/-- Weak convergence of covariance laws is equivalent to weak convergence of their
square-root images. Thus Lipschitz tests of square roots determine covariance spectral limits.
The reference law is assumed to be carried by the nonnegative half-line. -/
theorem tendsto_spectralMeasure_sampleCovariance_iff
    {ι : Type*} {p n : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (p i)] [∀ i, Nonempty (p i)]
    (X : (i : ι) → Matrix (p i) (n i) 𝕜) {l : Filter ι} {μ : ProbabilityMeasure ℝ}
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), 0 ≤ x) :
    Filter.Tendsto (fun i ↦ (sampleCovariance (X i)).spectralMeasure
      (isHermitian_sampleCovariance (X i))) l (nhds μ) ↔
    Filter.Tendsto (fun i ↦ ((Real.sqrt (Fintype.card (n i)))⁻¹ • (X i)ᴴ).singularValueMeasure)
      l (nhds (μ.map Real.sqrt)) := by
  have hmap (ν : ProbabilityMeasure ℝ) (hν : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x) :
      (ν.map Real.sqrt).map (fun x ↦ x ^ 2) = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, Measure.map_sq_map_sqrt _ hν]
  constructor
  · intro h
    simpa only [Function.comp_def, map_spectralMeasure_sampleCovariance_sqrt] using
      (ProbabilityMeasure.continuous_map Real.continuous_sqrt).tendsto μ |>.comp h
  · intro h
    have hs := (ProbabilityMeasure.continuous_map (by fun_prop : Continuous (fun x : ℝ ↦ x ^ 2)))
      |>.tendsto (μ.map Real.sqrt) |>.comp h
    simpa only [Function.comp_def, ← map_spectralMeasure_sampleCovariance_sqrt, hmap μ hμ,
      hmap _ (posSemidef_sampleCovariance _).ae_mem_Ici_spectralMeasure] using hs

end Matrix
