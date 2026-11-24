/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.SampleCovariance
import TauCeti.Analysis.Matrix.Resolvent.RankBound

/-!
# Self-consistency of the sample covariance resolvent

The Marchenko–Pastur quadratic evaluated at the empirical transform is a weighted sum of
leave-one-column-out errors. Each weight is an inverse denominator from the rank-one update.
The quadratic residual is bounded by the sum of the errors of replacing the column quadratic
forms by their minor traces, plus the rank-one errors of replacing those traces by the full
trace. A sup-norm form applies to simultaneous concentration of the column errors.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.
-/

public section

noncomputable section

open MeasureTheory

namespace Matrix

variable {p n : Type*} [Fintype p] [DecidableEq p] [Fintype n] [DecidableEq n]

/-- Removing one column changes the unnormalized covariance resolvent trace by at most
the reciprocal of the absolute imaginary part. The column normalization is preserved. -/
theorem norm_trace_inv_sampleCovariance_updateCol_zero_sub_le (X : Matrix p n ℂ) (k : n)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(sampleCovariance X - z • 1)⁻¹.trace -
      (sampleCovariance (X.updateCol k 0) - z • 1)⁻¹.trace‖ ≤ |z.im|⁻¹ := by
  have hr : (sampleCovariance X - sampleCovariance (X.updateCol k 0)).rank ≤ 1 := by
    have he := sampleCovariance_updateCol_zero_add X k
    rw [← he, add_sub_cancel_left, ← smul_vecMulVec]
    exact rank_vecMulVec_le _ _
  have hr' : ((sampleCovariance X - sampleCovariance (X.updateCol k 0)).rank : ℝ) ≤ 1 := by
    exact_mod_cast hr
  simpa only [one_div] using
    ((isHermitian_sampleCovariance X).norm_trace_inv_sub_smul_one_sub_le_rank
      (isHermitian_sampleCovariance (X.updateCol k 0)) hz).trans
      (div_le_div_of_nonneg_right hr' (abs_nonneg z.im))

/-- The leave-one-out resolvent quadratic form of a data column divided by the column count. -/
def sampleCovarianceResolventColumnForm (X : Matrix p n ℂ) (z : ℂ) (k : n) : ℂ :=
  (Fintype.card n : ℂ)⁻¹ *
    (star (X.col k) ⬝ᵥ ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹ *ᵥ X.col k))

/-- The column-normalized leave-one-out resolvent quadratic form in terms of the minor. -/
theorem sampleCovarianceResolventColumnForm_def (X : Matrix p n ℂ) (z : ℂ) (k : n) :
    X.sampleCovarianceResolventColumnForm z k = (Fintype.card n : ℂ)⁻¹ *
      (star (X.col k) ⬝ᵥ ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹ *ᵥ X.col k)) := (rfl)

/-- The leave-one-out quadratic form minus the minor resolvent trace, divided by the column
count. -/
def sampleCovarianceResolventColumnError (X : Matrix p n ℂ) (z : ℂ) (k : n) : ℂ :=
  X.sampleCovarianceResolventColumnForm z k -
    (Fintype.card n : ℂ)⁻¹ * (sampleCovariance (X.updateCol k 0) - z • 1)⁻¹.trace

/-- Expand the leave-one-out column error into its quadratic form and trace. -/
theorem sampleCovarianceResolventColumnError_def (X : Matrix p n ℂ) (z : ℂ) (k : n) :
    X.sampleCovarianceResolventColumnError z k = (Fintype.card n : ℂ)⁻¹ *
      (star (X.col k) ⬝ᵥ ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹ *ᵥ X.col k) -
        (sampleCovariance (X.updateCol k 0) - z • 1)⁻¹.trace) := by
  rw [sampleCovarianceResolventColumnError, sampleCovarianceResolventColumnForm_def, mul_sub]

variable [Nonempty p] [Nonempty n]

/-- The residual of the Marchenko–Pastur polynomial, multiplied by the row dimension,
is the sum of the leave-one-column-out errors with the rank-one inverse denominators
as weights. Each quadratic form is compared with the full trace, normalized by the
number of columns. -/
theorem card_mul_sampleCovariance_resolvent_quadratic_eq_sum (X : Matrix p n ℂ)
    {z : ℂ} (hz : z.im ≠ 0) :
    let y := (Fintype.card p : ℂ) / Fintype.card n
    let m := resolventTransform
      ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X) : Measure ℝ) z
    let q := X.sampleCovarianceResolventColumnForm z
    (Fintype.card p : ℂ) * (y * z * (m * m) + (z + y - 1) * m + 1) =
      ∑ k, (q k - y * m) * (1 + q k)⁻¹ := by
  dsimp only
  set d := (Fintype.card p : ℂ)
  set N := (Fintype.card n : ℂ)
  set m := resolventTransform
    ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X) : Measure ℝ) z
  set q := X.sampleCovarianceResolventColumnForm z
  have h := card_mul_one_add_mul_resolventTransform_spectralMeasure_sampleCovariance X hz
  have hden (k : n) : 1 + q k ≠ 0 := by
    have hk := isHermitian_sampleCovariance (X.updateCol k 0)
    simpa only [q, sampleCovarianceResolventColumnForm_def, Complex.ofReal_inv,
      Complex.ofReal_natCast, RCLike.ofReal_eq_complex_ofReal]
      using hk.one_add_mul_dotProduct_inv_sub_smul_one_ne_zero
        (Fintype.card n : ℝ)⁻¹ (X.col k) hz
  have hterm (k : n) : (q k - d / N * m) * (1 + q k)⁻¹ =
      1 - (1 + d / N * m) * (1 + q k)⁻¹ := by
    field_simp [hden k]
    ring
  have hh : d * (1 + z * m) = N - ∑ k, (1 + q k)⁻¹ := by
    simpa only [q, sampleCovarianceResolventColumnForm_def] using h
  have hn : N ≠ 0 := by simp [N]
  rw [Finset.sum_congr rfl (fun k _ ↦ hterm k), Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hsum : ∑ k, (1 + q k)⁻¹ = N - d * (1 + z * m) := by linear_combination hh
  rw [hsum]
  field_simp
  ring

/-- The Marchenko–Pastur quadratic residual is bounded by the sum of the normalized
leave-one-out quadratic-form errors plus the rank-one trace errors. -/
theorem norm_sampleCovariance_resolvent_quadratic_le_sum (X : Matrix p n ℂ)
    {z : ℂ} (hz : z.im ≠ 0) :
    let y := (Fintype.card p : ℂ) / Fintype.card n
    let m := resolventTransform
      ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X) : Measure ℝ) z
    let E := X.sampleCovarianceResolventColumnError z
    ‖y * z * (m * m) + (z + y - 1) * m + 1‖ ≤
      ((‖z‖ / |z.im|) * ∑ k, (‖E k‖ + ((Fintype.card n : ℝ) * |z.im|)⁻¹)) /
        Fintype.card p := by
  dsimp only
  set m := resolventTransform
    ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X) : Measure ℝ) z
    with hm_def
  set d := Fintype.card p
  set N := Fintype.card n
  set q := X.sampleCovarianceResolventColumnForm z
  set E := X.sampleCovarianceResolventColumnError z
  have hm : (d : ℂ) / N * m = (N : ℂ)⁻¹ * (sampleCovariance X - z • 1)⁻¹.trace := by
    rw [hm_def, resolventTransform_spectralMeasure _ _
      ((isHermitian_sampleCovariance X).notMem_spectrum_of_im_ne_zero hz)]
    simp only [d]
    field_simp
  have hbound (k : n) : ‖q k - (d : ℂ) / N * m‖ ≤ ‖E k‖ + ((N : ℝ) * |z.im|)⁻¹ := by
    rw [hm]
    have he : q k - (N : ℂ)⁻¹ * (sampleCovariance X - z • 1)⁻¹.trace =
        E k + (N : ℂ)⁻¹ * ((sampleCovariance (X.updateCol k 0) - z • 1)⁻¹.trace -
          (sampleCovariance X - z • 1)⁻¹.trace) := by
      simp only [q, E, N, sampleCovarianceResolventColumnError, mul_sub]
      abel
    rw [he]
    refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_mul, norm_inv, Complex.norm_natCast, norm_sub_rev, mul_inv]
    exact mul_le_mul_of_nonneg_left (norm_trace_inv_sampleCovariance_updateCol_zero_sub_le X k hz)
      (by positivity)
  have hd : 0 < (d : ℝ) := by positivity
  apply (le_div_iff₀ hd).2
  calc
    _ = ‖(d : ℂ) * ((d : ℂ) / N * z * (m * m) + (z + (d : ℂ) / N - 1) * m + 1)‖ := by
      rw [norm_mul, Complex.norm_natCast, mul_comm]
    _ ≤ ∑ k, ‖(q k - (d : ℂ) / N * m) * (1 + q k)⁻¹‖ := by
      rw [card_mul_sampleCovariance_resolvent_quadratic_eq_sum X hz]
      exact norm_sum_le _ _
    _ ≤ ∑ k : n, (‖E k‖ + ((N : ℝ) * |z.im|)⁻¹) * (‖z‖ / |z.im|) := by
      refine Finset.sum_le_sum fun k _ ↦ ?_
      rw [norm_mul]
      have hweight :=
        norm_inv_one_add_mul_dotProduct_inv_sampleCovariance_updateCol_sub_smul_one_mulVec_le X k hz
      simp only [← sampleCovarianceResolventColumnForm_def] at hweight
      exact mul_le_mul (hbound k) hweight (norm_nonneg _) (by positivity)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- A simultaneous bound on the normalized leave-one-out errors bounds the
Marchenko–Pastur quadratic residual, with the rank-one trace error made explicit. -/
theorem norm_sampleCovariance_resolvent_quadratic_le (X : Matrix p n ℂ)
    {z : ℂ} (hz : z.im ≠ 0) :
    let y := (Fintype.card p : ℂ) / Fintype.card n
    let m := resolventTransform
      ((sampleCovariance X).spectralMeasure (isHermitian_sampleCovariance X) : Measure ℝ) z
    let E := X.sampleCovarianceResolventColumnError z
    ‖y * z * (m * m) + (z + y - 1) * m + 1‖ ≤
      ((Fintype.card n : ℝ) / Fintype.card p) * (‖z‖ / |z.im|) *
        (‖E‖ + ((Fintype.card n : ℝ) * |z.im|)⁻¹) := by
  dsimp only
  set E := X.sampleCovarianceResolventColumnError z
  refine (norm_sampleCovariance_resolvent_quadratic_le_sum X hz).trans ?_
  calc
    _ ≤ (‖z‖ / |z.im|) * (∑ _ : n, (‖E‖ + ((Fintype.card n : ℝ) * |z.im|)⁻¹)) /
        Fintype.card p := by
      gcongr with k
      exact norm_le_pi_norm E k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Matrix
