/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Stability
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.HoffmanWielandt
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
public import TauCeti.Analysis.Matrix.Resolvent.RankBound

/-!
# Stability of spectral-measure resolvent transforms

The resolvent transform of a Hermitian matrix's empirical spectral measure is its normalized
resolvent trace. Its variation in both the matrix and the spectral parameter is bounded by the
corresponding operator-norm resolvent estimate, uniformly in the matrix dimension.
At a fixed parameter, the normalized Frobenius error gives a second bound. Splitting a
perturbation into a low-rank part and a Frobenius-small remainder combines both controls.

## Main results

* `Matrix.norm_resolventTransform_spectralMeasure_sub_le`: a joint stability estimate.
* `Matrix.norm_resolventTransform_spectralMeasure_sub_le_matrix`: fixed-parameter stability.
* `Matrix.norm_resolventTransform_spectralMeasure_sub_le_frobenius`: a normalized Frobenius bound.
* `Matrix.norm_resolventTransform_spectralMeasure_sub_le_rank_add_frobenius`: the mixed bound.
-/

public section

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Quantitative stability of the resolvent transforms of two Hermitian spectral measures. -/
theorem norm_resolventTransform_spectralMeasure_sub_le
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (B.spectralMeasure hB : Measure ℝ) w‖ ≤
        |z.im|⁻¹ * (‖B - A‖ + ‖z - w‖) * |w.im|⁻¹ := by
  rw [resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz),
    resolventTransform_spectralMeasure B hB (hB.notMem_spectrum_of_im_ne_zero hw),
    ← mul_sub, ← Matrix.trace_sub]
  exact (norm_normalized_trace_le_l2_opNorm _).trans
    (hA.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_add hB hz hw)

/-- At a fixed non-real parameter, spectral transforms are stable under matrix perturbations. -/
theorem norm_resolventTransform_spectralMeasure_sub_le_matrix
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (B.spectralMeasure hB : Measure ℝ) z‖ ≤
        |z.im|⁻¹ * ‖B - A‖ * |z.im|⁻¹ := by
  simpa using norm_resolventTransform_spectralMeasure_sub_le hA hB hz hz

open scoped Matrix.Norms.Frobenius in
/-- At a fixed nonreal parameter, the transform error is bounded by the Frobenius error
divided by the square root of the dimension and by `|Im z|²`. -/
theorem norm_resolventTransform_spectralMeasure_sub_le_frobenius
    {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (B.spectralMeasure hB : Measure ℝ) z‖ ≤
        |z.im|⁻¹ ^ 2 * ‖A - B‖ / Real.sqrt (Fintype.card n) := by
  simpa only [resolventTransform_apply, NNReal.coe_pow, NNReal.coe_inv, coe_nnNorm,
    Real.norm_eq_abs] using norm_integral_spectralMeasure_sub_integral_spectralMeasure_le
      hA hB (Complex.lipschitzWith_resolvent_real hz)

open scoped Matrix.Norms.Frobenius in
/-- Splitting a Hermitian perturbation into a low-rank part `P` and a small Frobenius remainder
controls its spectral-transform error without controlling the norm of `P`. -/
theorem norm_resolventTransform_spectralMeasure_sub_le_rank_add_frobenius
    {A B P : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hP : P.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (B.spectralMeasure hB : Measure ℝ) z‖ ≤
      (P.rank : ℝ) / ((Fintype.card n : ℝ) * |z.im|) +
        |z.im|⁻¹ ^ 2 * ‖A - B - P‖ / Real.sqrt (Fintype.card n) := by
  calc
    _ ≤ ‖resolventTransform ((B + P).spectralMeasure (hB.add hP) : Measure ℝ) z -
          resolventTransform (B.spectralMeasure hB : Measure ℝ) z‖ +
        ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
          resolventTransform ((B + P).spectralMeasure (hB.add hP) : Measure ℝ) z‖ := by
      simpa only [add_comm] using norm_sub_le_norm_sub_add_norm_sub
        (resolventTransform (A.spectralMeasure hA : Measure ℝ) z)
        (resolventTransform ((B + P).spectralMeasure (hB.add hP) : Measure ℝ) z)
        (resolventTransform (B.spectralMeasure hB : Measure ℝ) z)
    _ ≤ _ := add_le_add
      (by simpa only [add_sub_cancel_left] using
        (hB.add hP).norm_resolventTransform_spectralMeasure_sub_le_rank hB hz)
      (by simpa only [sub_add_eq_sub_sub] using
        norm_resolventTransform_spectralMeasure_sub_le_frobenius hA (hB.add hP) hz)

end Matrix
