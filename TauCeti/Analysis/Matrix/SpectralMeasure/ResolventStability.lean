/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Stability
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic

/-!
# Stability of spectral-measure resolvent transforms

The resolvent transform of a Hermitian matrix's empirical spectral measure is its normalized
resolvent trace. Its variation in both the matrix and the spectral parameter is bounded by the
corresponding operator-norm resolvent estimate, uniformly in the matrix dimension.

## Main results

* `Matrix.norm_normalized_trace_le_l2_opNorm`: the normalized trace bound.
* `Matrix.norm_resolventTransform_spectralMeasure_sub_le`: a joint stability estimate.
* `Matrix.norm_resolventTransform_spectralMeasure_sub_le_matrix` and
  `Matrix.norm_resolventTransform_spectralMeasure_sub_le_parameter`: the two specializations.
-/

public section

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The absolute normalized trace is at most the Euclidean operator norm. -/
theorem norm_normalized_trace_le_l2_opNorm (M : Matrix n n ℂ) :
    ‖((Fintype.card n : ℕ) : ℂ)⁻¹ * M.trace‖ ≤ ‖M‖ := by
  have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have htrace : ‖M.trace‖ ≤ (Fintype.card n : ℝ) * ‖M‖ := by
    calc
      ‖M.trace‖ ≤ ∑ i : n, ‖M i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : n, ‖M‖ := Finset.sum_le_sum (fun i _ => norm_apply_le_l2_opNorm M i i)
      _ = (Fintype.card n : ℝ) * ‖M‖ := by simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (Fintype.card n : ℝ)⁻¹ * ‖M.trace‖ ≤
        (Fintype.card n : ℝ)⁻¹ * ((Fintype.card n : ℝ) * ‖M‖) :=
      mul_le_mul_of_nonneg_left htrace (inv_nonneg.mpr hcard.le)
    _ = ‖M‖ := by rw [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul]

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
  rw [resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz),
    resolventTransform_spectralMeasure B hB (hB.notMem_spectrum_of_im_ne_zero hz),
    ← mul_sub, ← Matrix.trace_sub]
  exact (norm_normalized_trace_le_l2_opNorm _).trans
    (hA.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_matrix hB hz)

/-- For a fixed Hermitian matrix, the spectral transform is stable in its parameter. -/
theorem norm_resolventTransform_spectralMeasure_sub_le_parameter
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
      resolventTransform (A.spectralMeasure hA : Measure ℝ) w‖ ≤
        |z.im|⁻¹ * ‖z - w‖ * |w.im|⁻¹ := by
  rw [resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz),
    resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hw),
    ← mul_sub, ← Matrix.trace_sub]
  exact (norm_normalized_trace_le_l2_opNorm _).trans
    (hA.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_parameter hz hw)

end Matrix
