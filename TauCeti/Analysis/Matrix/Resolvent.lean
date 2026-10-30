/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import TauCeti.Analysis.Matrix.SpectralMeasure
public import TauCeti.Analysis.Matrix.Spectrum

/-!
# Resolvents of Hermitian matrices and the Stieltjes transform of the spectral measure

For a Hermitian matrix `A` over an `RCLike` field and a scalar `z` that is not an eigenvalue, the
resolvent `R_A(z) = (A - z • 1)⁻¹` is diagonal in the eigenbasis of `A`, with entries
`(λⱼ - z)⁻¹`. This file records the consequences used by the resolvent method of random matrix
theory:

* its trace is `∑ⱼ (λⱼ - z)⁻¹`, so the Stieltjes transform `m(z) = ∫ (x - z)⁻¹ dL_A(x)` of the
  empirical spectral measure (Mathlib's `MeasureTheory.resolventTransform`) is the normalized
  trace `n⁻¹ tr R_A(z)`;
* its conjugate transpose is the resolvent at `star z`, and its Euclidean operator norm is the
  largest `|λⱼ - z|⁻¹`, hence at most `|Im z|⁻¹` off the real axis;
* the Ward identity `∑ⱼ |R_A(z)ᵢⱼ|² = Im R_A(z)ᵢᵢ / Im z`, which follows from
  `R - Rᴴ = (z - star z) • R Rᴴ`.

The sign convention `(A - z • 1)⁻¹` matches the kernel `(x - z)⁻¹` of `resolventTransform` with
base field `ℝ`, under which the Stieltjes transform of a probability measure has positive imaginary
part in the upper half-plane. Mathlib's `resolvent A z` is `(z • 1 - A)⁻¹`, its negative.

## Main results

* `Matrix.IsHermitian.inv_sub_smul_one_eq_conjStarAlgAut_diagonal` — the spectral decomposition
  of the resolvent;
* `Matrix.IsHermitian.trace_inv_sub_smul_one` — `tr R_A(z) = ∑ⱼ (λⱼ - z)⁻¹`;
* `Matrix.IsHermitian.l2_opNorm_inv_sub_smul_one_le` — `‖R_A(z)‖ ≤ |Im z|⁻¹`;
* `Matrix.IsHermitian.sum_norm_inv_sub_smul_one_apply_sq` — the Ward identity;
* `Matrix.resolventTransform_spectralMeasure_eq_trace` — `m_{L_A}(z) = n⁻¹ tr R_A(z)`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.4.
* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.4.3.
-/

public section

noncomputable section

open MeasureTheory Unitary
open scoped Matrix.Norms.L2Operator

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
  (hA : A.IsHermitian)
include hA

/-- The shifted matrix `A - z • 1` is conjugate, by the eigenvector unitary of `A`, to the
diagonal matrix with entries `λⱼ - z`. -/
theorem sub_smul_one_eq_conjStarAlgAut_diagonal (z : 𝕜) :
    A - z • 1 =
      conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (diagonal fun j => (hA.eigenvalues j : 𝕜) - z) := by
  have h : (diagonal fun j => (hA.eigenvalues j : 𝕜) - z) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) - z • 1 := by
    rw [← diagonal_one, ← diagonal_smul, diagonal_sub]
    simp
  rw [h, map_sub, map_smul, map_one, ← hA.spectral_theorem]

/-- `A - z • 1` is invertible exactly when `z` is not an eigenvalue of `A`. -/
theorem isUnit_sub_smul_one_iff (z : 𝕜) :
    IsUnit (A - z • 1) ↔ ∀ j, (hA.eigenvalues j : 𝕜) ≠ z := by
  rw [← IsUnit.neg_iff, neg_sub, ← Algebra.algebraMap_eq_smul_one, ← spectrum.notMem_iff,
    hA.spectrum_eq_image_range]
  simp

/-- A scalar off the real axis is not an eigenvalue. -/
private theorem ofReal_eigenvalues_ne_of_im_ne_zero {z : 𝕜} (hz : RCLike.im z ≠ 0) (j : n) :
    (hA.eigenvalues j : 𝕜) ≠ z :=
  fun h => hz (by rw [← h, RCLike.ofReal_im])

/-- Off the real axis, `A - z • 1` is invertible. -/
theorem isUnit_sub_smul_one_of_im_ne_zero {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    IsUnit (A - z • 1) :=
  (hA.isUnit_sub_smul_one_iff z).2 (hA.ofReal_eigenvalues_ne_of_im_ne_zero hz)

/-- The resolvent `(A - z • 1)⁻¹` at a non-eigenvalue `z` is conjugate, by the eigenvector unitary
of `A`, to the diagonal matrix with entries `(λⱼ - z)⁻¹`. -/
theorem inv_sub_smul_one_eq_conjStarAlgAut_diagonal {z : 𝕜}
    (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) :
    (A - z • 1)⁻¹ =
      conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (diagonal fun j => ((hA.eigenvalues j : 𝕜) - z)⁻¹) := by
  refine inv_eq_left_inv ?_
  rw [hA.sub_smul_one_eq_conjStarAlgAut_diagonal, ← map_mul, diagonal_mul_diagonal,
    ← map_one (conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary), ← diagonal_one]
  congr 2
  ext j
  exact inv_mul_cancel₀ (sub_ne_zero.2 (hz j))

/-- The trace of the resolvent at a non-eigenvalue `z` is `∑ⱼ (λⱼ - z)⁻¹`. -/
theorem trace_inv_sub_smul_one {z : 𝕜} (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) :
    (A - z • 1)⁻¹.trace = ∑ j, ((hA.eigenvalues j : 𝕜) - z)⁻¹ := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply, trace_mul_cycle,
    star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul, trace_diagonal]

/-- The conjugate transpose of the resolvent at `z` is the resolvent at `star z`. -/
theorem conjTranspose_inv_sub_smul_one (z : 𝕜) :
    (A - z • 1)⁻¹ᴴ = (A - star z • 1)⁻¹ := by
  rw [conjTranspose_nonsing_inv, conjTranspose_sub, hA.eq, conjTranspose_smul, conjTranspose_one]

/-- The imaginary part of the resolvent: `R - Rᴴ = (z - star z) • (R * Rᴴ)` for
`R = (A - z • 1)⁻¹` and `z` not an eigenvalue. -/
theorem inv_sub_smul_one_sub_conjTranspose {z : 𝕜} (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) :
    (A - z • 1)⁻¹ - (A - z • 1)⁻¹ᴴ =
      (z - star z) • ((A - z • 1)⁻¹ * (A - z • 1)⁻¹ᴴ) := by
  have hz' (j : n) : (hA.eigenvalues j : 𝕜) ≠ star z := fun h =>
    hz j (by simpa using congr_arg star h)
  have hu := (A - z • 1).isUnit_iff_isUnit_det.1 ((hA.isUnit_sub_smul_one_iff z).2 hz)
  have hu' := (A - star z • 1).isUnit_iff_isUnit_det.1 ((hA.isUnit_sub_smul_one_iff _).2 hz')
  rw [hA.conjTranspose_inv_sub_smul_one]
  calc (A - z • 1)⁻¹ - (A - star z • 1)⁻¹
      = (A - z • 1)⁻¹ * (A - star z • 1) * (A - star z • 1)⁻¹ -
          (A - z • 1)⁻¹ * (A - z • 1) * (A - star z • 1)⁻¹ := by
        rw [nonsing_inv_mul _ hu, one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hu', Matrix.mul_one]
    _ = (z - star z) • ((A - z • 1)⁻¹ * (A - star z • 1)⁻¹) := by
        rw [← Matrix.sub_mul, ← Matrix.mul_sub, sub_sub_sub_cancel_left, ← sub_smul,
          Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- **Ward identity.** For `z` off the real axis, the squared moduli of the `i`-th row of the
resolvent `R = (A - z • 1)⁻¹` sum to `Im Rᵢᵢ / Im z`. -/
theorem sum_norm_inv_sub_smul_one_apply_sq {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    ∑ j, ‖(A - z • 1)⁻¹ i j‖ ^ 2 = RCLike.im ((A - z • 1)⁻¹ i i) / RCLike.im z := by
  have h := congr_arg (fun M : Matrix n n 𝕜 => RCLike.im (M i i))
    (hA.inv_sub_smul_one_sub_conjTranspose (hA.ofReal_eigenvalues_ne_of_im_ne_zero hz))
  simp only [sub_apply, conjTranspose_apply, smul_apply, mul_apply, smul_eq_mul,
    RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_sum, map_sub,
    RCLike.conj_im, RCLike.im_mul_ofReal] at h
  rw [eq_div_iff hz]
  linarith

/-- The Euclidean operator norm of the resolvent at a non-eigenvalue `z` is the sup norm of the
family `(λⱼ - z)⁻¹`, that is, the reciprocal of the distance from `z` to the spectrum. -/
theorem l2_opNorm_inv_sub_smul_one {z : 𝕜} (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) :
    ‖(A - z • 1)⁻¹‖ = ‖fun j => ((hA.eigenvalues j : 𝕜) - z)⁻¹‖ := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply,
    ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    l2_opNorm_diagonal]

/-- Off the real axis, the Euclidean operator norm of the resolvent is at most `|Im z|⁻¹`. -/
theorem l2_opNorm_inv_sub_smul_one_le {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    ‖(A - z • 1)⁻¹‖ ≤ |RCLike.im z|⁻¹ := by
  rw [hA.l2_opNorm_inv_sub_smul_one (hA.ofReal_eigenvalues_ne_of_im_ne_zero hz)]
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  rw [norm_inv]
  refine inv_anti₀ (abs_pos.2 hz) ?_
  simpa using RCLike.abs_im_le_norm ((hA.eigenvalues j : 𝕜) - z)

end Matrix.IsHermitian

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The Stieltjes transform `m(z) = ∫ (x - z)⁻¹ dL_A(x)` of the empirical spectral measure of a
Hermitian matrix is the average of `(λⱼ - z)⁻¹` over the eigenvalues. -/
theorem resolventTransform_spectralMeasure (A : Matrix n n 𝕜) (hA : A.IsHermitian) (z : 𝕜) :
    resolventTransform (A.spectralMeasure hA : Measure ℝ) z =
      ((Fintype.card n : ℕ) : 𝕜)⁻¹ * ∑ j, ((hA.eigenvalues j : 𝕜) - z)⁻¹ := by
  rw [resolventTransform_apply, integral_spectralMeasure, RCLike.real_smul_eq_coe_mul]
  simp [resolvent, Ring.inverse_eq_inv', RCLike.algebraMap_eq_ofReal]

/-- At a non-eigenvalue `z`, the Stieltjes transform of the empirical spectral measure of a
Hermitian matrix is the normalized trace of its resolvent: `m_{L_A}(z) = n⁻¹ tr (A - z • 1)⁻¹`. -/
theorem resolventTransform_spectralMeasure_eq_trace (A : Matrix n n 𝕜) (hA : A.IsHermitian)
    {z : 𝕜} (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) :
    resolventTransform (A.spectralMeasure hA : Measure ℝ) z =
      ((Fintype.card n : ℕ) : 𝕜)⁻¹ * (A - z • 1)⁻¹.trace := by
  rw [resolventTransform_spectralMeasure, hA.trace_inv_sub_smul_one hz]

end Matrix
