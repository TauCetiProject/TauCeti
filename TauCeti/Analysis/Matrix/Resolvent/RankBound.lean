/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.Trace.Rank

import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Low-rank bounds for Hermitian resolvent traces

For Hermitian matrices `A, B` and nonreal `z`, the difference of their resolvents has rank
`rank (A - B)` and Euclidean operator norm at most `1 / |Im z|`. Consequently
`|tr R_A(z) - tr R_B(z)| ≤ rank (A - B) / |Im z|`, and their empirical spectral transforms
differ by at most `rank (A - B) / (n |Im z|)`. No bound on the size of `A - B` is needed.
These estimates control the error from deleting or replacing a low-rank part of a matrix
in the resolvent method for global spectral laws.

The norm estimate uses the unit-disc bound for the Cayley expression
`1 + (z - conj z) • R_A(z)`, rather than the less precise triangle bound on the two resolvents.
All unnormalized estimates allow empty index types; spectral probability measures require
positive dimension. The resolvent convention is `R_A(z) = (A - z • 1)⁻¹`.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices, a review*,
  Statistica Sinica 9 (1999), §2.2.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.4.
-/

public section

open MeasureTheory Unitary
open scoped ComplexConjugate Matrix.Norms.L2Operator

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}

/-- The Cayley expression of a Hermitian resolvent has Euclidean operator norm at most one.
The inequality, unlike equality with one, includes the empty matrix. -/
theorem l2_opNorm_one_add_sub_conj_smul_inv_sub_smul_one_le (hA : A.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖1 + (z - conj z) • (A - z • 1)⁻¹‖ ≤ 1 := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal
    (hA.notMem_spectrum_of_im_ne_zero hz), ← map_smul, ← map_one (conjStarAlgAut ℂ _
      hA.eigenvectorUnitary), ← map_add, conjStarAlgAut_apply,
    ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  rw [← diagonal_smul, ← diagonal_one, diagonal_add, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have hne : (hA.eigenvalues i : ℂ) - z ≠ 0 := by
    intro h
    exact hz (by simpa using congrArg Complex.im h)
  have heq : 1 + (z - conj z) * ((hA.eigenvalues i : ℂ) - z)⁻¹ =
      ((hA.eigenvalues i : ℂ) - conj z) / ((hA.eigenvalues i : ℂ) - z) := by
    field_simp
    ring
  simp only [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_eq_complex_ofReal]
  rw [heq, norm_div]
  have hnorm : ‖(hA.eigenvalues i : ℂ) - conj z‖ = ‖(hA.eigenvalues i : ℂ) - z‖ := by
    simpa using Complex.norm_conj ((hA.eigenvalues i : ℂ) - z)
  rw [hnorm, div_self (norm_ne_zero_iff.mpr hne)]

/-- At a fixed nonreal parameter the difference of two Hermitian resolvents has operator norm
at most `1 / |Im z|`, independently of the size of the perturbation. -/
theorem l2_opNorm_inv_sub_smul_one_sub_le (hA : A.IsHermitian) (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(A - z • 1)⁻¹ - (B - z • 1)⁻¹‖ ≤ |z.im|⁻¹ := by
  have h := (norm_sub_le (1 + (z - conj z) • (A - z • 1)⁻¹)
    (1 + (z - conj z) • (B - z • 1)⁻¹)).trans
      (add_le_add (hA.l2_opNorm_one_add_sub_conj_smul_inv_sub_smul_one_le hz)
        (hB.l2_opNorm_one_add_sub_conj_smul_inv_sub_smul_one_le hz))
  rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Complex.sub_conj] at h
  have hn : ‖((2 * z.im : ℝ) : ℂ) * Complex.I‖ = 2 * |z.im| := by
    simp [Real.norm_eq_abs]
  rw [hn] at h
  rw [inv_eq_one_div |z.im|, le_div_iff₀ (abs_pos.mpr hz)]
  nlinarith

/-- Taking resolvents at a fixed nonreal parameter preserves the rank of the difference. -/
theorem rank_inv_sub_smul_one_sub {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    ((A - z • 1)⁻¹ - (B - z • 1)⁻¹).rank = (A - B).rank := by
  have hdetA := (isUnit_iff_isUnit_det _).mp (hA.isUnit_sub_smul_one_of_im_ne_zero hz)
  have hdetB := (isUnit_iff_isUnit_det _).mp (hB.isUnit_sub_smul_one_of_im_ne_zero hz)
  rw [inv_sub_inv (iff_of_true (hA.isUnit_sub_smul_one_of_im_ne_zero hz)
    (hB.isUnit_sub_smul_one_of_im_ne_zero hz)), sub_sub_sub_cancel_right,
    rank_mul_eq_left_of_isUnit_det _ _ (isUnit_nonsing_inv_det _ hdetB),
    rank_mul_eq_right_of_isUnit_det _ _ (isUnit_nonsing_inv_det _ hdetA),
    ← neg_sub A B, rank_neg]

/-- The trace error of a low-rank Hermitian perturbation is at most its rank divided by the
absolute imaginary part of the parameter. -/
theorem norm_trace_inv_sub_smul_one_sub_le_rank (hA : A.IsHermitian) (hB : B.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖(A - z • 1)⁻¹.trace - (B - z • 1)⁻¹.trace‖ ≤ (A - B).rank / |z.im| := by
  rw [← trace_sub, div_eq_mul_inv]
  have h := norm_trace_le_rank_mul_l2_opNorm ((A - z • 1)⁻¹ - (B - z • 1)⁻¹)
  rw [hA.rank_inv_sub_smul_one_sub hB hz] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (hA.l2_opNorm_inv_sub_smul_one_sub_le hB hz) (Nat.cast_nonneg _))

/-- Low-rank perturbations change the empirical spectral transform by at most
`rank (A - B) / (n |Im z|)`. -/
theorem norm_resolventTransform_spectralMeasure_sub_le_rank [Nonempty n]
    (hA : A.IsHermitian) (hB : B.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) :
    ‖resolventTransform (A.spectralMeasure hA : Measure ℝ) z -
        resolventTransform (B.spectralMeasure hB : Measure ℝ) z‖ ≤
      (A - B).rank / ((Fintype.card n : ℝ) * |z.im|) := by
  rw [resolventTransform_spectralMeasure A hA (hA.notMem_spectrum_of_im_ne_zero hz),
    resolventTransform_spectralMeasure B hB (hB.notMem_spectrum_of_im_ne_zero hz),
    ← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card n : ℝ)⁻¹ * ((A - B).rank / |z.im|) :=
      mul_le_mul_of_nonneg_left (hA.norm_trace_inv_sub_smul_one_sub_le_rank hB hz)
        (by positivity)
    _ = _ := by ring

end Matrix.IsHermitian
