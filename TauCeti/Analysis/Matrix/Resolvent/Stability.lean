/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# Stability of Hermitian matrix resolvents

For `R_A(z) = (A - z • 1)⁻¹`, the resolvent identity controls changes in the matrix and
spectral parameter. For Hermitian `A` and `B` and non-real `z` and `w`,

`‖R_A(z) - R_B(w)‖ ≤ |Im z|⁻¹ ‖(B - A) + (z - w) • 1‖ |Im w|⁻¹`.

The two useful specializations bound perturbations of the matrix at fixed `z`, and changes of
the spectral parameter at fixed `A`. The bounds use the Euclidean operator norm and also cover
empty matrices; an entrywise corollary follows from the operator-norm estimate.

## Main results

* `Matrix.IsHermitian.inv_sub_smul_one_sub_inv_sub_smul_one`: the joint resolvent identity.
* `Matrix.IsHermitian.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_add`: a joint bound in terms
  of the sizes of the two perturbations.
* `Matrix.IsHermitian.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_matrix` and
  `Matrix.IsHermitian.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_parameter`: fixed-parameter
  and fixed-matrix specializations.
* `Matrix.IsHermitian.norm_inv_sub_smul_one_apply_sub_inv_sub_smul_one_apply_le`: the entrywise
  joint bound.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, §2.4.
-/

public section

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
  {A B : Matrix n n 𝕜} {z w : 𝕜}

/-- The first resolvent identity for two Hermitian matrices and two non-real parameters. -/
theorem inv_sub_smul_one_sub_inv_sub_smul_one
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hz : RCLike.im z ≠ 0) (hw : RCLike.im w ≠ 0) :
    (A - z • 1)⁻¹ - (B - w • 1)⁻¹ =
      (A - z • 1)⁻¹ * ((B - A) + (z - w) • 1) * (B - w • 1)⁻¹ := by
  have h := Matrix.inv_sub_inv
    (A := A - z • 1) (B := B - w • 1)
    (iff_of_true (hA.isUnit_sub_smul_one_of_im_ne_zero hz)
      (hB.isUnit_sub_smul_one_of_im_ne_zero hw))
  convert h using 1
  congr 2
  rw [sub_smul]
  abel

/-- Joint stability of the resolvent under matrix and spectral-parameter perturbations. -/
theorem norm_inv_sub_smul_one_sub_inv_sub_smul_one_le
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hz : RCLike.im z ≠ 0) (hw : RCLike.im w ≠ 0) :
    ‖(A - z • 1)⁻¹ - (B - w • 1)⁻¹‖ ≤
      |RCLike.im z|⁻¹ * ‖(B - A) + (z - w) • 1‖ * |RCLike.im w|⁻¹ := by
  rw [hA.inv_sub_smul_one_sub_inv_sub_smul_one hB hz hw]
  calc
    ‖(A - z • 1)⁻¹ * ((B - A) + (z - w) • 1) * (B - w • 1)⁻¹‖ ≤
        ‖(A - z • 1)⁻¹‖ * ‖(B - A) + (z - w) • 1‖ * ‖(B - w • 1)⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ |RCLike.im z|⁻¹ * ‖(B - A) + (z - w) • 1‖ * |RCLike.im w|⁻¹ := by
      gcongr
      · exact hA.l2_opNorm_inv_sub_smul_one_le hz
      · exact hB.l2_opNorm_inv_sub_smul_one_le hw

/-- A joint bound in terms of the separate sizes of the two perturbations. -/
theorem norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_add
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hz : RCLike.im z ≠ 0) (hw : RCLike.im w ≠ 0) :
    ‖(A - z • 1)⁻¹ - (B - w • 1)⁻¹‖ ≤
      |RCLike.im z|⁻¹ * (‖B - A‖ + ‖z - w‖) * |RCLike.im w|⁻¹ := by
  have hone : ‖(1 : Matrix n n 𝕜)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => by simp)
  have hmid : ‖(B - A) + (z - w) • (1 : Matrix n n 𝕜)‖ ≤ ‖B - A‖ + ‖z - w‖ := by
    calc
      _ ≤ ‖B - A‖ + ‖(z - w) • (1 : Matrix n n 𝕜)‖ := norm_add_le _ _
      _ = ‖B - A‖ + ‖z - w‖ * ‖(1 : Matrix n n 𝕜)‖ := by rw [norm_smul]
      _ ≤ ‖B - A‖ + ‖z - w‖ := by nlinarith [norm_nonneg (z - w)]
  exact (hA.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le hB hz hw).trans (by
    gcongr)

/-- The joint stability bound also holds for every resolvent entry. -/
theorem norm_inv_sub_smul_one_apply_sub_inv_sub_smul_one_apply_le
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hz : RCLike.im z ≠ 0) (hw : RCLike.im w ≠ 0) (i j : n) :
    ‖(A - z • 1)⁻¹ i j - (B - w • 1)⁻¹ i j‖ ≤
      |RCLike.im z|⁻¹ * (‖B - A‖ + ‖z - w‖) * |RCLike.im w|⁻¹ := by
  exact (Matrix.norm_apply_le_l2_opNorm
    ((A - z • 1)⁻¹ - (B - w • 1)⁻¹) i j).trans
      (hA.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_add hB hz hw)

/-- At fixed spectral parameter, the resolvent is Lipschitz in the Hermitian matrix. -/
theorem norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_matrix
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hz : RCLike.im z ≠ 0) :
    ‖(A - z • 1)⁻¹ - (B - z • 1)⁻¹‖ ≤
      |RCLike.im z|⁻¹ * ‖B - A‖ * |RCLike.im z|⁻¹ := by
  simpa using hA.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le hB hz hz

/-- The first resolvent identity for a change of spectral parameter. -/
theorem inv_sub_smul_one_sub_inv_sub_smul_one_eq
    (hA : A.IsHermitian) (hz : RCLike.im z ≠ 0) (hw : RCLike.im w ≠ 0) :
    (A - z • 1)⁻¹ - (A - w • 1)⁻¹ =
      (z - w) • ((A - z • 1)⁻¹ * (A - w • 1)⁻¹) := by
  simpa [Matrix.mul_smul, Matrix.smul_mul] using
    hA.inv_sub_smul_one_sub_inv_sub_smul_one hA hz hw

/-- The resolvent is Lipschitz in the spectral parameter away from the real axis. -/
theorem norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_parameter
    (hA : A.IsHermitian) (hz : RCLike.im z ≠ 0) (hw : RCLike.im w ≠ 0) :
    ‖(A - z • 1)⁻¹ - (A - w • 1)⁻¹‖ ≤
      |RCLike.im z|⁻¹ * ‖z - w‖ * |RCLike.im w|⁻¹ := by
  simpa using hA.norm_inv_sub_smul_one_sub_inv_sub_smul_one_le_add hA hz hw

/-- At the zero matrix, `R(i) - R(-i) = 2i I`, checking the sign convention. -/
example :
    ((0 : Matrix (Fin 1) (Fin 1) ℂ) - Complex.I • 1)⁻¹ -
      ((0 : Matrix (Fin 1) (Fin 1) ℂ) - (-Complex.I) • 1)⁻¹ =
        (2 * Complex.I) • 1 := by
  have hp : ((0 : Matrix (Fin 1) (Fin 1) ℂ) - Complex.I • 1)⁻¹ = Complex.I • 1 := by
    apply Matrix.inv_eq_right_inv
    simp [smul_smul, Complex.I_mul_I]
  have hm : ((0 : Matrix (Fin 1) (Fin 1) ℂ) - (-Complex.I) • 1)⁻¹ =
      -Complex.I • 1 := by
    apply Matrix.inv_eq_right_inv
    simp [smul_smul, Complex.I_mul_I]
  rw [hp, hm, ← sub_smul]
  congr 1
  ring

end Matrix.IsHermitian
