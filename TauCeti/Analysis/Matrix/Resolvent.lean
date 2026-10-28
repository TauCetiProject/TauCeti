/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum

import Mathlib.Algebra.Group.Pi.Units

/-!
# Resolvents of Hermitian matrices

For a Hermitian matrix `A` over an `RCLike` field and a scalar `z`, the resolvent is
`R_A(z) = (A - z • 1)⁻¹`. Since `A = U * diagonal λ * Uᴴ` with `U = hA.eigenvectorUnitary` and
`λ = hA.eigenvalues` real, the shifted matrix `A - z • 1` is conjugate to the diagonal matrix with
entries `λ j - z`. Hence it is invertible exactly when `z` is not an eigenvalue, in particular
whenever `im z ≠ 0`, and then its inverse is conjugate to the diagonal matrix with entries
`(λ j - z)⁻¹`.

This file reads off the standard resolvent estimates of random matrix theory from that
diagonalization: the trace formula `trace R_A(z) = ∑ j, (λ j - z)⁻¹`, which identifies the
normalized trace of the resolvent with the Stieltjes transform of the empirical eigenvalue
distribution; the Euclidean operator norm `‖R_A(z)‖ = maxⱼ |λ j - z|⁻¹ ≤ |im z|⁻¹`; and the Ward
identity `∑ j, |R_A(z) i j| ^ 2 = im (R_A(z) i i) / im z`, with its consequence that the diagonal
entries of the resolvent lie in the upper half-plane when `z` does. The sign convention is that of
`MeasureTheory.resolventTransform`, whose scalar kernel is `(x - z)⁻¹`; Mathlib's `resolvent A z`
is `(z • 1 - A)⁻¹`, the negative of `R_A(z)`.

## Main results

* `Matrix.IsHermitian.isUnit_sub_smul_one_iff` — `A - z • 1` is invertible exactly when `z` is
  not an eigenvalue of `A`;
* `Matrix.IsHermitian.inv_sub_smul_one_eq_conjStarAlgAut_diagonal` — the spectral form of the
  resolvent;
* `Matrix.IsHermitian.trace_inv_sub_smul_one` — the trace of the resolvent is
  `∑ j, (λ j - z)⁻¹`;
* `Matrix.IsHermitian.l2_opNorm_inv_sub_smul_one_le` — `‖R_A(z)‖ ≤ |im z|⁻¹` in the Euclidean
  operator norm;
* `Matrix.IsHermitian.im_inv_sub_smul_one_apply_self` and
  `Matrix.IsHermitian.sum_norm_inv_sub_smul_one_apply_sq` — the Ward identity;
* `Matrix.IsHermitian.im_inv_sub_smul_one_apply_self_pos` — `0 < im (R_A(z) i i)` when
  `0 < im z`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.4.
* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.4.3.
* L. Erdős, H.-T. Yau, *A Dynamical Approach to Random Matrix Theory*, Courant Lecture Notes 28,
  AMS (2017), Lemma 8.3 (the Ward identity).
-/

public section

noncomputable section

open Unitary

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
  (hA : A.IsHermitian) {z : 𝕜}
include hA

/-- A shifted Hermitian matrix `A - z • 1` is conjugate, by the eigenvector unitary of `A`, to the
diagonal matrix with entries `hA.eigenvalues j - z`. -/
theorem sub_smul_one_eq_conjStarAlgAut_diagonal (z : 𝕜) :
    A - z • 1 =
      conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (diagonal fun j => (hA.eigenvalues j : 𝕜) - z) := by
  have h : (diagonal fun j => (hA.eigenvalues j : 𝕜) - z) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) - z • 1 := by
    simp [← diagonal_one, ← diagonal_sub, ← diagonal_smul, Pi.smul_def]
  rw [h, map_sub, map_smul, map_one, ← hA.spectral_theorem]

/-- A shifted Hermitian matrix `A - z • 1` is invertible exactly when `z` is not an eigenvalue
of `A`. -/
theorem isUnit_sub_smul_one_iff : IsUnit (A - z • 1) ↔ ∀ j, (hA.eigenvalues j : 𝕜) ≠ z := by
  rw [hA.sub_smul_one_eq_conjStarAlgAut_diagonal z, isUnit_map_iff, isUnit_diagonal]
  simp [Pi.isUnit_iff, sub_eq_zero]

/-- A shifted Hermitian matrix `A - z • 1` is invertible when `z` is not real. -/
theorem isUnit_sub_smul_one_of_im_ne_zero (hz : RCLike.im z ≠ 0) : IsUnit (A - z • 1) :=
  hA.isUnit_sub_smul_one_iff.2 fun j h => hz <| by simp [← h]

/-- The spectral form of the resolvent of a Hermitian matrix: away from the eigenvalues,
`(A - z • 1)⁻¹` is conjugate, by the eigenvector unitary of `A`, to the diagonal matrix with
entries `(hA.eigenvalues j - z)⁻¹`. -/
theorem inv_sub_smul_one_eq_conjStarAlgAut_diagonal (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) :
    (A - z • 1)⁻¹ =
      conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (diagonal fun j => ((hA.eigenvalues j : 𝕜) - z)⁻¹) := by
  refine inv_eq_right_inv ?_
  rw [hA.sub_smul_one_eq_conjStarAlgAut_diagonal z, ← map_mul, diagonal_mul_diagonal]
  simp [sub_ne_zero.2 (hz _)]

/-- The entrywise spectral expansion of the resolvent of a Hermitian matrix: with
`U = hA.eigenvectorUnitary` and `λ = hA.eigenvalues`,
`(A - z • 1)⁻¹ i j = ∑ k, U i k * (λ k - z)⁻¹ * conj (U j k)` away from the eigenvalues. -/
theorem inv_sub_smul_one_apply (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) (i j : n) :
    (A - z • 1)⁻¹ i j =
      ∑ k, (hA.eigenvectorUnitary : Matrix n n 𝕜) i k * ((hA.eigenvalues k : 𝕜) - z)⁻¹ *
        star ((hA.eigenvectorUnitary : Matrix n n 𝕜) j k) := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply, mul_apply]
  simp [mul_diagonal]

/-- The trace of the resolvent of a Hermitian matrix is `∑ j, (hA.eigenvalues j - z)⁻¹` away from
the eigenvalues. Divided by the size of the matrix, this is the Stieltjes transform of the
empirical distribution of the eigenvalues at `z`. -/
theorem trace_inv_sub_smul_one (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) :
    (A - z • 1)⁻¹.trace = ∑ j, ((hA.eigenvalues j : 𝕜) - z)⁻¹ := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply, trace_mul_cycle,
    star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul, trace_diagonal]

/-- The conjugate transpose of the resolvent of a Hermitian matrix at `z` is the resolvent at
`conj z`. -/
theorem conjTranspose_inv_sub_smul_one : (A - z • 1)⁻¹ᴴ = (A - star z • 1)⁻¹ := by
  rw [conjTranspose_nonsing_inv, conjTranspose_sub, hA.eq, conjTranspose_smul,
    conjTranspose_one]

/-- The **Ward identity** for the resolvent of a Hermitian matrix, in multiplicative form:
`im ((A - z • 1)⁻¹ i i) = im z * ∑ j, ‖(A - z • 1)⁻¹ i j‖ ^ 2`. No hypothesis on `z` is needed:
when `z` is an eigenvalue the nonsingular inverse is `0` and both sides vanish. -/
theorem im_inv_sub_smul_one_apply_self (i : n) :
    RCLike.im ((A - z • 1)⁻¹ i i) = RCLike.im z * ∑ j, ‖(A - z • 1)⁻¹ i j‖ ^ 2 := by
  by_cases hu : IsUnit (A - z • 1)
  swap
  · simp [nonsing_inv_apply_not_isUnit _ ((isUnit_iff_isUnit_det _).not.1 hu)]
  have hz := hA.isUnit_sub_smul_one_iff.1 hu
  set d : n → 𝕜 := fun k => ((hA.eigenvalues k : 𝕜) - z)⁻¹
  -- The imaginary part of each spectral weight is `im z` times its squared modulus.
  have him (k : n) : RCLike.im (d k) = RCLike.im z * ‖d k‖ ^ 2 := by
    simp [d, RCLike.inv_im, RCLike.normSq_eq_def', div_eq_mul_inv]
  -- `∑ j, ‖R i j‖ ^ 2` is the `(i, i)` entry of `R * Rᴴ = U * diagonal ‖d‖ ^ 2 * Uᴴ`.
  have hrow : ∑ j, ‖(A - z • 1)⁻¹ i j‖ ^ 2 =
      ∑ k, ‖(hA.eigenvectorUnitary : Matrix n n 𝕜) i k‖ ^ 2 * ‖d k‖ ^ 2 := by
    apply RCLike.ofReal_injective (K := 𝕜)
    have hRR : (A - z • 1)⁻¹ * (A - z • 1)⁻¹ᴴ =
        conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal fun k => ((‖d k‖ ^ 2 : ℝ) : 𝕜)) := by
      rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, ← star_eq_conjTranspose,
        ← map_star, ← map_mul, star_eq_conjTranspose, diagonal_conjTranspose,
        diagonal_mul_diagonal]
      congr 2
      funext k
      rw [Pi.star_apply, RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]
    have := congrFun (congrFun hRR i) i
    rw [mul_apply, conjStarAlgAut_apply, mul_apply] at this
    simp only [mul_diagonal, star_apply] at this
    push_cast
    convert this using 2 with j _ k _
    · simp [RCLike.mul_conj]
    · rw [mul_right_comm, RCLike.star_def, RCLike.mul_conj]
      push_cast
      ring
  rw [hrow, hA.inv_sub_smul_one_apply hz, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_right_comm, RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow,
    RCLike.im_ofReal_mul, him]
  ring

/-- The **Ward identity** for the resolvent of a Hermitian matrix: for `z` off the real axis,
`∑ j, ‖(A - z • 1)⁻¹ i j‖ ^ 2 = im ((A - z • 1)⁻¹ i i) / im z`. -/
theorem sum_norm_inv_sub_smul_one_apply_sq (hz : RCLike.im z ≠ 0) (i : n) :
    ∑ j, ‖(A - z • 1)⁻¹ i j‖ ^ 2 = RCLike.im ((A - z • 1)⁻¹ i i) / RCLike.im z := by
  rw [hA.im_inv_sub_smul_one_apply_self, mul_div_cancel_left₀ _ hz]

/-- The diagonal entries of the resolvent of a Hermitian matrix lie in the upper half-plane when
`z` does. -/
theorem im_inv_sub_smul_one_apply_self_pos (hz : 0 < RCLike.im z) (i : n) :
    0 < RCLike.im ((A - z • 1)⁻¹ i i) := by
  rw [hA.im_inv_sub_smul_one_apply_self]
  refine mul_pos hz <| (Finset.sum_nonneg fun j _ => by positivity).lt_of_ne' fun h => ?_
  -- Otherwise row `i` of the resolvent vanishes, contradicting `(R * (A - z • 1)) i i = 1`.
  have hrow : ∀ j, (A - z • 1)⁻¹ i j = 0 := fun j => by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).1 h j
      (Finset.mem_univ j)
  have h1 := congrFun (congrFun (nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1
    (hA.isUnit_sub_smul_one_of_im_ne_zero hz.ne'))) i) i
  simp [mul_apply, hrow] at h1

open scoped Matrix.Norms.L2Operator

/-- The Euclidean operator norm of the resolvent of a Hermitian matrix is the largest of the
`|hA.eigenvalues j - z|⁻¹`, written as the sup norm of that family, away from the eigenvalues. -/
theorem l2_opNorm_inv_sub_smul_one (hz : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z) :
    ‖(A - z • 1)⁻¹‖ = ‖fun j => ((hA.eigenvalues j : 𝕜) - z)⁻¹‖ := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply, ← coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]

/-- The resolvent bound `‖(A - z • 1)⁻¹‖ ≤ |im z|⁻¹` for a Hermitian matrix, in the Euclidean
operator norm. -/
theorem l2_opNorm_inv_sub_smul_one_le (hz : RCLike.im z ≠ 0) :
    ‖(A - z • 1)⁻¹‖ ≤ |RCLike.im z|⁻¹ := by
  have hz' : ∀ j, (hA.eigenvalues j : 𝕜) ≠ z := hA.isUnit_sub_smul_one_iff.1
    (hA.isUnit_sub_smul_one_of_im_ne_zero hz)
  rw [hA.l2_opNorm_inv_sub_smul_one hz']
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  rw [norm_inv]
  refine inv_anti₀ (abs_pos.2 hz) ?_
  simpa using RCLike.abs_im_le_norm ((hA.eigenvalues j : 𝕜) - z)

end Matrix.IsHermitian
