/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Resolvents of Hermitian matrices

For a square matrix `A` and a scalar `z` outside its spectrum, the resolvent of `A` at `z` is the
matrix `R_A(z) = (A - z • 1)⁻¹`. This is the sign convention of
`MeasureTheory.resolventTransform`, whose kernel at a point `x` is `(x - z)⁻¹`, so that the
normalized trace of `R_A(z)` is the resolvent transform of the empirical spectral measure of `A`.
Mathlib's `resolvent A z` is `(z • 1 - A)⁻¹`, the negative of `R_A(z)`.

For a Hermitian matrix `A` with eigenvector unitary `U` and eigenvalues `λ`, the resolvent is
diagonal in the eigenbasis: `R_A(z) = U * diagonal (fun j ↦ (λ j - z)⁻¹) * Uᴴ`. This file reads
off its entries, its trace and its Euclidean operator norm. For a non-real `z` it proves the
resolvent bound `‖R_A(z)‖ ≤ |Im z|⁻¹` and the Ward identity
`∑ j, ‖R_A(z) i j‖ ^ 2 = Im (R_A(z) i i) / Im z`, whose consequence is that the diagonal entries
of the resolvent lie in the upper half-plane when `z` does. These deterministic facts drive the
resolvent method for global spectral laws of random matrices: the bound keeps the resolvent and
its entries under control in the upper half-plane, and the Ward identity converts sums of squared
entries back into diagonal entries. The first resolvent identity is Mathlib's
`Matrix.inv_sub_inv`.

## Main results

* `Matrix.IsHermitian.inv_sub_smul_one_eq_conjStarAlgAut_diagonal` — the resolvent of a Hermitian
  matrix is conjugate, by the eigenvector unitary, to `diagonal fun j ↦ (λ j - z)⁻¹`;
* `Matrix.IsHermitian.inv_sub_smul_one_apply` — the entrywise spectral expansion of the
  resolvent;
* `Matrix.IsHermitian.trace_inv_sub_smul_one` — its trace is `∑ j, (λ j - z)⁻¹`;
* `Matrix.IsHermitian.l2_opNorm_inv_sub_smul_one` — its Euclidean operator norm is the largest of
  the moduli `|λ j - z|⁻¹`;
* `Matrix.IsHermitian.conjTranspose_inv_sub_smul_one` — the conjugate transpose of the resolvent
  at `z` is the resolvent at `conj z`;
* `Matrix.IsHermitian.notMem_spectrum_of_im_ne_zero` — a non-real scalar lies outside the spectrum
  of a Hermitian matrix;
* `Matrix.IsHermitian.l2_opNorm_inv_sub_smul_one_le` — the resolvent bound
  `‖(A - z • 1)⁻¹‖ ≤ |Im z|⁻¹`;
* `Matrix.IsHermitian.im_inv_sub_smul_one_apply_self` and
  `Matrix.IsHermitian.sum_norm_inv_sub_smul_one_apply_sq` — the Ward identity;
* `Matrix.IsHermitian.im_inv_sub_smul_one_apply_self_pos` — `0 < Im (R_A(z) i i)` when
  `0 < Im z`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.4.
* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.4.3.
* L. Erdős, H.-T. Yau, *A Dynamical Approach to Random Matrix Theory*, Courant Lecture Notes 28,
  AMS (2017), Lemma 8.3 (the Ward identity).
-/

public section

noncomputable section

open Unitary
open scoped ComplexConjugate

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
  (hA : A.IsHermitian)
include hA

/-- The shifted matrix `A - z • 1` of a Hermitian matrix is conjugate, by the eigenvector unitary
of `A`, to the diagonal matrix with entries `hA.eigenvalues j - z`. -/
theorem sub_smul_one_eq_conjStarAlgAut_diagonal (z : 𝕜) :
    A - z • 1 =
      conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal fun j => (hA.eigenvalues j : 𝕜) - z) := by
  have h : (diagonal fun j => (hA.eigenvalues j : 𝕜) - z) =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) - z • 1 := by
    simp [← diagonal_one, ← diagonal_sub, ← diagonal_smul, Pi.smul_def]
  rw [h, map_sub, map_smul, map_one, ← hA.spectral_theorem]

/-- Off the spectrum, the resolvent `(A - z • 1)⁻¹` of a Hermitian matrix is conjugate, by the
eigenvector unitary of `A`, to the diagonal matrix with entries `(hA.eigenvalues j - z)⁻¹`. -/
theorem inv_sub_smul_one_eq_conjStarAlgAut_diagonal {z : 𝕜} (hz : z ∉ spectrum 𝕜 A) :
    (A - z • 1)⁻¹ =
      conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
        (diagonal fun j => ((hA.eigenvalues j : 𝕜) - z)⁻¹) := by
  have hne (j : n) : (hA.eigenvalues j : 𝕜) - z ≠ 0 := by
    rw [sub_ne_zero]
    rintro rfl
    exact hz (hA.spectrum_eq_image_range ▸ Set.mem_image_of_mem _ (Set.mem_range_self j))
  refine inv_eq_right_inv ?_
  rw [hA.sub_smul_one_eq_conjStarAlgAut_diagonal, ← map_mul, diagonal_mul_diagonal]
  simp [mul_inv_cancel₀ (hne _)]

/-- Off the spectrum, the trace of the resolvent of a Hermitian matrix is
`∑ j, (hA.eigenvalues j - z)⁻¹`. -/
theorem trace_inv_sub_smul_one {z : 𝕜} (hz : z ∉ spectrum 𝕜 A) :
    (A - z • 1)⁻¹.trace = ∑ j, ((hA.eigenvalues j : 𝕜) - z)⁻¹ := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply, trace_mul_cycle,
    star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul, trace_diagonal]

open scoped Matrix.Norms.L2Operator in
/-- Off the spectrum, the Euclidean operator norm of the resolvent of a Hermitian matrix is the
largest of the moduli `‖hA.eigenvalues j - z‖⁻¹`, written as the sup norm of that family. -/
theorem l2_opNorm_inv_sub_smul_one {z : 𝕜} (hz : z ∉ spectrum 𝕜 A) :
    ‖(A - z • 1)⁻¹‖ = ‖fun j => ((hA.eigenvalues j : 𝕜) - z)⁻¹‖ := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply, ← coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]

/-- The entrywise spectral expansion of the resolvent of a Hermitian matrix: with
`U = hA.eigenvectorUnitary` and `λ = hA.eigenvalues`, off the spectrum
`(A - z • 1)⁻¹ i j = ∑ k, U i k * (λ k - z)⁻¹ * conj (U j k)`. -/
theorem inv_sub_smul_one_apply {z : 𝕜} (hz : z ∉ spectrum 𝕜 A) (i j : n) :
    (A - z • 1)⁻¹ i j =
      ∑ k, (hA.eigenvectorUnitary : Matrix n n 𝕜) i k * ((hA.eigenvalues k : 𝕜) - z)⁻¹ *
        star ((hA.eigenvectorUnitary : Matrix n n 𝕜) j k) := by
  rw [hA.inv_sub_smul_one_eq_conjStarAlgAut_diagonal hz, conjStarAlgAut_apply, mul_apply]
  simp [mul_diagonal]

/-- The conjugate transpose of the resolvent of a Hermitian matrix at `z` is the resolvent at
`conj z`. -/
theorem conjTranspose_inv_sub_smul_one (z : 𝕜) : (A - z • 1)⁻¹ᴴ = (A - conj z • 1)⁻¹ := by
  rw [conjTranspose_nonsing_inv, conjTranspose_sub, hA.eq, conjTranspose_smul,
    conjTranspose_one, RCLike.star_def]

/-- A scalar with nonzero imaginary part lies outside the spectrum of a Hermitian matrix, whose
eigenvalues are real. Unlike `IsSelfAdjoint.im_eq_zero_of_mem_spectrum`, this needs no
C⋆-algebra structure on `Matrix n n 𝕜`. -/
theorem notMem_spectrum_of_im_ne_zero {z : 𝕜} (hz : RCLike.im z ≠ 0) : z ∉ spectrum 𝕜 A := by
  rw [hA.spectrum_eq_image_range]
  rintro ⟨_, ⟨j, rfl⟩, rfl⟩
  exact hz (by simp)

/-- A shifted Hermitian matrix `A - z • 1` is invertible when `z` is not real. -/
theorem isUnit_sub_smul_one_of_im_ne_zero {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    IsUnit (A - z • 1) := by
  simpa [Algebra.algebraMap_eq_smul_one] using
    (spectrum.notMem_iff.1 (hA.notMem_spectrum_of_im_ne_zero hz)).neg

open scoped Matrix.Norms.L2Operator in
/-- **Resolvent bound.** For a Hermitian matrix and a non-real `z`, the Euclidean operator norm of
the resolvent `(A - z • 1)⁻¹` is at most `|Im z|⁻¹`. -/
theorem l2_opNorm_inv_sub_smul_one_le {z : 𝕜} (hz : RCLike.im z ≠ 0) :
    ‖(A - z • 1)⁻¹‖ ≤ |RCLike.im z|⁻¹ := by
  rw [hA.l2_opNorm_inv_sub_smul_one (hA.notMem_spectrum_of_im_ne_zero hz)]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [norm_inv]
  refine inv_anti₀ (abs_pos.2 hz) ?_
  simpa using RCLike.abs_im_le_norm ((hA.eigenvalues j : 𝕜) - z)

/-- The **Ward identity** for the resolvent `R = (A - z • 1)⁻¹` of a Hermitian matrix, in
multiplicative form: `Im (R i i) = Im z * ∑ j, ‖R i j‖ ^ 2`. No hypothesis on `z` is needed: when
`A - z • 1` is singular the nonsingular inverse is `0` and both sides vanish. -/
theorem im_inv_sub_smul_one_apply_self (z : 𝕜) (i : n) :
    RCLike.im ((A - z • 1)⁻¹ i i) = RCLike.im z * ∑ j, ‖(A - z • 1)⁻¹ i j‖ ^ 2 := by
  by_cases hu : IsUnit (A - z • 1)
  swap
  · simp [nonsing_inv_apply_not_isUnit _ ((isUnit_iff_isUnit_det _).not.1 hu)]
  have hu' : IsUnit (A - conj z • 1) := by
    simpa [star_eq_conjTranspose, conjTranspose_sub, hA.eq, conjTranspose_smul, RCLike.star_def]
      using hu.star
  -- The first resolvent identity at `z` and `conj z`.
  have hres : (A - z • 1)⁻¹ - (A - z • 1)⁻¹ᴴ = (z - conj z) • ((A - z • 1)⁻¹ * (A - z • 1)⁻¹ᴴ) := by
    rw [hA.conjTranspose_inv_sub_smul_one, inv_sub_inv (iff_of_true hu hu'),
      sub_sub_sub_cancel_left, ← sub_smul, mul_smul_one, smul_mul_assoc]
  have key := congr(RCLike.im ($hres i i))
  simp only [sub_apply, smul_apply, conjTranspose_apply, mul_apply, smul_eq_mul, RCLike.star_def,
    RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_sum, RCLike.im_mul_ofReal, map_sub,
    RCLike.conj_im] at key
  linarith

/-- **Ward identity.** For a Hermitian matrix and a non-real `z`, the squared moduli of the entries
in a row of the resolvent `R = (A - z • 1)⁻¹` sum to `Im (R i i) / Im z`. -/
theorem sum_norm_inv_sub_smul_one_apply_sq {z : 𝕜} (hz : RCLike.im z ≠ 0) (i : n) :
    ∑ j, ‖(A - z • 1)⁻¹ i j‖ ^ 2 = RCLike.im ((A - z • 1)⁻¹ i i) / RCLike.im z := by
  rw [hA.im_inv_sub_smul_one_apply_self, mul_div_cancel_left₀ _ hz]

/-- The diagonal entries of the resolvent of a Hermitian matrix lie in the upper half-plane when
`z` does. -/
theorem im_inv_sub_smul_one_apply_self_pos {z : 𝕜} (hz : 0 < RCLike.im z) (i : n) :
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

end Matrix.IsHermitian
