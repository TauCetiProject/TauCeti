/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef

/-!
# Eigen-coordinates and eigenvalue multisets of a Hermitian matrix

Let `B` be a Hermitian matrix over an `RCLike` field with orthonormal eigenvector basis
`hB.eigenvectorBasis` and real eigenvalues `hB.eigenvalues`. Writing `U` for the eigenvector
unitary `hB.eigenvectorUnitary`, whose columns are the eigenvectors, the spectral theorem
`B = U * diagonal λ * Uᴴ` reads entrywise as `B i j = ∑ k, λ k * U i k * conj (U j k)`.
This file also reads four quantities off the eigen-coordinates: the quadratic form
`x ↦ ⟪x, B x⟫`, which becomes a weighted sum of squared moduli, the diagonalization and the
determinant of the pencil `1 - c • B`, which are read off the scalars `1 - c * hB.eigenvalues j`,
and the traces of natural powers of `B`, which are sums of powers of the eigenvalues. The
pencil is diagonal in the eigenbasis for any scalar `c`; only its positive definiteness asks
for a real one.

These are the spectral facts behind the moment-generating function of a Gaussian quadratic form,
whose exponential-integrability domain is a positive-definiteness condition on such a pencil and
whose value is a power of its determinant.

The eigenvalues of a Hermitian matrix, counted with multiplicity, are the roots of its
characteristic polynomial. So if `A.charpoly = X ^ k * B.charpoly` for Hermitian `A` and `B`,
possibly of different sizes, then the eigenvalues of `A` are those of `B` together with `k`
zeros. Mathlib's `Matrix.charpoly_mul_comm_of_le` gives this relation for the two Gram matrices
`Aᴴ * A` and `A * Aᴴ` of a rectangular matrix, which therefore have the same nonzero eigenvalues.
This is how the spectra of sample covariance matrices `X * Xᴴ` and of their companions `Xᴴ * X`
are compared.

## Main results

* `Matrix.IsHermitian.apply_eq_sum_eigenvalues` — the entrywise spectral expansion
  `B i j = ∑ k, λ k * U i k * conj (U j k)`;
* `Matrix.IsHermitian.inner_toEuclideanLin_sum_smul_eigenvectorBasis` — the quadratic form of
  `B` at `∑ j, c j • b j` is `∑ j, hB.eigenvalues j * ‖c j‖ ^ 2`;
* `Matrix.IsHermitian.posDef_one_sub_smul_iff` — `1 - c • B` is positive definite exactly when
  `c * hB.eigenvalues j < 1` for every `j`;
* `Matrix.IsHermitian.eventually_posDef_one_sub_smul` — `1 - c • B` is positive definite for all
  real `c` near `0`;
* `Matrix.IsHermitian.one_sub_smul_eq_conjStarAlgAut_diagonal` and
  `Matrix.IsHermitian.det_one_sub_smul` — `1 - c • B` is conjugate to a diagonal matrix, and its
  determinant is `∏ j, (1 - c * hB.eigenvalues j)`;
* `Matrix.IsHermitian.trace_pow_eq_sum_eigenvalues_pow` — the trace of `B ^ k` is
  `∑ j, hB.eigenvalues j ^ k` for every natural `k`;
* `Matrix.IsHermitian.map_eigenvalues_of_charpoly_eq_X_pow_mul` — if
  `A.charpoly = X ^ k * B.charpoly`, the eigenvalue multiset of `A` is that of `B` plus `k`
  zeros;
* `Matrix.filter_map_eigenvalues_conjTranspose_mul_self` — `Aᴴ * A` and `A * Aᴴ` have the same
  nonzero eigenvalues, counted with multiplicity.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 1.3.22 (`AB` and `BA` have the same nonzero eigenvalues).
-/

public section

noncomputable section

open Unitary
open scoped InnerProductSpace

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι 𝕜}
  (hB : B.IsHermitian)
include hB

/-- The entrywise spectral expansion of a Hermitian matrix: with `U = hB.eigenvectorUnitary`,
`B i j = ∑ k, λ k * U i k * conj (U j k)`, where `λ = hB.eigenvalues`. -/
theorem apply_eq_sum_eigenvalues (i j : ι) :
    B i j = ∑ k, (hB.eigenvalues k : 𝕜) * (hB.eigenvectorUnitary : Matrix ι ι 𝕜) i k *
      star ((hB.eigenvectorUnitary : Matrix ι ι 𝕜) j k) := by
  conv_lhs => rw [hB.spectral_theorem]
  rw [conjStarAlgAut_apply, mul_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_diagonal, star_apply, Function.comp_apply]
  ring

/-- In the eigen-coordinates of a Hermitian matrix, its quadratic form is the sum of the squared
moduli of the coordinates weighted by the eigenvalues. -/
theorem inner_toEuclideanLin_sum_smul_eigenvectorBasis (c : ι → 𝕜) :
    ⟪∑ j, c j • hB.eigenvectorBasis j,
      B.toEuclideanLin (∑ j, c j • hB.eigenvectorBasis j)⟫_𝕜 =
      ∑ j, (hB.eigenvalues j : 𝕜) * (‖c j‖ : 𝕜) ^ 2 := by
  have hb (j : ι) : B.toEuclideanLin (hB.eigenvectorBasis j) =
      (hB.eigenvalues j : 𝕜) • hB.eigenvectorBasis j := by
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [toLpLin_apply, hB.mulVec_eigenvectorBasis]
  rw [map_sum]
  simp_rw [map_smul, hb, smul_smul]
  rw [hB.eigenvectorBasis.orthonormal.inner_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← mul_assoc, RCLike.conj_mul]
  ring

/-- The pencil `1 - c • B` is conjugate, by the eigenvector unitary of `B`, to the diagonal matrix
with entries `1 - c * hB.eigenvalues j`. -/
theorem one_sub_smul_eq_conjStarAlgAut_diagonal (c : 𝕜) :
    1 - c • B =
      conjStarAlgAut 𝕜 _ hB.eigenvectorUnitary
        (diagonal fun j => 1 - c * (hB.eigenvalues j : 𝕜)) := by
  have h : (diagonal fun j => 1 - c * (hB.eigenvalues j : 𝕜)) =
      1 - c • diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
    simp [← diagonal_one, ← diagonal_sub, ← diagonal_smul, Pi.smul_def]
  rw [h, map_sub, map_one, map_smul, ← hB.spectral_theorem]

open scoped ComplexOrder in
/-- The pencil `1 - c • B` is positive definite exactly when `c * hB.eigenvalues j < 1` for every
eigenvalue. -/
theorem posDef_one_sub_smul_iff (c : ℝ) :
    (1 - c • B).PosDef ↔ ∀ j, c * hB.eigenvalues j < 1 := by
  have hentry (j : ι) : 1 - (c : 𝕜) * (hB.eigenvalues j : 𝕜) =
      ((1 - c * hB.eigenvalues j : ℝ) : 𝕜) := by push_cast; ring
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜),
    hB.one_sub_smul_eq_conjStarAlgAut_diagonal (c : 𝕜), conjStarAlgAut_apply,
    IsUnit.posDef_star_right_conjugate_iff isUnit_coe, posDef_diagonal_iff]
  simp only [hentry, RCLike.ofReal_pos, sub_pos]

/-- The determinant of the pencil `1 - c • B` is the product of `1 - c * hB.eigenvalues j` over
the eigenvalues. -/
theorem det_one_sub_smul (c : 𝕜) :
    (1 - c • B).det = ∏ j, (1 - c * (hB.eigenvalues j : 𝕜)) := by
  rw [hB.one_sub_smul_eq_conjStarAlgAut_diagonal c, conjStarAlgAut_apply, det_mul, det_mul,
    mul_right_comm, ← det_mul, mul_star_self_of_mem hB.eigenvectorUnitary.2, det_one,
    one_mul, det_diagonal]

/-- The trace of a natural power of a Hermitian matrix is the sum of the corresponding
powers of its eigenvalues. -/
theorem trace_pow_eq_sum_eigenvalues_pow (k : ℕ) :
    (B ^ k).trace = ∑ j, (hB.eigenvalues j : 𝕜) ^ k := by
  conv_lhs => rw [hB.spectral_theorem, ← map_pow]
  rw [conjStarAlgAut_apply, trace_mul_cycle, star_mul_self_of_mem hB.eigenvectorUnitary.2,
    one_mul, diagonal_pow, trace_diagonal]
  rfl

end Matrix.IsHermitian

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Finite ι] [DecidableEq ι] {B : Matrix ι ι 𝕜}

open scoped ComplexOrder Topology in
/-- For all real `c` close enough to `0`, the pencil `1 - c • B` is positive definite. -/
theorem eventually_posDef_one_sub_smul (hB : B.IsHermitian) :
    ∀ᶠ c in 𝓝 (0 : ℝ), (1 - c • B).PosDef := by
  have := Fintype.ofFinite ι
  simp only [hB.posDef_one_sub_smul_iff]
  exact Filter.eventually_all.2 fun j =>
    ((continuous_id.mul continuous_const).tendsto' 0 0 (zero_mul _)).eventually
      (gt_mem_nhds zero_lt_one)

end Matrix.IsHermitian

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

open Polynomial in
/-- If the characteristic polynomial of a Hermitian matrix `A` is `X ^ k` times that of a
Hermitian matrix `B`, then the eigenvalues of `A`, counted with multiplicity, are those of `B`
together with `k` additional zeros. -/
theorem IsHermitian.map_eigenvalues_of_charpoly_eq_X_pow_mul {A : Matrix ι ι 𝕜}
    {B : Matrix κ κ 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) {k : ℕ}
    (h : A.charpoly = X ^ k * B.charpoly) :
    Finset.univ.val.map hA.eigenvalues =
      Multiset.replicate k 0 + Finset.univ.val.map hB.eigenvalues := by
  apply Multiset.map_injective (RCLike.ofReal_injective (K := 𝕜))
  rw [Multiset.map_map, ← hA.roots_charpoly_eq_eigenvalues, h,
    roots_mul ((monic_X_pow k).mul B.charpoly_monic).ne_zero, roots_X_pow,
    hB.roots_charpoly_eq_eigenvalues]
  simp [Multiset.map_map, Multiset.nsmul_singleton]

open Polynomial in
/-- If the characteristic polynomial of a Hermitian matrix `A` is `X ^ k` times that of a
Hermitian matrix `B`, then summing a function over the eigenvalues of `A` gives its sum over the
eigenvalues of `B` plus `k` copies of its value at `0`. -/
theorem IsHermitian.sum_comp_eigenvalues_of_charpoly_eq_X_pow_mul {M : Type*} [AddCommMonoid M]
    {A : Matrix ι ι 𝕜} {B : Matrix κ κ 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) {k : ℕ}
    (h : A.charpoly = X ^ k * B.charpoly) (g : ℝ → M) :
    ∑ i, g (hA.eigenvalues i) = k • g 0 + ∑ j, g (hB.eigenvalues j) := by
  have := congrArg (fun s => (s.map g).sum) (hA.map_eigenvalues_of_charpoly_eq_X_pow_mul hB h)
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate, Multiset.sum_replicate,
    Multiset.map_map, Function.comp_def] at this
  rwa [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]

/-- `Aᴴ * A` and `A * Aᴴ` have the same nonzero eigenvalues, counted with multiplicity. -/
theorem filter_map_eigenvalues_conjTranspose_mul_self (A : Matrix ι κ 𝕜) :
    (Finset.univ.val.map (isHermitian_conjTranspose_mul_self A).eigenvalues).filter (· ≠ 0) =
      (Finset.univ.val.map (isHermitian_mul_conjTranspose_self A).eigenvalues).filter
        (· ≠ 0) := by
  rcases le_total (Fintype.card ι) (Fintype.card κ) with hle | hle
  · rw [IsHermitian.map_eigenvalues_of_charpoly_eq_X_pow_mul _
      (isHermitian_mul_conjTranspose_self A) (charpoly_mul_comm_of_le Aᴴ A hle)]
    simp +contextual [Multiset.mem_replicate]
  · rw [IsHermitian.map_eigenvalues_of_charpoly_eq_X_pow_mul
      (isHermitian_mul_conjTranspose_self A) (isHermitian_conjTranspose_mul_self A)
      (charpoly_mul_comm_of_le A Aᴴ hle)]
    simp +contextual [Multiset.mem_replicate]

end Matrix
