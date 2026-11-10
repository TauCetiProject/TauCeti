/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive

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

Eigen-coordinates also bound the pseudo-inverse of `B` along eigenvectors of a matrix below it in
the Loewner order: if `0 ≤ A ≤ B` and `u` is a unit eigenvector of `A` with eigenvalue `a > 0`,
then `a ⟪u, B⁻¹ u⟫ ≤ 1`. This bound underlies the trace inequality `Tr (A log A) ≤ Tr (A log B)`
for `0 ≤ A ≤ B`.

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
  nonzero eigenvalues, counted with multiplicity;
* `Matrix.IsHermitian.eigenvalues_eq_zero_of_inner_ne_zero` — if the kernel of `B` lies in the
  kernel of a Hermitian `A`, an eigenvector of `B` with eigenvalue zero is orthogonal to every
  eigenvector of `A` with nonzero eigenvalue.
* `Matrix.PosSemidef.eigenvalues_mul_sum_inv_mul_le_one` — if `0 ≤ A ≤ B`, a unit eigenvector `u`
  of `A` with eigenvalue `a > 0` satisfies `a ⟪u, B⁻¹ u⟫ ≤ 1` for the pseudo-inverse of `B`.

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
  rw [conjStarAlgAut_apply, Matrix.mul_apply]
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

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι 𝕜}

/-- If the kernel of `B` lies in the kernel of the Hermitian matrix `A`, then an eigenvector of `B`
with eigenvalue zero is orthogonal to every eigenvector of `A` with nonzero eigenvalue: a nonzero
overlap forces the eigenvalue of `A` to vanish. -/
theorem eigenvalues_eq_zero_of_inner_ne_zero (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : LinearMap.ker B.mulVecLin ≤ LinearMap.ker A.mulVecLin) {i j : ι}
    (hij : ⟪hA.eigenvectorBasis i, hB.eigenvectorBasis j⟫_𝕜 ≠ 0) (hj : hB.eigenvalues j = 0) :
    hA.eigenvalues i = 0 := by
  have hker : A *ᵥ ⇑(hB.eigenvectorBasis j) = 0 := by
    have hv : B *ᵥ ⇑(hB.eigenvectorBasis j) = 0 := by
      rw [hB.mulVec_eigenvectorBasis, hj, zero_smul]
    exact h hv
  have hsymm := isSymmetric_toEuclideanLin_iff.mpr hA (hA.eigenvectorBasis i)
    (hB.eigenvectorBasis j)
  simp only [toLpLin_apply, hA.mulVec_eigenvectorBasis, hker, WithLp.toLp_zero, inner_zero_right,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.toLp_smul, WithLp.toLp_ofLp, inner_smul_left,
    RCLike.conj_ofReal, mul_eq_zero, RCLike.ofReal_eq_zero] at hsymm
  exact hsymm.resolve_right hij

end Matrix.IsHermitian

namespace Matrix

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Let `0 ≤ A ≤ B`, that is `A` and `B - A` positive semidefinite, let `u` be a unit eigenvector
of `A` with eigenvalue `a > 0`, and let `B` have eigenvalues `bⱼ` and orthonormal eigenvectors `vⱼ`.
Then `a ∑ⱼ bⱼ⁻¹ ‖⟪u, vⱼ⟫‖² ≤ 1`, that is `a ⟪u, B⁻¹ u⟫ ≤ 1` for the pseudo-inverse `B⁻¹` of `B`,
with the convention `0⁻¹ = 0`. -/
theorem PosSemidef.eigenvalues_mul_sum_inv_mul_le_one {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) (hB : B.IsHermitian) {i : ι}
    (hi : 0 < hA.1.eigenvalues i) :
    hA.1.eigenvalues i * ∑ j, (hB.eigenvalues j)⁻¹ *
      ‖⟪hA.1.eigenvectorBasis i, hB.eigenvectorBasis j⟫_𝕜‖ ^ 2 ≤ 1 := by
  set a := hA.1.eigenvalues i
  set u := hA.1.eigenvectorBasis i
  set v := hB.eigenvectorBasis
  set b := hB.eigenvalues
  set c : ι → 𝕜 := fun j ↦ ⟪v j, u⟫_𝕜
  set s : ℝ := ∑ j, (b j)⁻¹ * ‖⟪u, v j⟫_𝕜‖ ^ 2
  have hb (j : ι) : 0 ≤ b j := by simpa using (hA.add hBA).eigenvalues_nonneg j
  have hcn (j : ι) : ‖c j‖ = ‖⟪u, v j⟫_𝕜‖ := by
    simp only [c]
    rw [← inner_conj_symm, RCLike.norm_conj]
  -- The test vector `y = B⁻¹ u`, written in the eigenbasis of `B`, has `⟪y, B y⟫ = ⟪u, y⟫ = s`.
  set y : EuclideanSpace 𝕜 ι := ∑ j, (((b j)⁻¹ : ℝ) * c j : 𝕜) • v j
  have hyBy : ⟪y, B.toEuclideanLin y⟫_𝕜 = s := by
    rw [hB.inner_toEuclideanLin_sum_smul_eigenvectorBasis]
    have key (j : ι) :
        b j * ‖(((b j)⁻¹ : ℝ) : 𝕜) * c j‖ ^ 2 = (b j)⁻¹ * ‖⟪u, v j⟫_𝕜‖ ^ 2 := by
      rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (inv_nonneg.2 (hb j)), hcn]
      by_cases h : b j = 0
      · simp [h]
      · field_simp
    simp only [s, b, ← key, RCLike.ofReal_sum, RCLike.ofReal_mul, RCLike.ofReal_pow]
  have huy : ⟪u, y⟫_𝕜 = s := by
    conv_lhs => rw [← v.sum_repr' u]
    rw [v.orthonormal.inner_sum]
    simp only [s]
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_left_comm, RCLike.conj_mul, hcn]
  have hTu : A.toEuclideanLin u = (a : 𝕜) • u := by
    rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [u, a, toLpLin_apply, hA.1.mulVec_eigenvectorBasis]
  have huu : ⟪u, u⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hA.1.eigenvectorBasis.orthonormal.1 i]
    simp
  have hTyu : ⟪A.toEuclideanLin y, u⟫_𝕜 = a * s := by
    rw [isSymmetric_toEuclideanLin_iff.mpr hA.1, hTu, inner_smul_right, ← inner_conj_symm, huy,
      RCLike.conj_ofReal]
  -- Positivity of `B - A` at `y` gives `re ⟪A y, y⟫ ≤ s`.
  have hyAy : RCLike.re ⟪A.toEuclideanLin y, y⟫_𝕜 ≤ s := by
    have h := (isPositive_toEuclideanLin_iff.2 hBA).re_inner_nonneg_left y
    rw [map_sub, LinearMap.sub_apply, inner_sub_left, map_sub, sub_nonneg] at h
    rwa [inner_re_symm (𝕜 := 𝕜) (B.toEuclideanLin y), hyBy, RCLike.ofReal_re] at h
  -- Positivity of `A` at `u - a y` gives `0 ≤ a - 2 a² s + a² re ⟪A y, y⟫ ≤ a - a² s`.
  have h := (isPositive_toEuclideanLin_iff.2 hA).re_inner_nonneg_left (u - (a : 𝕜) • y)
  simp only [map_sub, map_smul, hTu, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, huu, huy, hTyu, RCLike.conj_ofReal, RCLike.re_ofReal_mul, mul_one,
    RCLike.ofReal_re] at h
  nlinarith [mul_le_mul_of_nonneg_left hyAy (mul_nonneg hi.le hi.le)]

end Matrix

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
