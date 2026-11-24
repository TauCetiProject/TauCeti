/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.InnerProductSpace.Positive
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.LinearAlgebra.Matrix.Charpoly.Diagonal

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
are compared. Since unitary conjugation preserves the characteristic polynomial, a decreasing real
diagonal is recovered from the ordered eigenvalues of any of its unitary conjugates; this is the
ordered diagonal coordinate in the spectral change of variables.

Eigen-coordinates also bound the pseudo-inverse of `B` along eigenvectors of a matrix below it in
the Loewner order: if `0 ≤ A ≤ B` and `u` is a unit eigenvector of `A` with eigenvalue `a`,
then `a ⟪u, B⁻¹ u⟫ ≤ 1`. This bound underlies the trace inequality `Tr (A log A) ≤ Tr (A log B)`
for `0 ≤ A ≤ B`.

A unit eigenvector of a simple eigenvalue is a unimodular multiple of the matching column of `U`,
so the quadratic form of any matrix `C` at it is a diagonal entry of `Uᴴ C U`. This identifies the
first variation of a simple eigenvalue. The adjugate of `λ k₀ - B` multiplies an eigenvector for
`λ k₀` by the product of the gaps `λ k₀ - λ k` to the other eigenvalues, which is nonzero exactly
when `λ k₀` is simple; this gives differentiable curves of eigenvectors.

Over `ℝ`, where the conjugate transpose is the transpose, the spectral theorem diagonalizes a
symmetric matrix by an orthogonal one: `X = O * diagonal d * O⁻¹` with `O⁻¹ = Oᵀ`.

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
* `Matrix.eigenvalues₀_conjStarAlgAut_diagonal` — the ordered eigenvalues of a unitary conjugate
  of a decreasing real diagonal are its diagonal entries;
* `Matrix.IsHermitian.eigenvalues_eq_zero_of_inner_ne_zero` — if the kernel of `B` lies in the
  kernel of a Hermitian `A`, an eigenvector of `B` with eigenvalue zero is orthogonal to every
  eigenvector of `A` with nonzero eigenvalue.
* `Matrix.PosSemidef.eigenvalues_mul_sum_inv_mul_le_one` — if `0 ≤ A ≤ B`, a unit eigenvector `u`
  of `A` with eigenvalue `a` satisfies `a ⟪u, B⁻¹ u⟫ ≤ 1` for the pseudo-inverse of `B`;
* `Matrix.IsHermitian.star_eigenvectorUnitary_mul_mul_eigenvectorUnitary` — `Uᴴ B U` is the
  diagonal matrix of eigenvalues;
* `Matrix.IsHermitian.star_eigenvectorUnitary_mulVec_apply_eq_zero` — the eigen-coordinates of an
  eigenvector for `μ` vanish off the indices with eigenvalue `μ`;
* `Matrix.IsHermitian.adjugate_scalar_sub_mulVec_eq_prod_smul` — the adjugate of `λ k₀ - B`
  multiplies an eigenvector for `λ k₀` by the product of the gaps `λ k₀ - λ k`, `k ≠ k₀`;
* `Matrix.IsHermitian.star_dotProduct_mulVec_eq_of_simple` — a unit eigenvector `u` of a simple
  eigenvalue `λ k₀` satisfies `⟪u, C u⟫ = (Uᴴ C U) k₀ k₀` for every matrix `C`;
* `Matrix.IsSymm.exists_orthogonal_diagonal` — a real symmetric matrix is `O * diagonal d * O⁻¹`
  for an invertible `O` with `O⁻¹ = Oᵀ`;
* `Matrix.IsHermitian.eigenvalues_apply_equivOfCardEq` and
  `Matrix.IsHermitian.eigenvalues_ne_eigenvalues_equivOfCardEq` — the canonical equivalence
  `Fin (Fintype.card ι) ≃ ι` reindexes the sorted eigenvalues `hB.eigenvalues₀` as the
  matrix-indexed eigenvalues `hB.eigenvalues`, so a simple sorted eigenvalue is simple as a
  matrix-indexed one;
* `Matrix.IsHermitian.prod_comp_eigenvalues` and `Matrix.IsHermitian.sum_comp_eigenvalues` — a
  product or sum of a function over the matrix-indexed eigenvalues is the same over the sorted
  eigenvalues.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 1.3.22 (`AB` and `BA` have the same nonzero eigenvalues).
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.1 (ordered diagonal coordinate of the spectral change of variables).
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

/-- The eigenvectors of a Hermitian matrix are eigenvectors of the associated linear map on
Euclidean space. -/
@[simp]
theorem toEuclideanLin_eigenvectorBasis (j : ι) :
    B.toEuclideanLin (hB.eigenvectorBasis j) = (hB.eigenvalues j : 𝕜) • hB.eigenvectorBasis j := by
  rw [← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  simp [toLpLin_apply, hB.mulVec_eigenvectorBasis]

/-- In the eigen-coordinates of a Hermitian matrix, its quadratic form is the sum of the squared
moduli of the coordinates weighted by the eigenvalues. -/
theorem inner_toEuclideanLin_sum_smul_eigenvectorBasis (c : ι → 𝕜) :
    ⟪∑ j, c j • hB.eigenvectorBasis j,
      B.toEuclideanLin (∑ j, c j • hB.eigenvectorBasis j)⟫_𝕜 =
      ∑ j, (hB.eigenvalues j : 𝕜) * (‖c j‖ : 𝕜) ^ 2 := by
  rw [map_sum]
  simp_rw [map_smul, hB.toEuclideanLin_eigenvectorBasis, smul_smul]
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
    mul_right_comm, ← det_mul, mul_star_self_of_mem hB.eigenvectorUnitary.property, det_one,
    one_mul, det_diagonal]

/-- The trace of a natural power of a Hermitian matrix is the sum of the corresponding
powers of its eigenvalues. -/
theorem trace_pow_eq_sum_eigenvalues_pow (k : ℕ) :
    (B ^ k).trace = ∑ j, (hB.eigenvalues j : 𝕜) ^ k := by
  conv_lhs => rw [hB.spectral_theorem, ← map_pow]
  rw [conjStarAlgAut_apply, trace_mul_cycle, star_mul_self_of_mem hB.eigenvectorUnitary.property,
    one_mul, diagonal_pow, trace_diagonal]
  simp

end Matrix.IsHermitian

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι 𝕜}
  (hB : B.IsHermitian)
include hB

/-- Unitary diagonalization of a Hermitian matrix as a matrix product: `Uᴴ B U` is the diagonal
matrix of the eigenvalues of `B`, where `U = hB.eigenvectorUnitary`. -/
theorem star_eigenvectorUnitary_mul_mul_eigenvectorUnitary :
    star (hB.eigenvectorUnitary : Matrix ι ι 𝕜) * B * (hB.eigenvectorUnitary : Matrix ι ι 𝕜) =
      diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
  simpa [Unitary.conjStarAlgAut_star_apply] using hB.conjStarAlgAut_star_eigenvectorUnitary

/-- The coordinates `Uᴴ u` of an eigenvector `u` of `B` for the eigenvalue `μ`, in the eigenbasis
`U = hB.eigenvectorUnitary`, vanish at every index whose eigenvalue differs from `μ`. -/
theorem star_eigenvectorUnitary_mulVec_apply_eq_zero {μ : ℝ} {u : ι → 𝕜}
    (hu : B *ᵥ u = (μ : 𝕜) • u) {k : ι} (hk : hB.eigenvalues k ≠ μ) :
    (star (hB.eigenvectorUnitary : Matrix ι ι 𝕜) *ᵥ u) k = 0 := by
  set U : Matrix ι ι 𝕜 := (hB.eigenvectorUnitary : Matrix ι ι 𝕜)
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.property
  have h : diagonal (RCLike.ofReal ∘ hB.eigenvalues) *ᵥ (star U *ᵥ u) =
      (μ : 𝕜) • (star U *ᵥ u) := by
    rw [← hB.star_eigenvectorUnitary_mul_mul_eigenvectorUnitary, ← mulVec_mulVec,
      mulVec_mulVec _ U, hU', one_mulVec, ← mulVec_mulVec, hu, mulVec_smul]
  have hk' := congrFun h k
  simp only [mulVec_diagonal, Function.comp_apply, Pi.smul_apply, smul_eq_mul] at hk'
  have h' : ((hB.eigenvalues k : 𝕜) - μ) * (star U *ᵥ u) k = 0 := by rw [sub_mul, hk', sub_self]
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 (by exact_mod_cast hk))

/-- The adjugate of `λ k₀ - B` multiplies an eigenvector of a Hermitian matrix `B` for the
eigenvalue `λ k₀ = hB.eigenvalues k₀` by the product `∏_{k ≠ k₀} (λ k₀ - λ k)` of the gaps to the
eigenvalues at the other indices. This product vanishes unless the eigenvalue is simple. -/
theorem adjugate_scalar_sub_mulVec_eq_prod_smul {k₀ : ι} {u : ι → 𝕜}
    (hu : B *ᵥ u = (hB.eigenvalues k₀ : 𝕜) • u) :
    Matrix.adjugate (scalar ι (hB.eigenvalues k₀ : 𝕜) - B) *ᵥ u =
      (∏ k ∈ Finset.univ.erase k₀, ((hB.eigenvalues k₀ - hB.eigenvalues k : ℝ) : 𝕜)) • u := by
  set U : Matrix ι ι 𝕜 := (hB.eigenvectorUnitary : Matrix ι ι 𝕜)
  set d := hB.eigenvalues
  set μ := d k₀
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.property
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.property
  -- In the eigenbasis, `μ - B` is the diagonal matrix of the gaps `μ - λₖ`.
  have hN : scalar ι (μ : 𝕜) - B = U * diagonal (fun k ↦ ((μ - d k : ℝ) : 𝕜)) * star U := by
    have hD : diagonal (fun k ↦ ((μ - d k : ℝ) : 𝕜)) =
        (μ : 𝕜) • 1 - diagonal (RCLike.ofReal ∘ d) := by
      rw [smul_one_eq_diagonal, diagonal_sub]
      simp
    rw [hD, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU',
      scalar_apply, ← smul_one_eq_diagonal]
    conv_lhs => rw [hB.spectral_theorem, conjStarAlgAut_apply]
  -- Conjugation by a unitary commutes with the adjugate.
  have hadj : Matrix.adjugate (scalar ι (μ : 𝕜) - B) =
      U * Matrix.adjugate (diagonal fun k ↦ ((μ - d k : ℝ) : 𝕜)) * star U := by
    rw [hN, adjugate_mul_distrib, adjugate_mul_distrib, adjugate_eq_det_smul_of_mul_eq_one hU,
      adjugate_eq_det_smul_of_mul_eq_one hU']
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [← det_mul, hU', det_one, one_smul]
  -- Off `k₀`, either the eigen-coordinate of `u` or the adjugate entry, a product containing the
  -- gap `μ - λ k₀ = 0`, vanishes.
  have hdiag : Matrix.adjugate (diagonal fun k ↦ ((μ - d k : ℝ) : 𝕜)) *ᵥ (star U *ᵥ u) =
      (∏ k ∈ Finset.univ.erase k₀, ((μ - d k : ℝ) : 𝕜)) • (star U *ᵥ u) := by
    ext k
    rw [adjugate_diagonal, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    obtain rfl | hk := eq_or_ne k₀ k
    · rfl
    obtain hdk | hdk := ne_or_eq (d k) μ
    · rw [hB.star_eigenvectorUnitary_mulVec_apply_eq_zero hu hdk, mul_zero, mul_zero]
    · rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k₀⟩) (by simp [μ]),
        Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hk.symm, Finset.mem_univ k⟩)
          (by rw [hdk, sub_self, RCLike.ofReal_zero])]
  rw [hadj, ← mulVec_mulVec, ← mulVec_mulVec, hdiag, mulVec_smul, mulVec_mulVec, hU', one_mulVec]

/-- A unit eigenvector `u` of a simple eigenvalue `λ k₀` of a Hermitian matrix `B` is a unimodular
multiple of the `k₀`-th column of `U = hB.eigenvectorUnitary`, so `⟪u, C u⟫ = (Uᴴ C U) k₀ k₀` for
every matrix `C`. -/
theorem star_dotProduct_mulVec_eq_of_simple {k₀ : ι}
    (hk₀ : ∀ k ≠ k₀, hB.eigenvalues k ≠ hB.eigenvalues k₀) {u : ι → 𝕜}
    (hu : B *ᵥ u = (hB.eigenvalues k₀ : 𝕜) • u) (hu1 : star u ⬝ᵥ u = 1) (C : Matrix ι ι 𝕜) :
    star u ⬝ᵥ (C *ᵥ u) =
      (star (hB.eigenvectorUnitary : Matrix ι ι 𝕜) * C * hB.eigenvectorUnitary) k₀ k₀ := by
  set U : Matrix ι ι 𝕜 := (hB.eigenvectorUnitary : Matrix ι ι 𝕜)
  set d := hB.eigenvalues
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hB.eigenvectorUnitary.property
  have hU' : U * star U = 1 := Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.property
  -- Coordinates of `u` in the eigenbasis vanish off `k₀`.
  set w := star U *ᵥ u
  have huw : u = U *ᵥ w := by rw [mulVec_mulVec, hU', one_mulVec]
  have hw : w = Pi.single k₀ (w k₀) := by
    ext k
    obtain rfl | hk := eq_or_ne k k₀
    · simp
    rw [Pi.single_eq_of_ne hk]
    exact hB.star_eigenvectorUnitary_mulVec_apply_eq_zero hu (hk₀ k hk)
  have hconj (D : Matrix ι ι 𝕜) : star u ⬝ᵥ (D *ᵥ u) = star w ⬝ᵥ ((star U * D * U) *ᵥ w) := by
    rw [huw, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, star_eq_conjTranspose,
      Matrix.mul_assoc]
  have hsingle (D : Matrix ι ι 𝕜) (a : 𝕜) :
      star (Pi.single k₀ a) ⬝ᵥ (D *ᵥ Pi.single k₀ a) = star a * a * D k₀ k₀ := by
    rw [← Pi.single_star, single_dotProduct]
    simp only [mulVec, dotProduct_single]
    ring
  have h1 : star (w k₀) * w k₀ = 1 := by
    have h := hconj 1
    rw [Matrix.mul_one, hU, hw, hsingle, one_mulVec, hu1] at h
    simpa using h.symm
  rw [hconj, hw, hsingle, h1, one_mul]

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
  rw [hA.toEuclideanLin_eigenvectorBasis, inner_smul_left] at hsymm
  simpa [toLpLin_apply, hker, hij] using hsymm

end Matrix.IsHermitian

namespace Matrix

open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Let `0 ≤ A ≤ B`, that is `A` and `B - A` positive semidefinite, let `u` be a unit eigenvector
of `A` with eigenvalue `a`, and let `B` have eigenvalues `bⱼ` and orthonormal eigenvectors `vⱼ`.
Then `a ∑ⱼ bⱼ⁻¹ ‖⟪u, vⱼ⟫‖² ≤ 1`, that is `a ⟪u, B⁻¹ u⟫ ≤ 1` for the pseudo-inverse `B⁻¹` of `B`,
with the convention `0⁻¹ = 0`. For `a = 0` the bound is trivial. -/
theorem PosSemidef.eigenvalues_mul_sum_inv_mul_le_one {A B : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) (hB : B.IsHermitian) (i : ι) :
    hA.1.eigenvalues i * ∑ j, (hB.eigenvalues j)⁻¹ *
      ‖⟪hA.1.eigenvectorBasis i, hB.eigenvectorBasis j⟫_𝕜‖ ^ 2 ≤ 1 := by
  obtain hi | hi := (hA.eigenvalues_nonneg i).eq_or_lt
  · simp [← hi]
  set a := hA.1.eigenvalues i
  set u := hA.1.eigenvectorBasis i
  set v := hB.eigenvectorBasis
  set b := hB.eigenvalues
  set c : ι → 𝕜 := fun j ↦ ⟪v j, u⟫_𝕜
  set s : ℝ := ∑ j, (b j)⁻¹ * ‖⟪u, v j⟫_𝕜‖ ^ 2
  rcases (hA.eigenvalues_nonneg i).eq_or_lt with ha | hi
  · have ha0 : a = 0 := ha.symm
    rw [ha0, zero_mul]
    exact zero_le_one
  have hb (j : ι) : 0 ≤ b j := by simpa using (hA.add hBA).eigenvalues_nonneg j
  have hcn (j : ι) : ‖c j‖ = ‖⟪u, v j⟫_𝕜‖ := norm_inner_symm _ _
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
  have hTu : A.toEuclideanLin u = (a : 𝕜) • u := hA.1.toEuclideanLin_eigenvectorBasis i
  have huu : ⟪u, u⟫_𝕜 = 1 := hA.1.eigenvectorBasis.inner_eq_one i
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

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [LinearOrder ι]

/-- If a real diagonal decreases along a linear order on its finite index type, its entries listed
in that order are the ordered eigenvalues of every unitary conjugate of the diagonal. -/
theorem eigenvalues₀_conjStarAlgAut_diagonal (U : unitaryGroup ι 𝕜) {d : ι → ℝ}
    (hd : Antitone d) (hA : (Unitary.conjStarAlgAut ℝ _ U
      (diagonal fun i ↦ (d i : 𝕜))).IsHermitian) :
    hA.eigenvalues₀ = d ∘ Fintype.orderIsoFinOfCardEq ι rfl := by
  let D := diagonal fun i : ι ↦ (d i : 𝕜)
  let o := Fintype.orderIsoFinOfCardEq ι rfl
  have hC : (Unitary.conjStarAlgAut ℝ _ U D).charpoly = D.charpoly := by
    rw [Unitary.conjStarAlgAut_apply, ← inv_eq_left_inv (Unitary.coe_star_mul_self U)]
    exact charpoly_units_conj (Unitary.toUnits U) D
  rw [← List.ofFn_inj, ← hA.sort_roots_charpoly_eq_eigenvalues₀, hC,
    roots_charpoly_diagonal, Multiset.map_map]
  have hmap : Finset.univ.val.map (RCLike.re ∘ fun i ↦ (d i : 𝕜)) =
      (List.ofFn (d ∘ o) : Multiset ℝ) := by
    have ho : Finset.univ.val.map (d ∘ o) = Finset.univ.val.map d := by
      rw [← Multiset.map_map, ← OrderIso.coe_toEquiv, Multiset.map_univ_val_equiv]
    rw [← Fin.univ_val_map, ho]
    simp
  rw [hmap, Multiset.coe_sort]
  exact List.mergeSort_of_pairwise (by
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact (hd.comp_monotone o.monotone).sortedGE_ofFn)

end Matrix

namespace Matrix.IsSymm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Orthogonal diagonalization.** A real symmetric matrix is `O * diagonal d * O⁻¹` for an
invertible `O` with `O⁻¹ = Oᵀ`; one can take for `O` the eigenvector unitary and for `d` the
eigenvalues. -/
theorem exists_orthogonal_diagonal {X : Matrix ι ι ℝ} (hX : X.IsSymm) :
    ∃ (O : GL ι ℝ) (d : ι → ℝ), ((O⁻¹ : GL ι ℝ) : Matrix ι ι ℝ) = (O : Matrix ι ι ℝ)ᵀ ∧
      X = O * diagonal d * ((O⁻¹ : GL ι ℝ) : Matrix ι ι ℝ) := by
  have hH : X.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact hX
  have hstar : star (hH.eigenvectorUnitary : Matrix ι ι ℝ) =
      (hH.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ :=
    conjTranspose_eq_transpose_of_trivial _
  refine ⟨⟨hH.eigenvectorUnitary, (hH.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ,
    hstar ▸ Unitary.coe_mul_star_self _, hstar ▸ Unitary.coe_star_mul_self _⟩,
    hH.eigenvalues, rfl, ?_⟩
  conv_lhs => rw [hH.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, hstar]

end Matrix.IsSymm

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι 𝕜}

/-- Reindexing a sorted eigenvalue by the canonical finite equivalence gives the
corresponding matrix-indexed eigenvalue. -/
@[simp]
theorem eigenvalues_apply_equivOfCardEq (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) i) =
      hA.eigenvalues₀ i := by
  simp only [IsHermitian.eigenvalues, Equiv.symm_apply_apply]

/-- A product of a function over the matrix-indexed eigenvalues of a Hermitian matrix is its
product over the sorted eigenvalues. -/
@[to_additive /-- A sum of a function over the matrix-indexed eigenvalues of a Hermitian matrix is
its sum over the sorted eigenvalues. -/]
theorem prod_comp_eigenvalues {M : Type*} [CommMonoid M] (hA : A.IsHermitian) (g : ℝ → M) :
    ∏ i, g (hA.eigenvalues i) = ∏ k, g (hA.eigenvalues₀ k) := by
  rw [← Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)))]
  simp only [eigenvalues_apply_equivOfCardEq]

/-- A simple sorted eigenvalue is simple as a matrix-indexed eigenvalue at the index given by the
canonical finite equivalence. -/
theorem eigenvalues_ne_eigenvalues_equivOfCardEq (hA : A.IsHermitian)
    {i : Fin (Fintype.card ι)} (hi : ∀ j ≠ i, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ i) :
    ∀ k ≠ Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) i, hA.eigenvalues k ≠
      hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι)) i) := by
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  intro k hk
  have hk' : e.symm k ≠ i := fun h ↦ hk (by rw [← h, e.apply_symm_apply])
  simpa [e, IsHermitian.eigenvalues] using hi _ hk'

end Matrix.IsHermitian
