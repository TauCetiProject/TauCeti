/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector
import TauCeti.Analysis.Matrix.Spectrum

/-!
# Spectral projectors of Hermitian matrices

For a Hermitian matrix `A` over an `RCLike` field `𝕜`, this file pairs Mathlib's sorted decreasing
eigenvalue list `hA.eigenvalues₀ : Fin (Fintype.card n) → ℝ` with a chosen orthonormal eigenbasis
`hA.eigenvectorBasis₀` and defines the rank-one orthogonal projectors `hA.eigenprojector₀ k`,
building on `TauCeti.rankOneHermitianProjector` and `TauCeti.hermitianProjectorLocus` from
`TauCeti.LinearAlgebra.Projectivization.HermitianProjector`.

At repeated eigenvalues both `hA.eigenvectorBasis₀` and `hA.eigenprojector₀ k` depend on
`Classical.choose` rather than projecting onto the full eigenspace. Each rank-one projector lies in
`TauCeti.hermitianProjectorLocus n 𝕜`, and the family is pairwise orthogonal, sums to `1`, and
resolves `A` as `∑ k, (hA.eigenvalues₀ k : 𝕜) • hA.eigenprojector₀ k`. At a simple sorted eigenvalue
`hA.eigenvalues₀ k`, `hA.eigenprojector₀ k` becomes canonical: it agrees with
`TauCeti.rankOneHermitianProjector v` for every nonzero eigenvector `v`, and is symmetric whenever
`A` is symmetric.

## Main definitions

* `Matrix.IsHermitian.eigenvectorBasis₀`: chosen orthonormal eigenbasis paired with
  `hA.eigenvalues₀`.
* `Matrix.IsHermitian.eigenprojector₀`: rank-one Hermitian spectral projectors indexed by
  `Fin (Fintype.card n)`.

## Main results

* `Matrix.IsHermitian.eigenprojector₀_mem_hermitianProjectorLocus`,
  `Matrix.IsHermitian.eigenprojector₀_mul_eigenprojector₀`,
  `Matrix.IsHermitian.sum_eigenprojector₀`, and
  `Matrix.IsHermitian.sum_eigenvalues₀_smul_eigenprojector₀`.
* `Matrix.IsHermitian.eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec_eq_smul`: basis
  independence of `hA.eigenprojector₀ k` at a simple sorted eigenvalue.
* `Matrix.IsHermitian.isSymm_eigenprojector₀`: symmetry of simple projectors for symmetric `A`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Ch. I §5 and Ch. II §§1–2.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), Ch. I.
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge Univ. Press (2013), Thm. 2.5.6.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

namespace IsHermitian

/-! ### Sorted orthonormal eigenbasis -/

/-- Choice of an orthonormal basis of eigenvectors of a Hermitian matrix `A`, indexed by
`Fin (Fintype.card n)` so that the `k`-th vector corresponds directly to `hA.eigenvalues₀ k`. -/
def eigenvectorBasis₀ (hA : A.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n) :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace

/-- Unfolds `hA.eigenvectorBasis₀` in terms of `LinearMap.IsSymmetric.eigenvectorBasis`. -/
theorem eigenvectorBasis₀_def (hA : A.IsHermitian) :
    hA.eigenvectorBasis₀ =
      (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace := (rfl)

/-- Reindexing `hA.eigenvectorBasis` by the canonical finite equivalence recovers
`hA.eigenvectorBasis₀`. -/
@[simp] theorem eigenvectorBasis_apply_equivOfCardEq (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenvectorBasis (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) k) =
      hA.eigenvectorBasis₀ k := by
  simp [eigenvectorBasis, eigenvectorBasis₀_def]

/-- Each vector of `hA.eigenvectorBasis₀` is a matrix eigenvector of `A` with real eigenvalue
`hA.eigenvalues₀ k`. -/
theorem mulVec_eigenvectorBasis₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    A *ᵥ ⇑(hA.eigenvectorBasis₀ k) = hA.eigenvalues₀ k • ⇑(hA.eigenvectorBasis₀ k) := by
  rw [← hA.eigenvectorBasis_apply_equivOfCardEq, hA.mulVec_eigenvectorBasis,
    hA.eigenvalues_apply_equivOfCardEq]

/-- Matrix-vector multiplication by `A` scales `hA.eigenvectorBasis₀ k` by
`(hA.eigenvalues₀ k : 𝕜)`. -/
theorem mulVec_eigenvectorBasis₀_coe (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    A *ᵥ ⇑(hA.eigenvectorBasis₀ k) = (hA.eigenvalues₀ k : 𝕜) • ⇑(hA.eigenvectorBasis₀ k) := by
  rw [hA.mulVec_eigenvectorBasis₀, RCLike.real_smul_eq_coe_smul (K := 𝕜)]

/-- Left vector-matrix multiplication of `star ⇑(hA.eigenvectorBasis₀ k)` by `A` scales by
`(hA.eigenvalues₀ k : 𝕜)`. -/
theorem star_eigenvectorBasis₀_vecMul (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    star ⇑(hA.eigenvectorBasis₀ k) ᵥ* A =
      (hA.eigenvalues₀ k : 𝕜) • star ⇑(hA.eigenvectorBasis₀ k) := by
  simpa [star_mulVec, hA.eq, star_smul] using congrArg star (hA.mulVec_eigenvectorBasis₀_coe k)

/-- Each vector of `hA.eigenvectorBasis₀` is an eigenvector of `A.toEuclideanLin` with eigenvalue
`hA.eigenvalues₀ k`. -/
@[simp] theorem toEuclideanLin_eigenvectorBasis₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    A.toEuclideanLin (hA.eigenvectorBasis₀ k) =
      (hA.eigenvalues₀ k : 𝕜) • hA.eigenvectorBasis₀ k := by
  simp [eigenvectorBasis₀_def, eigenvalues₀]

/-- Orthonormality of `hA.eigenvectorBasis₀` expressed via the Hermitian dot product on `n → 𝕜`. -/
theorem dotProduct_star_eigenvectorBasis₀ (hA : A.IsHermitian) (j k : Fin (Fintype.card n)) :
    star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ ⇑(hA.eigenvectorBasis₀ k) = if j = k then 1 else 0 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  split_ifs with hjk
  · exact hjk ▸ hA.eigenvectorBasis₀.inner_eq_one j
  · exact hA.eigenvectorBasis₀.orthonormal.right hjk

/-- Every vector in `hA.eigenvectorBasis₀` has unit Hermitian norm square. -/
@[simp] theorem dotProduct_star_eigenvectorBasis₀_self (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ ⇑(hA.eigenvectorBasis₀ k) = 1 := by
  simp [hA.dotProduct_star_eigenvectorBasis₀]

/-- Distinct vectors in `hA.eigenvectorBasis₀` are orthogonal for the Hermitian dot product. -/
theorem dotProduct_star_eigenvectorBasis₀_of_ne (hA : A.IsHermitian)
    {j k : Fin (Fintype.card n)} (hjk : j ≠ k) :
    star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ ⇑(hA.eigenvectorBasis₀ k) = 0 := by
  simp [hA.dotProduct_star_eigenvectorBasis₀, hjk]

/-- Expansion of any vector `v : n → 𝕜` along `hA.eigenvectorBasis₀`. -/
theorem sum_dotProduct_smul_eigenvectorBasis₀ (hA : A.IsHermitian) (v : n → 𝕜) :
    ∑ j, (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v) • ⇑(hA.eigenvectorBasis₀ j) = v := by
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    congrArg WithLp.ofLp (hA.eigenvectorBasis₀.sum_repr' (WithLp.toLp 2 v))

/-! ### Rank-one spectral projectors -/

/-- The rank-one orthogonal projector `uₖ uₖ*` onto `hA.eigenvectorBasis₀ k`. -/
def eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) : Matrix n n 𝕜 :=
  vecMulVec ⇑(hA.eigenvectorBasis₀ k) (star ⇑(hA.eigenvectorBasis₀ k))

/-- Unfolds `hA.eigenprojector₀ k` as `vecMulVec` of the `k`-th sorted eigenvector and its star. -/
theorem eigenprojector₀_def (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k =
      vecMulVec ⇑(hA.eigenvectorBasis₀ k) (star ⇑(hA.eigenvectorBasis₀ k)) := (rfl)

/-- Equal Hermitian matrices have equal sorted projector families. -/
theorem eigenprojector₀_congr {B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) : hA.eigenprojector₀ = hB.eigenprojector₀ := by subst h; rfl

/-- `hA.eigenprojector₀ k` is the rank-one Hermitian projector of `hA.eigenvectorBasis₀ k`. -/
theorem eigenprojector₀_eq_rankOneHermitianProjector (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k = TauCeti.rankOneHermitianProjector ⇑(hA.eigenvectorBasis₀ k) := by
  rw [TauCeti.rankOneHermitianProjector_def, eigenprojector₀_def,
    hA.dotProduct_star_eigenvectorBasis₀_self, inv_one, one_smul]

/-- Every sorted spectral projector lies in `TauCeti.hermitianProjectorLocus n 𝕜`. -/
theorem eigenprojector₀_mem_hermitianProjectorLocus (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k ∈ TauCeti.hermitianProjectorLocus n 𝕜 := by
  rw [hA.eigenprojector₀_eq_rankOneHermitianProjector]
  exact TauCeti.rankOneHermitianProjector_mem_hermitianProjectorLocus
    (by simp [hA.dotProduct_star_eigenvectorBasis₀_self])

/-- Every sorted spectral projector is a star projection. -/
@[simp] theorem isStarProjection_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsStarProjection (hA.eigenprojector₀ k) :=
  (TauCeti.mem_hermitianProjectorLocus.mp (hA.eigenprojector₀_mem_hermitianProjectorLocus k)).left

/-- Every sorted spectral projector is self-adjoint. -/
@[simp] theorem isSelfAdjoint_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsSelfAdjoint (hA.eigenprojector₀ k) :=
  (hA.isStarProjection_eigenprojector₀ k).isSelfAdjoint

/-- Every sorted spectral projector is Hermitian. -/
@[simp] theorem isHermitian_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    (hA.eigenprojector₀ k).IsHermitian := by
  simpa [IsHermitian, star_eq_conjTranspose] using (hA.isSelfAdjoint_eigenprojector₀ k).star_eq

/-- Taking the conjugate transpose fixes every sorted spectral projector. -/
@[simp] theorem conjTranspose_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    (hA.eigenprojector₀ k)ᴴ = hA.eigenprojector₀ k :=
  (hA.isHermitian_eigenprojector₀ k).eq

/-- Taking `star` fixes every sorted spectral projector. -/
@[simp] theorem star_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    star (hA.eigenprojector₀ k) = hA.eigenprojector₀ k :=
  (hA.isSelfAdjoint_eigenprojector₀ k).star_eq

/-- Every sorted spectral projector is idempotent. -/
@[simp] theorem eigenprojector₀_mul_self (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k * hA.eigenprojector₀ k = hA.eigenprojector₀ k :=
  (hA.isStarProjection_eigenprojector₀ k).isIdempotentElem.eq

/-- Spectral projectors at distinct sorted indices are mutually orthogonal. -/
theorem eigenprojector₀_mul_of_ne (hA : A.IsHermitian) {j k : Fin (Fintype.card n)}
    (hjk : j ≠ k) : hA.eigenprojector₀ j * hA.eigenprojector₀ k = 0 := by
  simp [eigenprojector₀_def, vecMulVec_mul_vecMulVec,
    hA.dotProduct_star_eigenvectorBasis₀_of_ne hjk]

/-- Multiplication table of the sorted spectral projectors. -/
theorem eigenprojector₀_mul_eigenprojector₀ (hA : A.IsHermitian) (j k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ j * hA.eigenprojector₀ k =
      if j = k then hA.eigenprojector₀ j else 0 := by
  split_ifs with hjk
  · exact hjk ▸ hA.eigenprojector₀_mul_self j
  · exact hA.eigenprojector₀_mul_of_ne hjk

/-- Action of `hA.eigenprojector₀ k` on a vector `x : n → 𝕜`. -/
theorem eigenprojector₀_mulVec (hA : A.IsHermitian) (k : Fin (Fintype.card n)) (x : n → 𝕜) :
    hA.eigenprojector₀ k *ᵥ x =
      (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ x) • ⇑(hA.eigenvectorBasis₀ k) := by
  rw [eigenprojector₀_def, vecMulVec_mulVec, op_smul_eq_smul]

/-- `hA.eigenprojector₀ k` fixes the `k`-th sorted eigenvector. -/
@[simp] theorem eigenprojector₀_mulVec_eigenvectorBasis₀_self (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k *ᵥ ⇑(hA.eigenvectorBasis₀ k) = ⇑(hA.eigenvectorBasis₀ k) := by
  simp [hA.eigenprojector₀_mulVec]

/-- `hA.eigenprojector₀ j` annihilates the `k`-th sorted eigenvector for `j ≠ k`. -/
theorem eigenprojector₀_mulVec_eigenvectorBasis₀_of_ne (hA : A.IsHermitian)
    {j k : Fin (Fintype.card n)} (hjk : j ≠ k) :
    hA.eigenprojector₀ j *ᵥ ⇑(hA.eigenvectorBasis₀ k) = 0 := by
  simp [hA.eigenprojector₀_mulVec, hA.dotProduct_star_eigenvectorBasis₀_of_ne hjk]

/-- Every sorted spectral projector has trace `1`. -/
@[simp] theorem trace_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    (hA.eigenprojector₀ k).trace = 1 :=
  (TauCeti.mem_hermitianProjectorLocus.mp (hA.eigenprojector₀_mem_hermitianProjectorLocus k)).right

/-- The trace of `hA.eigenprojector₀ k * B` is the Rayleigh matrix element of `B` at the `k`-th
sorted eigenvector. -/
theorem trace_eigenprojector₀_mul (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (B : Matrix n n 𝕜) :
    (hA.eigenprojector₀ k * B).trace =
      star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ k)) := by
  rw [eigenprojector₀_def, vecMulVec_mul, trace_vecMulVec, dotProduct_comm, dotProduct_mulVec]

/-- The trace of `B * hA.eigenprojector₀ k` is the Rayleigh matrix element of `B` at the `k`-th
sorted eigenvector. -/
theorem trace_mul_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n))
    (B : Matrix n n 𝕜) :
    (B * hA.eigenprojector₀ k).trace =
      star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ k)) := by
  rw [trace_mul_comm, hA.trace_eigenprojector₀_mul]

/-- Four-factor trace identity for two spectral projectors sandwiching matrices `B` and `C`. -/
theorem trace_eigenprojector₀_mul_mul_eigenprojector₀_mul (hA : A.IsHermitian)
    (j k : Fin (Fintype.card n)) (B C : Matrix n n 𝕜) :
    (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j * C).trace =
      (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ j))) *
        (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ (C *ᵥ ⇑(hA.eigenvectorBasis₀ k))) := by
  simp only [eigenprojector₀_def, mul_vecMulVec, vecMulVec_mul, trace_vecMulVec,
    vecMulVec_mulVec, smul_dotProduct, dotProduct_mulVec, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  rw [dotProduct_comm ⇑(hA.eigenvectorBasis₀ k), mul_comm]

/-- **Resolution of the identity** by the sorted rank-one spectral projectors. -/
@[simp] theorem sum_eigenprojector₀ (hA : A.IsHermitian) :
    ∑ k, hA.eigenprojector₀ k = (1 : Matrix n n 𝕜) := by
  ext i j
  simpa [eigenprojector₀_def, Finset.sum_apply, vecMulVec_apply, Pi.smul_apply, Matrix.one_apply,
    Pi.single_apply, mul_comm, eq_comm] using
      congrFun (hA.sum_dotProduct_smul_eigenvectorBasis₀ (Pi.single j 1)) i

/-- Left multiplication of `hA.eigenprojector₀ k` by `A` scales by `hA.eigenvalues₀ k`. -/
@[simp] theorem mul_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    A * hA.eigenprojector₀ k = (hA.eigenvalues₀ k : 𝕜) • hA.eigenprojector₀ k := by
  rw [eigenprojector₀_def, mul_vecMulVec, hA.mulVec_eigenvectorBasis₀_coe, smul_vecMulVec]

/-- Right multiplication of `hA.eigenprojector₀ k` by `A` scales by `hA.eigenvalues₀ k`. -/
@[simp] theorem eigenprojector₀_mul (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k * A = (hA.eigenvalues₀ k : 𝕜) • hA.eigenprojector₀ k := by
  have h := congrArg Matrix.conjTranspose (hA.mul_eigenprojector₀ k)
  rwa [conjTranspose_mul, conjTranspose_smul, hA.eq, hA.conjTranspose_eigenprojector₀ k,
    RCLike.star_def, RCLike.conj_ofReal] at h

/-- **Spectral decomposition** of a Hermitian matrix along its sorted spectral projectors. -/
theorem sum_eigenvalues₀_smul_eigenprojector₀ (hA : A.IsHermitian) :
    ∑ k, (hA.eigenvalues₀ k : 𝕜) • hA.eigenprojector₀ k = A := by
  simp_rw [← hA.mul_eigenprojector₀, ← Matrix.mul_sum, hA.sum_eigenprojector₀, Matrix.mul_one]

/-- The trace of `hA.eigenprojector₀ k * A` recovers `(hA.eigenvalues₀ k : 𝕜)`. -/
theorem trace_eigenprojector₀_mul_eq_eigenvalues₀ (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    (hA.eigenprojector₀ k * A).trace = (hA.eigenvalues₀ k : 𝕜) := by
  rw [hA.eigenprojector₀_mul, trace_smul, hA.trace_eigenprojector₀, smul_eq_mul, mul_one]

/-- The real part of the trace of `hA.eigenprojector₀ k * A` recovers `hA.eigenvalues₀ k`. -/
theorem re_trace_eigenprojector₀_mul_eq_eigenvalues₀ (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    RCLike.re (hA.eigenprojector₀ k * A).trace = hA.eigenvalues₀ k := by
  rw [hA.trace_eigenprojector₀_mul_eq_eigenvalues₀, RCLike.ofReal_re]

/-! ### Canonical projector at a simple eigenvalue -/

/-- Any vector `v` satisfying `A *ᵥ v = μ • v` is orthogonal to every sorted eigenvector
`hA.eigenvectorBasis₀ j` whose eigenvalue `(hA.eigenvalues₀ j : 𝕜)` differs from `μ`. -/
theorem dotProduct_star_eigenvectorBasis₀_eq_zero_of_mulVec_eq_smul (hA : A.IsHermitian)
    {j : Fin (Fintype.card n)} {μ : 𝕜} (hne : (hA.eigenvalues₀ j : 𝕜) ≠ μ)
    {v : n → 𝕜} (hv : A *ᵥ v = μ • v) :
    star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v = 0 := by
  have h1 : (hA.eigenvalues₀ j : 𝕜) * (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v) =
      μ * (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v) := by
    rw [← smul_eq_mul, ← smul_dotProduct, ← hA.star_eigenvectorBasis₀_vecMul,
      ← dotProduct_mulVec, hv, dotProduct_smul, smul_eq_mul]
  exact (mul_eq_zero.mp ((sub_mul _ _ _).trans (sub_eq_zero.mpr h1))).resolve_left
    (sub_ne_zero.mpr hne)

/-- Every nonzero eigenvector `v` of a Hermitian matrix `A` with scalar `μ : 𝕜` (`A *ᵥ v = μ • v`)
has `μ = (hA.eigenvalues₀ m : 𝕜)` for some sorted index `m`. -/
theorem exists_eigenvalues₀_eq_of_mulVec_eq_smul (hA : A.IsHermitian)
    {v : n → 𝕜} (hv_ne : v ≠ 0) {μ : 𝕜} (hv : A *ᵥ v = μ • v) :
    ∃ m : Fin (Fintype.card n), μ = (hA.eigenvalues₀ m : 𝕜) := by
  by_contra! hall
  refine hv_ne ?_
  rw [← hA.sum_dotProduct_smul_eigenvectorBasis₀ v]
  exact Finset.sum_eq_zero fun j _ ↦ by
    rw [hA.dotProduct_star_eigenvectorBasis₀_eq_zero_of_mulVec_eq_smul (hall j).symm hv, zero_smul]

/-- At a simple sorted eigenvalue `hA.eigenvalues₀ k`, every eigenvector `v` for
`hA.eigenvalues₀ k` is a scalar multiple of `hA.eigenvectorBasis₀ k`. -/
theorem eq_smul_eigenvectorBasis₀_of_mulVec_eq_smul (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k)
    {v : n → 𝕜} (hv : A *ᵥ v = (hA.eigenvalues₀ k : 𝕜) • v) :
    v = (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ v) • ⇑(hA.eigenvectorBasis₀ k) := by
  conv_lhs => rw [← hA.sum_dotProduct_smul_eigenvectorBasis₀ v]
  refine Finset.sum_eq_single k (fun j _ hjk ↦ ?_) (fun hk' ↦ (hk' (Finset.mem_univ k)).elim)
  rw [hA.dotProduct_star_eigenvectorBasis₀_eq_zero_of_mulVec_eq_smul
    ((RCLike.ofReal_injective (K := 𝕜)).ne (hk j hjk)) hv, zero_smul]

/-- **Basis independence at a simple eigenvalue.** If `hA.eigenvalues₀ k` is simple, then
`hA.eigenprojector₀ k` agrees with `TauCeti.rankOneHermitianProjector v` for any nonzero
eigenvector `v` with eigenvalue `hA.eigenvalues₀ k`. -/
theorem eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec_eq_smul (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k)
    {v : n → 𝕜} (hv_ne : v ≠ 0) (hv : A *ᵥ v = (hA.eigenvalues₀ k : 𝕜) • v) :
    hA.eigenprojector₀ k = TauCeti.rankOneHermitianProjector v := by
  have hv_eq := hA.eq_smul_eigenvectorBasis₀_of_mulVec_eq_smul hk hv
  have hc : star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ v ≠ 0 :=
    fun h0 ↦ hv_ne (by rw [hv_eq, h0, zero_smul])
  rw [hv_eq, TauCeti.rankOneHermitianProjector_smul hc,
    ← hA.eigenprojector₀_eq_rankOneHermitianProjector]

/-- At a simple sorted eigenvalue `hA.eigenvalues₀ k`, any unit eigenvector `v` (`star v ⬝ᵥ v = 1`)
for `hA.eigenvalues₀ k` satisfies `hA.eigenprojector₀ k = vecMulVec v (star v)`. -/
theorem eigenprojector₀_eq_vecMulVec_of_mulVec_eq_smul (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k)
    {v : n → 𝕜} (hunit : star v ⬝ᵥ v = 1) (hv : A *ᵥ v = (hA.eigenvalues₀ k : 𝕜) • v) :
    hA.eigenprojector₀ k = vecMulVec v (star v) := by
  have hv_ne : v ≠ 0 := by rintro rfl; simp at hunit
  rw [hA.eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec_eq_smul hk hv_ne hv,
    TauCeti.rankOneHermitianProjector_def, hunit, inv_one, one_smul]

/-- If `A` is both Hermitian and symmetric (`Aᵀ = A`), its spectral projector at any simple sorted
eigenvalue is symmetric. -/
theorem isSymm_eigenprojector₀ (hA : A.IsHermitian) (hsymm : A.IsSymm)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (hA.eigenprojector₀ k).IsSymm := by
  set u : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  have hmap : A.map star = A := by rw [← conjTranspose_transpose, hA.eq, hsymm.eq]
  have hv : A *ᵥ star u = (hA.eigenvalues₀ k : 𝕜) • star u := by
    have h := congrArg star (hA.mulVec_eigenvectorBasis₀_coe k)
    have hmul : star (A *ᵥ u) = A.map star *ᵥ star u := by ext i; simp [mulVec, dotProduct]
    rwa [hmul, hmap, star_smul, RCLike.star_def, RCLike.conj_ofReal] at h
  have hunit : star (star u) ⬝ᵥ star u = 1 := by
    rw [star_star, dotProduct_comm, hA.dotProduct_star_eigenvectorBasis₀_self]
  rw [IsSymm]
  conv_lhs => rw [eigenprojector₀_def, transpose_vecMulVec]
  rw [hA.eigenprojector₀_eq_vecMulVec_of_mulVec_eq_smul hk hunit hv, star_star]

end IsHermitian

end Matrix
