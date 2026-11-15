/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector
import TauCeti.Analysis.Matrix.Eigenvalues.Basic

/-!
# Spectral projectors of Hermitian matrices

For a Hermitian matrix `A` over an `RCLike` field `𝕜`, Mathlib constructs both the sorted
decreasing eigenvalue list `hA.eigenvalues₀ : Fin (Fintype.card n) → ℝ` and the matrix-indexed
orthonormal eigenbasis `hA.eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)`. This
file provides the sorted eigenbasis `hA.eigenvectorBasis₀` paired directly with `hA.eigenvalues₀`,
together with the associated rank-one orthogonal projectors `hA.eigenprojector₀ k` and
`hA.eigenprojector i`.

Each projector `hA.eigenprojector₀ k` equals `TauCeti.rankOneHermitianProjector` of the `k`-th
unit eigenvector, hence lies in `TauCeti.hermitianProjectorLocus n 𝕜` (self-adjoint idempotents of
trace one). The projectors are pairwise orthogonal, sum to the identity matrix, and resolve `A` as
`∑ k, (hA.eigenvalues₀ k : 𝕜) • hA.eigenprojector₀ k`.

While `hA.eigenvectorBasis₀ k` depends on an arbitrary choice of unit eigenvector (and at repeated
eigenvalues on a basis of the eigenspace), at a simple eigenvalue `hA.eigenvalues₀ k` the
one-dimensional eigenspace is canonical: any nonzero eigenvector `v` with eigenvalue
`hA.eigenvalues₀ k` determines the same rank-one projector
`hA.eigenprojector₀ k = TauCeti.rankOneHermitianProjector v`. In particular, if `A` is also
symmetric (`Aᵀ = A`), the simple spectral projector `hA.eigenprojector₀ k` is symmetric even over
`ℂ`.

## Main definitions

* `Matrix.IsHermitian.eigenvectorBasis₀`: the orthonormal basis of `EuclideanSpace 𝕜 n` indexed by
  `Fin (Fintype.card n)` whose `k`-th vector is an eigenvector for `hA.eigenvalues₀ k`.
* `Matrix.IsHermitian.eigenprojector₀`: the rank-one Hermitian projector onto the `k`-th sorted
  eigenvector `hA.eigenvectorBasis₀ k`.
* `Matrix.IsHermitian.eigenprojector`: the rank-one Hermitian projector indexed by `n`, matching
  `hA.eigenvectorBasis` and `hA.eigenvalues`.

## Main results

* `Matrix.IsHermitian.eigenprojector₀_mem_hermitianProjectorLocus`: each `hA.eigenprojector₀ k` is
  a star projection of trace one.
* `Matrix.IsHermitian.eigenprojector₀_mul_eigenprojector₀`,
  `Matrix.IsHermitian.sum_eigenprojector₀`, and
  `Matrix.IsHermitian.sum_eigenvalues₀_smul_eigenprojector₀`: orthogonality, resolution of the
  identity, and spectral resolution of `A`.
* `Matrix.IsHermitian.eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec`: at a simple sorted
  eigenvalue, `hA.eigenprojector₀ k` agrees with `TauCeti.rankOneHermitianProjector v` for any
  nonzero eigenvector `v`, making it independent of the chosen eigenbasis.
* `Matrix.IsHermitian.isSymm_eigenprojector₀`: if `A` is both Hermitian and symmetric, the
  projector onto a simple eigenvalue is symmetric.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Classics in Mathematics, Springer (1995),
  Chapter I, §5 and Chapter II, §1–§2.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), Chapter I.
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Theorem 2.5.6.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

namespace IsHermitian

/-! ### Sorted orthonormal eigenbasis -/

/-- Choice of an orthonormal basis of eigenvectors of a Hermitian matrix `A`, indexed by
`Fin (Fintype.card n)` so that the `k`-th vector corresponds directly to the `k`-th sorted
eigenvalue `hA.eigenvalues₀ k`. -/
def eigenvectorBasis₀ (hA : A.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card n)) 𝕜 (EuclideanSpace 𝕜 n) :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace

/-- Reindexing `hA.eigenvectorBasis` by the canonical finite equivalence recovers
`hA.eigenvectorBasis₀`. -/
@[simp]
theorem eigenvectorBasis_apply_equivOfCardEq (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenvectorBasis (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) k) =
      hA.eigenvectorBasis₀ k := by
  simp [eigenvectorBasis, eigenvectorBasis₀]

/-- The `i`-th vector of `hA.eigenvectorBasis` is `hA.eigenvectorBasis₀` at the corresponding
`Fin (Fintype.card n)` index. -/
theorem eigenvectorBasis_eq_eigenvectorBasis₀ (hA : A.IsHermitian) (i : n) :
    hA.eigenvectorBasis i = hA.eigenvectorBasis₀
      ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i) := by
  simp [eigenvectorBasis, eigenvectorBasis₀]

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
  have h := congrArg star (hA.mulVec_eigenvectorBasis₀_coe k)
  simpa [star_mulVec, hA.eq, star_smul] using h

/-- Each vector of `hA.eigenvectorBasis₀` is an eigenvector of `A.toEuclideanLin` with eigenvalue
`hA.eigenvalues₀ k`. -/
@[simp]
theorem toEuclideanLin_eigenvectorBasis₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    A.toEuclideanLin (hA.eigenvectorBasis₀ k) =
      (hA.eigenvalues₀ k : 𝕜) • hA.eigenvectorBasis₀ k := by
  simp [eigenvectorBasis₀, eigenvalues₀]

/-- Orthonormality of `hA.eigenvectorBasis₀` expressed via the Hermitian dot product on `n → 𝕜`. -/
theorem dotProduct_star_eigenvectorBasis₀ (hA : A.IsHermitian)
    (j k : Fin (Fintype.card n)) :
    star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ ⇑(hA.eigenvectorBasis₀ k) = if j = k then 1 else 0 := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  split_ifs with hjk
  · subst hjk
    exact hA.eigenvectorBasis₀.inner_eq_one j
  · exact hA.eigenvectorBasis₀.orthonormal.2 hjk

/-- Every vector in `hA.eigenvectorBasis₀` has unit Hermitian norm square. -/
@[simp]
theorem dotProduct_star_eigenvectorBasis₀_self (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ ⇑(hA.eigenvectorBasis₀ k) = 1 := by
  simp [hA.dotProduct_star_eigenvectorBasis₀]

/-- Distinct vectors in `hA.eigenvectorBasis₀` are orthogonal for the Hermitian dot product. -/
theorem dotProduct_star_eigenvectorBasis₀_of_ne (hA : A.IsHermitian)
    {j k : Fin (Fintype.card n)} (hjk : j ≠ k) :
    star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ ⇑(hA.eigenvectorBasis₀ k) = 0 := by
  simp [hA.dotProduct_star_eigenvectorBasis₀, hjk]

/-- Expansion of any vector `v : n → 𝕜` along the sorted orthonormal eigenbasis
`hA.eigenvectorBasis₀`. -/
theorem sum_dotProduct_smul_eigenvectorBasis₀ (hA : A.IsHermitian) (v : n → 𝕜) :
    ∑ j, (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v) • ⇑(hA.eigenvectorBasis₀ j) = v := by
  have hval := congrArg WithLp.ofLp (hA.eigenvectorBasis₀.sum_repr' (WithLp.toLp 2 v))
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hval

/-! ### Rank-one spectral projectors -/

/-- The rank-one orthogonal projector `uₖ uₖ*` onto the `k`-th sorted eigenvector
`hA.eigenvectorBasis₀ k` of a Hermitian matrix `A`. -/
def eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) : Matrix n n 𝕜 :=
  vecMulVec ⇑(hA.eigenvectorBasis₀ k) (star ⇑(hA.eigenvectorBasis₀ k))

/-- The rank-one orthogonal projector `uᵢ uᵢ*` onto the `i`-th eigenvector `hA.eigenvectorBasis i`
of a Hermitian matrix `A`. -/
def eigenprojector (hA : A.IsHermitian) (i : n) : Matrix n n 𝕜 :=
  vecMulVec ⇑(hA.eigenvectorBasis i) (star ⇑(hA.eigenvectorBasis i))

/-- Unfolds `hA.eigenprojector₀ k` as `vecMulVec` of the `k`-th sorted eigenvector and its star. -/
theorem eigenprojector₀_def (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k = vecMulVec ⇑(hA.eigenvectorBasis₀ k) (star ⇑(hA.eigenvectorBasis₀ k)) :=
  (rfl)

/-- Unfolds `hA.eigenprojector i` as `vecMulVec` of the `i`-th eigenvector and its star. -/
theorem eigenprojector_def (hA : A.IsHermitian) (i : n) :
    hA.eigenprojector i = vecMulVec ⇑(hA.eigenvectorBasis i) (star ⇑(hA.eigenvectorBasis i)) :=
  (rfl)

/-- Reindexing `hA.eigenprojector` by the canonical finite equivalence recovers
`hA.eigenprojector₀`. -/
@[simp]
theorem eigenprojector_apply_equivOfCardEq (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenprojector (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) k) =
      hA.eigenprojector₀ k := by
  simp [eigenprojector, eigenprojector₀]

/-- Each `n`-indexed eigenprojector is the corresponding sorted eigenprojector. -/
theorem eigenprojector_eq_eigenprojector₀ (hA : A.IsHermitian) (i : n) :
    hA.eigenprojector i =
      hA.eigenprojector₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i) := by
  simp [eigenprojector, eigenprojector₀, hA.eigenvectorBasis_eq_eigenvectorBasis₀]

/-- `hA.eigenprojector₀ k` is the rank-one Hermitian projector of `hA.eigenvectorBasis₀ k`. -/
theorem eigenprojector₀_eq_rankOneHermitianProjector (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k = TauCeti.rankOneHermitianProjector ⇑(hA.eigenvectorBasis₀ k) := by
  rw [TauCeti.rankOneHermitianProjector_def, eigenprojector₀_def,
    hA.dotProduct_star_eigenvectorBasis₀_self, inv_one, one_smul]

/-- `hA.eigenprojector i` is the rank-one Hermitian projector of `hA.eigenvectorBasis i`. -/
theorem eigenprojector_eq_rankOneHermitianProjector (hA : A.IsHermitian) (i : n) :
    hA.eigenprojector i = TauCeti.rankOneHermitianProjector ⇑(hA.eigenvectorBasis i) := by
  rw [hA.eigenprojector_eq_eigenprojector₀, hA.eigenvectorBasis_eq_eigenvectorBasis₀,
    hA.eigenprojector₀_eq_rankOneHermitianProjector]

/-- Every sorted spectral projector `hA.eigenprojector₀ k` lies in the Hermitian projector locus
(self-adjoint idempotent matrices of trace one). -/
theorem eigenprojector₀_mem_hermitianProjectorLocus (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k ∈ TauCeti.hermitianProjectorLocus n 𝕜 := by
  rw [hA.eigenprojector₀_eq_rankOneHermitianProjector]
  exact TauCeti.rankOneHermitianProjector_mem_hermitianProjectorLocus
    (by simp [hA.dotProduct_star_eigenvectorBasis₀_self])

/-- Every sorted spectral projector is a star projection. -/
theorem isStarProjection_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsStarProjection (hA.eigenprojector₀ k) :=
  (TauCeti.mem_hermitianProjectorLocus.mp (hA.eigenprojector₀_mem_hermitianProjectorLocus k)).1

/-- Every sorted spectral projector is self-adjoint. -/
theorem isSelfAdjoint_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    IsSelfAdjoint (hA.eigenprojector₀ k) :=
  (hA.isStarProjection_eigenprojector₀ k).isSelfAdjoint

/-- Every sorted spectral projector is Hermitian. -/
theorem isHermitian_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    (hA.eigenprojector₀ k).IsHermitian := by
  simpa [IsHermitian, star_eq_conjTranspose] using (hA.isSelfAdjoint_eigenprojector₀ k).star_eq

/-- Every sorted spectral projector is idempotent. -/
@[simp]
theorem eigenprojector₀_mul_self (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k * hA.eigenprojector₀ k = hA.eigenprojector₀ k :=
  (hA.isStarProjection_eigenprojector₀ k).isIdempotentElem.eq

/-- Spectral projectors at distinct sorted indices are mutually orthogonal. -/
theorem eigenprojector₀_mul_of_ne (hA : A.IsHermitian) {j k : Fin (Fintype.card n)}
    (hjk : j ≠ k) : hA.eigenprojector₀ j * hA.eigenprojector₀ k = 0 := by
  rw [eigenprojector₀_def, eigenprojector₀_def, vecMulVec_mul_vecMulVec,
    hA.dotProduct_star_eigenvectorBasis₀_of_ne hjk]
  simp

/-- Multiplication table of the sorted spectral projectors. -/
theorem eigenprojector₀_mul_eigenprojector₀ (hA : A.IsHermitian)
    (j k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ j * hA.eigenprojector₀ k =
      if j = k then hA.eigenprojector₀ j else 0 := by
  split_ifs with hjk
  · subst hjk
    exact hA.eigenprojector₀_mul_self j
  · exact hA.eigenprojector₀_mul_of_ne hjk

/-- Action of `hA.eigenprojector₀ k` on a vector `x : n → 𝕜`. -/
theorem eigenprojector₀_mulVec (hA : A.IsHermitian) (k : Fin (Fintype.card n)) (x : n → 𝕜) :
    hA.eigenprojector₀ k *ᵥ x =
      (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ x) • ⇑(hA.eigenvectorBasis₀ k) := by
  rw [eigenprojector₀_def, vecMulVec_mulVec, op_smul_eq_smul]

/-- `hA.eigenprojector₀ k` fixes the `k`-th sorted eigenvector. -/
@[simp]
theorem eigenprojector₀_mulVec_eigenvectorBasis₀_self (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k *ᵥ ⇑(hA.eigenvectorBasis₀ k) = ⇑(hA.eigenvectorBasis₀ k) := by
  simp [hA.eigenprojector₀_mulVec]

/-- `hA.eigenprojector₀ j` annihilates the `k`-th sorted eigenvector for `j ≠ k`. -/
theorem eigenprojector₀_mulVec_eigenvectorBasis₀_of_ne (hA : A.IsHermitian)
    {j k : Fin (Fintype.card n)} (hjk : j ≠ k) :
    hA.eigenprojector₀ j *ᵥ ⇑(hA.eigenvectorBasis₀ k) = 0 := by
  simp [hA.eigenprojector₀_mulVec, hA.dotProduct_star_eigenvectorBasis₀_of_ne hjk]

/-- Every sorted spectral projector has trace `1`. -/
@[simp]
theorem trace_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    (hA.eigenprojector₀ k).trace = 1 :=
  (TauCeti.mem_hermitianProjectorLocus.mp (hA.eigenprojector₀_mem_hermitianProjectorLocus k)).2

/-- Every `n`-indexed spectral projector has trace `1`. -/
@[simp]
theorem trace_eigenprojector (hA : A.IsHermitian) (i : n) :
    (hA.eigenprojector i).trace = 1 := by
  rw [hA.eigenprojector_eq_eigenprojector₀, hA.trace_eigenprojector₀]

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
theorem trace_eigenprojector₀_mul_eigenprojector₀_mul (hA : A.IsHermitian)
    (j k : Fin (Fintype.card n)) (B C : Matrix n n 𝕜) :
    (hA.eigenprojector₀ k * B * hA.eigenprojector₀ j * C).trace =
      (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ (B *ᵥ ⇑(hA.eigenvectorBasis₀ j))) *
        (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ (C *ᵥ ⇑(hA.eigenvectorBasis₀ k))) := by
  rw [eigenprojector₀_def, eigenprojector₀_def, Matrix.mul_assoc (vecMulVec _ _) B,
    mul_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul, trace_vecMulVec,
    dotProduct_comm ⇑(hA.eigenvectorBasis₀ k), smul_vecMul, smul_dotProduct, smul_eq_mul,
    dotProduct_mulVec, dotProduct_mulVec]

/-- **Resolution of the identity** by the sorted rank-one spectral projectors. -/
@[simp]
theorem sum_eigenprojector₀ (hA : A.IsHermitian) :
    ∑ k, hA.eigenprojector₀ k = (1 : Matrix n n 𝕜) := by
  ext i j
  have hcol := congrFun (hA.sum_dotProduct_smul_eigenvectorBasis₀ (Pi.single j 1)) i
  simpa [eigenprojector₀_def, Finset.sum_apply, vecMulVec_apply, Pi.smul_apply, Matrix.one_apply,
    Pi.single_apply, mul_comm, eq_comm] using hcol

/-- **Resolution of the identity** by the `n`-indexed rank-one spectral projectors. -/
@[simp]
theorem sum_eigenprojector (hA : A.IsHermitian) :
    ∑ i, hA.eigenprojector i = (1 : Matrix n n 𝕜) := by
  simp_rw [hA.eigenprojector_eq_eigenprojector₀]
  rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm,
    hA.sum_eigenprojector₀]

/-- Left multiplication of `hA.eigenprojector₀ k` by `A` scales by `hA.eigenvalues₀ k`. -/
@[simp]
theorem mul_eigenprojector₀ (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    A * hA.eigenprojector₀ k = (hA.eigenvalues₀ k : 𝕜) • hA.eigenprojector₀ k := by
  rw [eigenprojector₀_def, mul_vecMulVec, hA.mulVec_eigenvectorBasis₀_coe, smul_vecMulVec]

/-- Right multiplication of `hA.eigenprojector₀ k` by `A` scales by `hA.eigenvalues₀ k`. -/
@[simp]
theorem eigenprojector₀_mul (hA : A.IsHermitian) (k : Fin (Fintype.card n)) :
    hA.eigenprojector₀ k * A = (hA.eigenvalues₀ k : 𝕜) • hA.eigenprojector₀ k := by
  have h := congrArg Matrix.conjTranspose (hA.mul_eigenprojector₀ k)
  rwa [conjTranspose_mul, conjTranspose_smul, hA.eq, (hA.isHermitian_eigenprojector₀ k).eq,
    RCLike.star_def, RCLike.conj_ofReal] at h

/-- **Spectral decomposition** of a Hermitian matrix as a linear combination of its sorted
rank-one spectral projectors. -/
theorem sum_eigenvalues₀_smul_eigenprojector₀ (hA : A.IsHermitian) :
    ∑ k, (hA.eigenvalues₀ k : 𝕜) • hA.eigenprojector₀ k = A := by
  simp_rw [← hA.mul_eigenprojector₀, ← Matrix.mul_sum, hA.sum_eigenprojector₀, Matrix.mul_one]

/-- The trace of `hA.eigenprojector₀ k * A` recovers `(hA.eigenvalues₀ k : 𝕜)`. -/
theorem trace_eigenprojector₀_mul_self_matrix (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    (hA.eigenprojector₀ k * A).trace = (hA.eigenvalues₀ k : 𝕜) := by
  rw [hA.eigenprojector₀_mul, trace_smul, hA.trace_eigenprojector₀, smul_eq_mul, mul_one]

/-! ### Canonical projector at a simple eigenvalue -/

/-- Any vector `v` satisfying `A *ᵥ v = (hA.eigenvalues₀ k : 𝕜) • v` is orthogonal to every sorted
eigenvector `hA.eigenvectorBasis₀ j` whose eigenvalue differs from `hA.eigenvalues₀ k`. -/
theorem dotProduct_star_eigenvectorBasis₀_eq_zero_of_mulVec (hA : A.IsHermitian)
    {j k : Fin (Fintype.card n)} (hne : hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k)
    {v : n → 𝕜} (hv : A *ᵥ v = (hA.eigenvalues₀ k : 𝕜) • v) :
    star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v = 0 := by
  have h1 : (hA.eigenvalues₀ j : 𝕜) * (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v) =
      (hA.eigenvalues₀ k : 𝕜) * (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v) := by
    calc
      (hA.eigenvalues₀ j : 𝕜) * (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v)
          = ((hA.eigenvalues₀ j : 𝕜) • star ⇑(hA.eigenvectorBasis₀ j)) ⬝ᵥ v := by
            rw [smul_dotProduct, smul_eq_mul]
      _ = (star ⇑(hA.eigenvectorBasis₀ j) ᵥ* A) ⬝ᵥ v := by
            rw [hA.star_eigenvectorBasis₀_vecMul]
      _ = star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ (A *ᵥ v) := (dotProduct_mulVec _ _ _).symm
      _ = (hA.eigenvalues₀ k : 𝕜) * (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v) := by
            rw [hv, dotProduct_smul, smul_eq_mul]
  have hdiff : ((hA.eigenvalues₀ j : 𝕜) - (hA.eigenvalues₀ k : 𝕜)) *
      (star ⇑(hA.eigenvectorBasis₀ j) ⬝ᵥ v) = 0 := by
    rwa [sub_mul, sub_eq_zero]
  exact (mul_eq_zero.mp hdiff).resolve_left
    (sub_ne_zero.mpr ((RCLike.ofReal_injective (K := 𝕜)).ne hne))

/-- At a simple sorted eigenvalue `hA.eigenvalues₀ k`, every eigenvector `v` for
`hA.eigenvalues₀ k` is a scalar multiple of `hA.eigenvectorBasis₀ k`. -/
theorem eq_smul_eigenvectorBasis₀_of_mulVec (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k)
    {v : n → 𝕜} (hv : A *ᵥ v = (hA.eigenvalues₀ k : 𝕜) • v) :
    v = (star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ v) • ⇑(hA.eigenvectorBasis₀ k) := by
  conv_lhs => rw [← hA.sum_dotProduct_smul_eigenvectorBasis₀ v]
  refine Finset.sum_eq_single k (fun j _ hjk ↦ ?_) (fun hk' ↦ (hk' (Finset.mem_univ k)).elim)
  rw [hA.dotProduct_star_eigenvectorBasis₀_eq_zero_of_mulVec (hk j hjk) hv, zero_smul]

/-- **Basis independence at a simple eigenvalue.** If `hA.eigenvalues₀ k` is simple, then
`hA.eigenprojector₀ k` agrees with `TauCeti.rankOneHermitianProjector v` for any nonzero
eigenvector `v` with eigenvalue `hA.eigenvalues₀ k`. -/
theorem eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k)
    {v : n → 𝕜} (hv_ne : v ≠ 0) (hv : A *ᵥ v = (hA.eigenvalues₀ k : 𝕜) • v) :
    hA.eigenprojector₀ k = TauCeti.rankOneHermitianProjector v := by
  have hv_eq := hA.eq_smul_eigenvectorBasis₀_of_mulVec hk hv
  have hc : star ⇑(hA.eigenvectorBasis₀ k) ⬝ᵥ v ≠ 0 := by
    intro h0
    apply hv_ne
    rw [hv_eq, h0, zero_smul]
  rw [hv_eq, TauCeti.rankOneHermitianProjector_smul hc,
    ← hA.eigenprojector₀_eq_rankOneHermitianProjector]

/-- At a simple sorted eigenvalue `hA.eigenvalues₀ k`, any unit eigenvector `v` (`star v ⬝ᵥ v = 1`)
for `hA.eigenvalues₀ k` satisfies `hA.eigenprojector₀ k = vecMulVec v (star v)`. -/
theorem eigenprojector₀_eq_vecMulVec_of_mulVec (hA : A.IsHermitian)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k)
    {v : n → 𝕜} (hunit : star v ⬝ᵥ v = 1) (hv : A *ᵥ v = (hA.eigenvalues₀ k : 𝕜) • v) :
    hA.eigenprojector₀ k = vecMulVec v (star v) := by
  have hv_ne : v ≠ 0 := by
    rintro rfl
    simp at hunit
  rw [hA.eigenprojector₀_eq_rankOneHermitianProjector_of_mulVec hk hv_ne hv,
    TauCeti.rankOneHermitianProjector_def, hunit, inv_one, one_smul]

/-- If `A` is both Hermitian and symmetric (`Aᵀ = A`, for instance a real symmetric matrix embedded
into `Matrix n n ℂ`), then its spectral projector at any simple sorted eigenvalue is symmetric. -/
theorem isSymm_eigenprojector₀ (hA : A.IsHermitian) (hsymm : A.IsSymm)
    {k : Fin (Fintype.card n)} (hk : ∀ j ≠ k, hA.eigenvalues₀ j ≠ hA.eigenvalues₀ k) :
    (hA.eigenprojector₀ k).IsSymm := by
  set u : n → 𝕜 := ⇑(hA.eigenvectorBasis₀ k)
  have hmap : A.map star = A := by
    rw [← conjTranspose_transpose, hA.eq, hsymm.eq]
  have hv : A *ᵥ star u = (hA.eigenvalues₀ k : 𝕜) • star u := by
    have h := congrArg star (hA.mulVec_eigenvectorBasis₀_coe k)
    have hmul : star (A *ᵥ u) = A.map star *ᵥ star u := by
      ext i
      simp [mulVec, dotProduct]
    rwa [hmul, hmap, star_smul, RCLike.star_def, RCLike.conj_ofReal] at h
  have hunit : star (star u) ⬝ᵥ star u = 1 := by
    rw [star_star, dotProduct_comm, hA.dotProduct_star_eigenvectorBasis₀_self]
  have heq := hA.eigenprojector₀_eq_vecMulVec_of_mulVec hk hunit hv
  rw [IsSymm]
  conv_lhs => rw [eigenprojector₀_def, transpose_vecMulVec]
  rw [heq, star_star]

end IsHermitian

end Matrix
