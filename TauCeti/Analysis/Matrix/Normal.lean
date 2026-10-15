/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.NormalOperator

/-!
# Unitary diagonalization of normal matrices

A complex square matrix `A` is **normal** when it commutes with its conjugate transpose,
`IsStarNormal A`. The spectral theorem for normal matrices says that such a matrix is unitarily
diagonalizable: `star U * A * U` is diagonal for some unitary `U`. Mathlib proves this for Hermitian
matrices (`Matrix.IsHermitian.spectral_theorem`); this file extends it to normal ones, by reading
the spectral theorem for normal operators
(`LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal`) in the standard basis of
`EuclideanSpace ℂ n`. The columns of `U` are an orthonormal basis of eigenvectors of `A`.

Unitary matrices are normal, so in particular every unitary matrix is conjugate within the unitary
group to a diagonal one. This is the statement that every element of `U(n)` lies in a conjugate of
the diagonal torus.

## Main results

* `Matrix.isStarNormal_toEuclideanLin`: a normal matrix acts on `EuclideanSpace 𝕜 n` as a normal
  operator.
* `Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal`: **the spectral theorem for normal
  matrices**, a normal complex matrix is diagonalized by a unitary matrix.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The operator of a normal matrix on `EuclideanSpace 𝕜 n` is normal. -/
instance isStarNormal_toEuclideanLin {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) [IsStarNormal A] :
    IsStarNormal (toEuclideanLin A) where
  star_comm_self := by
    have h : Aᴴ * A = A * Aᴴ := star_comm_self' A
    rw [commute_iff_eq, LinearMap.star_eq_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← toLpLin_mul_same, ← toLpLin_mul_same, h]

/-- **The spectral theorem for normal matrices.** A normal complex matrix is unitarily
diagonalizable: there is a unitary matrix `U` with `star U * A * U` diagonal. -/
theorem exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (A : Matrix n n ℂ) [IsStarNormal A] :
    ∃ U ∈ unitaryGroup n ℂ, ∃ d : n → ℂ, star U * A * U = diagonal d := by
  obtain ⟨b, μ, hb⟩ := LinearMap.exists_orthonormalBasis_apply_eq_smul_of_isStarNormal
    (toEuclideanLin A) (ι := n) finrank_euclideanSpace.symm
  -- `U` is the change of basis from the eigenbasis `b` to the standard basis `s`.
  set s := (EuclideanSpace.basisFun n ℂ).toBasis
  have hU : s.toMatrix b.toBasis ∈ unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b
  refine ⟨_, hU, μ, ?_⟩
  -- Its inverse `star U` is the change of basis the other way.
  have hstar : star (s.toMatrix b.toBasis) = b.toBasis.toMatrix s := by
    rw [← Matrix.mul_one (star _), ← s.toMatrix_mul_toMatrix_flip b.toBasis, ← Matrix.mul_assoc,
      (mem_unitaryGroup_iff'.mp hU), Matrix.one_mul]
  -- So `star U * A * U` is the matrix of `A` in the eigenbasis, which is diagonal.
  have hA : A = LinearMap.toMatrix s s (toEuclideanLin A) := by
    rw [toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [hstar, hA, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  by_cases h : i = j <;> simp [LinearMap.toMatrix_apply, hb, h]

end Matrix
