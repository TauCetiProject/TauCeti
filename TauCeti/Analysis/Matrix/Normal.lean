/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.InnerProductSpace.NormalOperator

/-!
# Unitary diagonalization of commuting normal matrices

A complex square matrix `A` is **normal** when it commutes with its conjugate transpose,
`IsStarNormal A`. The spectral theorem for normal matrices says that such a matrix is unitarily
diagonalizable: `star U * A * U` is diagonal for some unitary `U`. Mathlib proves this for Hermitian
matrices (`Matrix.IsHermitian.spectral_theorem`); this file extends it to normal ones as the
singleton case of `TauCeti.exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal`.
The columns of `U` are an orthonormal basis of eigenvectors of `A`.
The family theorem gives a single unitary diagonalizer for any commuting family of complex
normal matrices; the family need not be finite.

Unitary matrices are normal, so in particular every unitary matrix is conjugate within the unitary
group to a diagonal one. This is the statement that every element of `U(n)` lies in a conjugate of
the diagonal torus.

## Main results

* `TauCeti.exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal`: a common unitary
  diagonalizer for any commuting family of complex normal matrices.

* `Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal`: **the spectral theorem for normal
  matrices**, a normal complex matrix is diagonalized by a unitary matrix.

## References

* S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer (2015), Theorem 7.24 (the complex
  spectral theorem).
-/

public section

namespace TauCeti

open Matrix Module

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- A commuting family of complex normal matrices has a common unitary diagonalizer.
The index type of the family need not be finite. -/
theorem exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal
    (A : ι → Matrix n n ℂ) (hA : ∀ i, IsStarNormal (A i))
    (hC : Pairwise (fun i j => Commute (A i) (A j))) :
    ∃ U ∈ unitaryGroup n ℂ, ∃ d : ι → n → ℂ,
      ∀ i, star U * A i * U = diagonal (d i) := by
  have hT (i : ι) : IsStarNormal (toEuclideanLin (A i)) := by
    have := hA i
    infer_instance
  have hcomm : Pairwise (fun i j => Commute (toEuclideanLin (A i))
      (toEuclideanLin (A j))) := by
    intro i j hij
    simpa only [commute_iff_eq, Module.End.mul_eq_comp, ← toLpLin_mul_same] using
      congrArg toEuclideanLin (hC hij).eq
  obtain ⟨b, d, hb⟩ := TauCeti.exists_orthonormalBasis_apply_eq_smul_of_pairwise_commute
    (fun i => toEuclideanLin (A i)) hT hcomm (κ := n) finrank_euclideanSpace.symm
  let s := (EuclideanSpace.basisFun n ℂ).toBasis
  have hU : s.toMatrix b.toBasis ∈ unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b
  refine ⟨_, hU, d, fun k => ?_⟩
  -- The inverse change of orthonormal basis is the conjugate transpose.
  have hstar : star (s.toMatrix b.toBasis) = b.toBasis.toMatrix s := by
    rw [← Matrix.mul_one (star _), ← s.toMatrix_mul_toMatrix_flip b.toBasis,
      ← Matrix.mul_assoc, mem_unitaryGroup_iff'.mp hU, Matrix.one_mul]
  have hAk : A k = LinearMap.toMatrix s s (toEuclideanLin (A k)) := by
    rw [toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [hstar, hAk, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  by_cases h : i = j <;> simp [LinearMap.toMatrix_apply, hb, h]

end TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The spectral theorem for normal matrices.** A normal complex matrix is unitarily
diagonalizable: there is a unitary matrix `U` with `star U * A * U` diagonal. -/
theorem exists_mem_unitaryGroup_star_mul_mul_eq_diagonal (A : Matrix n n ℂ) [IsStarNormal A] :
    ∃ U ∈ unitaryGroup n ℂ, ∃ d : n → ℂ, star U * A * U = diagonal d := by
  obtain ⟨U, hU, d, hd⟩ := TauCeti.exists_mem_unitaryGroup_forall_star_mul_mul_eq_diagonal
    (fun _ : Unit => A) (fun _ => inferInstance) (fun _ _ _ => Commute.refl _)
  exact ⟨U, hU, d (), hd ()⟩

end Matrix
