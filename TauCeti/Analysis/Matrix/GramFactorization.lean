/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Gram factorizations of positive-semidefinite matrices

A square matrix `B` over `𝕜 = ℝ` or `ℂ` is positive semidefinite exactly when it is a Gram matrix
`B = Aᴴ * A`, that is, when `B i j = ⟪aᵢ, aⱼ⟫` for the columns `aᵢ` of some matrix `A`. The number
of rows of `A` can be taken to be any `d ≥ rank B`, and no smaller: the Gram matrix of `n` vectors
in `𝕜ᵈ` has rank at most `d`. Thus the positive-semidefinite matrices of rank at most `d` are
exactly the Gram matrices of configurations of `n` points in `d`-dimensional space.

## Main results

* `Matrix.posSemidef_iff_eq_conjTranspose_mul_self`: `B` is positive semidefinite iff
  `B = Aᴴ * A` for a square matrix `A`.
* `Matrix.PosSemidef.exists_eq_conjTranspose_mul_self_of_rank_le`: a positive-semidefinite matrix
  of rank at most `Fintype.card m` is `Aᴴ * A` for some `A` with rows indexed by `m`.
* `Matrix.posSemidef_and_rank_le_iff_eq_conjTranspose_mul_self`: `B` is positive semidefinite of
  rank at most `Fintype.card m` iff `B = Aᴴ * A` for some `A` with rows indexed by `m`.

## Implementation notes

The square factorization is the C⋆-algebra statement `CStarAlgebra.nonneg_iff_eq_star_mul_self`
for the matrix order. The rank-controlled factorization compresses a square factor `X` through
its rank: a rank factorization `X = L * R` with `d` inner columns gives
`B = Rᴴ * (Lᴴ * L) * R`, and a square factorization `Lᴴ * L = Cᴴ * C` of the `d × d` middle term
turns this into `B = (C * R)ᴴ * (C * R)`.

## References

* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed. (2013), Section 7.2.
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]

/-- A square matrix is positive semidefinite exactly when it is the Gram matrix `Aᴴ * A` of a
square matrix `A`. -/
theorem posSemidef_iff_eq_conjTranspose_mul_self {B : Matrix n n 𝕜} :
    B.PosSemidef ↔ ∃ A : Matrix n n 𝕜, B = Aᴴ * A := by
  classical
  refine ⟨fun hB ↦ ?_, fun ⟨A, hA⟩ ↦ hA ▸ posSemidef_conjTranspose_mul_self A⟩
  obtain ⟨A, hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  exact ⟨A, star_eq_conjTranspose A ▸ hA⟩

/-- A positive-semidefinite matrix of rank at most `Fintype.card m` is the Gram matrix `Aᴴ * A` of
a matrix `A` with rows indexed by `m`. -/
theorem PosSemidef.exists_eq_conjTranspose_mul_self_of_rank_le {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) (h : B.rank ≤ Fintype.card m) : ∃ A : Matrix m n 𝕜, B = Aᴴ * A := by
  classical
  obtain ⟨X, rfl⟩ := posSemidef_iff_eq_conjTranspose_mul_self.mp hB
  rw [rank_conjTranspose_mul_self] at h
  obtain ⟨L, R, rfl⟩ := X.exists_eq_mul_of_rank_le h
  obtain ⟨C, hC⟩ :=
    posSemidef_iff_eq_conjTranspose_mul_self.mp (posSemidef_conjTranspose_mul_self L)
  refine ⟨(C * R).submatrix (Fintype.equivFin m) id, ?_⟩
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_id_id]
  calc (L * R)ᴴ * (L * R) = Rᴴ * (Lᴴ * L) * R := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (C * R)ᴴ * (C * R) := by rw [hC]; simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- A square matrix is positive semidefinite of rank at most `Fintype.card m` exactly when it is
the Gram matrix `Aᴴ * A` of a matrix `A` with rows indexed by `m`, that is, the Gram matrix of a
configuration of points in an `m`-indexed coordinate space. -/
theorem posSemidef_and_rank_le_iff_eq_conjTranspose_mul_self {B : Matrix n n 𝕜} :
    B.PosSemidef ∧ B.rank ≤ Fintype.card m ↔ ∃ A : Matrix m n 𝕜, B = Aᴴ * A := by
  refine ⟨fun ⟨hB, h⟩ ↦ hB.exists_eq_conjTranspose_mul_self_of_rank_le h, ?_⟩
  rintro ⟨A, rfl⟩
  exact ⟨posSemidef_conjTranspose_mul_self A,
    (rank_conjTranspose_mul_self A).trans_le A.rank_le_card_height⟩

end Matrix
