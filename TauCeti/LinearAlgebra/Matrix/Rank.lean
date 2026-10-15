/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Matrix rank

This file records general results relating matrix rank to the corresponding linear maps.

## Main results

* `Matrix.rank_eq_card_iff_vecMul_injective` characterizes full row rank by injectivity of right
  multiplication by the matrix.
* `Matrix.rank_add_rank_le_rank_mul_add_card`: Sylvester's rank inequality
  `rank A + rank B ≤ rank (A * B) + n` for an `m × n` matrix `A` and an `n × o` matrix `B`.
* `Matrix.exists_eq_mul_fin_rank`: a rectangular matrix factors through `Fin A.rank`.
* `Matrix.exists_eq_mul_of_rank_le` and `Matrix.rank_le_iff_exists_eq_mul`: a matrix has rank at
  most `r` exactly when it factors through `Fin r`.

-/

public section

namespace Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

/-- A matrix has full row rank exactly when right multiplication by it is injective. -/
theorem rank_eq_card_iff_vecMul_injective (B : Matrix m n K) :
    B.rank = Fintype.card m ↔ Function.Injective B.vecMul := by
  rw [vecMul_injective_iff, rank_eq_finrank_span_row,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

omit [Fintype m] in
/-- Every matrix with finitely many columns over a field factors through a space whose dimension
is its rank. The factorization also applies to a rank-zero matrix, with inner index type `Fin 0`. -/
theorem exists_eq_mul_fin_rank (A : Matrix m n K) :
    ∃ (L : Matrix m (Fin A.rank) K) (R : Matrix (Fin A.rank) n K), A = L * R := by
  classical
  let e : LinearMap.range A.mulVecLin ≃ₗ[K] (Fin A.rank → K) :=
    (Module.finBasis K (LinearMap.range A.mulVecLin)).equivFun
  let l := (LinearMap.range A.mulVecLin).subtype.comp e.symm.toLinearMap
  let r := e.toLinearMap.comp A.mulVecLin.rangeRestrict
  have h : l.comp r = A.mulVecLin := by
    ext v i
    simp [l, r, LinearMap.comp_apply]
  refine ⟨LinearMap.toMatrix' l, LinearMap.toMatrix' r, ?_⟩
  rw [← LinearMap.toMatrix'_comp, h, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

omit [Fintype m] in
/-- A rank bound gives a factorization through `Fin r`, padding an exact-rank factorization
with zero columns and rows when necessary. -/
theorem exists_eq_mul_of_rank_le (A : Matrix m n K) {r : ℕ} (h : A.rank ≤ r) :
    ∃ (L : Matrix m (Fin r) K) (R : Matrix (Fin r) n K), A = L * R := by
  classical
  obtain ⟨L, R, hA⟩ := A.exists_eq_mul_fin_rank
  let e : Fin r ≃ Fin A.rank ⊕ Fin (r - A.rank) :=
    (finCongr (Nat.add_sub_of_le h).symm).trans finSumFinEquiv.symm
  refine ⟨(fromCols L (0 : Matrix m (Fin (r - A.rank)) K)).submatrix id e,
    (fromRows R (0 : Matrix (Fin (r - A.rank)) n K)).submatrix e id, ?_⟩
  simpa only [submatrix_mul_equiv, fromCols_mul_fromRows, Matrix.zero_mul, add_zero,
    submatrix_id_id] using hA

omit [Fintype m] in
/-- Matrix rank is at most `r` if and only if the matrix is a product with inner index `Fin r`.
In particular, rank is the least possible inner dimension of a factorization. -/
theorem rank_le_iff_exists_eq_mul (A : Matrix m n K) (r : ℕ) :
    A.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) K) (R : Matrix (Fin r) n K), A = L * R := by
  refine ⟨A.exists_eq_mul_of_rank_le, ?_⟩
  rintro ⟨L, R, rfl⟩
  exact (rank_mul_le_left L R).trans (by simpa using L.rank_le_card_width)

omit [Fintype m] in
/-- **Sylvester's rank inequality**: for an `m × n` matrix `A` and an `n × o` matrix `B` over a
field, `rank A + rank B ≤ rank (A * B) + n`. Equivalently, multiplying by `A` lowers the rank of
`B` by at most the nullity of `A`. -/
theorem rank_add_rank_le_rank_mul_add_card {o : Type*} [Fintype o] (A : Matrix m n K)
    (B : Matrix n o K) : A.rank + B.rank ≤ (A * B).rank + Fintype.card n := by
  classical
  set S := LinearMap.range B.mulVecLin
  set g := A.mulVecLin.domRestrict S
  have hrange : (A * B).rank = Module.finrank K (LinearMap.range g) := by
    rw [rank, mulVecLin_mul, LinearMap.range_comp, LinearMap.range_domRestrict]
  have hker : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K (LinearMap.ker A.mulVecLin) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := S.subtype.restrict (p := LinearMap.ker g) (q := LinearMap.ker A.mulVecLin)
        fun x hx ↦ by simpa [g] using hx)
      fun x y h ↦ Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  have hg := g.finrank_range_add_finrank_ker
  have hA := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hA
  have hB : B.rank = Module.finrank K S := rfl
  rw [rank, hB, hrange]
  omega

end Matrix
