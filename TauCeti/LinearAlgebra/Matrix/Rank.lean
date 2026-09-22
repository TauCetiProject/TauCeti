/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Matrix rank

This file records general results relating matrix rank to the corresponding linear maps.

## Main results

* `Matrix.rank_eq_card_iff_vecMul_injective` characterizes full row rank by injectivity of right
  multiplication by the matrix.
* `Matrix.rank_add_rank_le_rank_mul_add_card`: Sylvester's rank inequality
  `rank A + rank B ≤ rank (A * B) + n` for an `m × n` matrix `A` and an `n × o` matrix `B`.

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
