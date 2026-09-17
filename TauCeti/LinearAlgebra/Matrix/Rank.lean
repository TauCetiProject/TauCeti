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

-/

public section

namespace Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

/-- A matrix has full row rank exactly when right multiplication by it is injective. -/
theorem rank_eq_card_iff_vecMul_injective (B : Matrix m n K) :
    B.rank = Fintype.card m ↔ Function.Injective B.vecMul := by
  rw [vecMul_injective_iff, rank_eq_finrank_span_row,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

end Matrix
