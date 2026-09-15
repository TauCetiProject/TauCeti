/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear independence of rows in partitioned matrices

This file proves that the rows of a column-partitioned matrix are linearly independent when one
of its blocks is an identity matrix. The identity block already separates the row indices: two
distinct combinations of the rows differ on the identity columns, so no nontrivial combination
of the rows vanishes.

Consequently a matrix in systematic form has full row rank, which is what turns a row count into
a dimension: over a field, `[I | A]` has as many rows as the dimension of the code it generates,
and `[B | I]` has as many rows as the codimension of the code it checks.

## Main declarations

* `Matrix.linearIndependent_row_fromCols_one`: the rows of `[I | A]` are linearly independent.
* `Matrix.linearIndependent_row_fromCols_one_right`: the rows of `[B | I]` are linearly
  independent.
-/

public section

namespace Matrix

variable {R ρ τ : Type*} [Semiring R]

/-- The rows of a systematic matrix `[I | A]` are linearly independent. -/
theorem linearIndependent_row_fromCols_one [Finite ρ] [DecidableEq ρ] (A : Matrix ρ τ R) :
    LinearIndependent R (fromCols (1 : Matrix ρ ρ R) A).row := by
  cases nonempty_fintype ρ
  rw [← vecMul_injective_iff]
  intro a b h
  simpa using congrArg (· ∘ Sum.inl) h

/-- The rows of a systematic matrix `[B | I]` are linearly independent. -/
theorem linearIndependent_row_fromCols_one_right [Finite τ] [DecidableEq τ] (B : Matrix τ ρ R) :
    LinearIndependent R (fromCols B (1 : Matrix τ τ R)).row := by
  cases nonempty_fintype τ
  rw [← vecMul_injective_iff]
  intro a b h
  simpa using congrArg (· ∘ Sum.inr) h

end Matrix
