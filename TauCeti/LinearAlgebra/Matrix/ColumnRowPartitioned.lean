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

* `Matrix.linearIndependent_row_one_fromCols`: the rows of `[I | A]` are linearly independent.
* `Matrix.linearIndependent_row_fromCols_one`: the rows of `[B | I]` are linearly
  independent.
-/

public section

namespace Matrix

variable {R ρ τ : Type*} [Semiring R]

/-- The rows of a systematic matrix `[I | A]` are linearly independent. -/
theorem linearIndependent_row_one_fromCols [DecidableEq ρ] (A : Matrix ρ τ R) :
    LinearIndependent R (fromCols (1 : Matrix ρ ρ R) A).row :=
  .of_comp (LinearMap.funLeft R R Sum.inl) <| by
    convert Pi.linearIndependent_single_one ρ R using 1
    ext i j
    simp only [Function.comp_apply, LinearMap.funLeft_apply, row_apply, fromCols_apply_inl,
      one_apply, Pi.single_apply, eq_comm]

/-- The rows of a systematic matrix `[B | I]` are linearly independent. -/
theorem linearIndependent_row_fromCols_one [DecidableEq τ] (B : Matrix τ ρ R) :
    LinearIndependent R (fromCols B (1 : Matrix τ τ R)).row :=
  .of_comp (LinearMap.funLeft R R Sum.inr) <| by
    convert Pi.linearIndependent_single_one τ R using 1
    ext i j
    simp only [Function.comp_apply, LinearMap.funLeft_apply, row_apply, fromCols_apply_inr,
      one_apply, Pi.single_apply, eq_comm]

end Matrix
