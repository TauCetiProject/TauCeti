/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Linear independence of rows in partitioned matrices

This file proves that the rows of a column-partitioned matrix `[A | B]` are linearly independent
as soon as the rows of one of its blocks are: two distinct combinations of the rows already
differ on the columns of that block, so no nontrivial combination of the rows vanishes.

The main instance is a block that is an identity matrix, whose rows are linearly independent by
`Matrix.linearIndependent_row_one`. Consequently a matrix in systematic form has full row rank,
which is what turns a row count into a dimension: over a field, `[I | A]` has as many rows as the
dimension of the code it generates, and `[B | I]` has as many rows as the codimension of the code
it checks.

## Main declarations

* `Matrix.linearIndependent_row_fromCols_of_left`,
  `Matrix.linearIndependent_row_fromCols_of_right`: the rows of `[A | B]` are linearly
  independent when those of `A`, respectively `B`, are.
* `Matrix.linearIndependent_row_one_fromCols`: the rows of `[I | A]` are linearly independent.
* `Matrix.linearIndependent_row_fromCols_one`: the rows of `[B | I]` are linearly
  independent.
-/

public section

namespace Matrix

variable {R m n₁ n₂ : Type*} [Semiring R]

/-- If the rows of the left block `A` are linearly independent, so are the rows of `[A | B]`. -/
theorem linearIndependent_row_fromCols_of_left {A : Matrix m n₁ R}
    (hA : LinearIndependent R A.row) (B : Matrix m n₂ R) :
    LinearIndependent R (fromCols A B).row :=
  .of_comp (LinearMap.funLeft R R Sum.inl) <| by convert hA using 1; ext; simp

/-- If the rows of the right block `B` are linearly independent, so are the rows of `[A | B]`. -/
theorem linearIndependent_row_fromCols_of_right {B : Matrix m n₂ R}
    (hB : LinearIndependent R B.row) (A : Matrix m n₁ R) :
    LinearIndependent R (fromCols A B).row :=
  .of_comp (LinearMap.funLeft R R Sum.inr) <| by convert hB using 1; ext; simp

/-- The rows of a systematic matrix `[I | A]` are linearly independent. -/
theorem linearIndependent_row_one_fromCols [DecidableEq m] (A : Matrix m n₂ R) :
    LinearIndependent R (fromCols (1 : Matrix m m R) A).row :=
  linearIndependent_row_fromCols_of_left linearIndependent_row_one A

/-- The rows of a systematic matrix `[B | I]` are linearly independent. -/
theorem linearIndependent_row_fromCols_one [DecidableEq m] (B : Matrix m n₁ R) :
    LinearIndependent R (fromCols B (1 : Matrix m m R)).row :=
  linearIndependent_row_fromCols_of_right linearIndependent_row_one B

end Matrix
