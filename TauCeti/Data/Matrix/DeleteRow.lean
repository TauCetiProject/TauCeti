/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Deleting a row of a matrix

For a matrix `G` with rows indexed by `ρ` and a row index `r`, the matrix `Matrix.deleteRow G r`
has rows indexed by `{s : ρ // s ≠ r}` and retains every row of `G` except row `r`. It is the
submatrix of `G` along the inclusion of the remaining row indices.

## Main definitions

* `Matrix.deleteRow` deletes one row of a matrix.
-/

public section

variable {ι ρ R : Type*}

namespace TauCeti

/-- The matrix obtained from `G` by deleting the row indexed by `r`. -/
def _root_.Matrix.deleteRow (G : Matrix ρ ι R) (r : ρ) : Matrix {s : ρ // s ≠ r} ι R :=
  G.submatrix Subtype.val id

/-- Evaluation of a matrix after deleting a row. -/
@[simp]
theorem _root_.Matrix.deleteRow_apply (G : Matrix ρ ι R) (r : ρ) (s : {s : ρ // s ≠ r})
    (i : ι) :
    G.deleteRow r s i = G s i := (rfl)

/-- A retained row of `deleteRow G r` is the corresponding row of `G`. -/
@[simp]
theorem _root_.Matrix.row_deleteRow (G : Matrix ρ ι R) (r : ρ) (s : {s : ρ // s ≠ r}) :
    (G.deleteRow r).row s = G.row s := (rfl)

end TauCeti
