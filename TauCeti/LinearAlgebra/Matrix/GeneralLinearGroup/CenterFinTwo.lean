/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Subgroup.center (GL (Fin 2) R)` occurs in the statement below, and
-- `Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar` is the classification it reads.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
-- Non-public: `TauCeti.mem_range_scalar_fin_two_iff` turns being scalar into entry equations, in
-- the proof only.
import TauCeti.LinearAlgebra.Matrix.Commute

/-!
# The centre of `GL₂` in terms of matrix entries

The centre of `GL n R` consists of the scalar matrices, which is Mathlib's
`Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar`. In size two a matrix is scalar
exactly when three entry equations hold, so centrality of an invertible `2 × 2` matrix is decided
by reading off its two off-diagonal entries and its two diagonal entries.

This entry form is what a group acting through `2 × 2` coefficient matrices needs: the kernel of
such an action is computed by equations on the coefficients, and matching it with the centre turns
the action into a faithful action of `PGL₂`.

## Main results

* `Matrix.GeneralLinearGroup.mem_center_iff_entries`: an element of `GL (Fin 2) R` is central
  exactly when its off-diagonal entries vanish and its two diagonal entries agree.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R] {A : GL (Fin 2) R}

/-- **An invertible `2 × 2` matrix is central exactly when it is scalar**, in entries: its
off-diagonal entries vanish and its two diagonal entries agree. -/
theorem mem_center_iff_entries :
    A ∈ Subgroup.center (GL (Fin 2) R) ↔
      (A : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
        (A : Matrix (Fin 2) (Fin 2) R) 0 0 = (A : Matrix (Fin 2) (Fin 2) R) 1 1 :=
  mem_center_iff_val_mem_range_scalar.trans TauCeti.mem_range_scalar_fin_two_iff

end Matrix.GeneralLinearGroup
