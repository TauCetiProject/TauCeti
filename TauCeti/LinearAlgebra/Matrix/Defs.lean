/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Entrywise maps of matrices

This file complements `Matrix.map_injective` from Mathlib with its surjective counterpart.

## Main results

* `Matrix.map_map_surjInv`, `Matrix.map_surjective`: applying a surjective function entrywise is
  surjective on matrices. The lift by the chosen section `Function.surjInv` commutes with
  transposition, so it lifts symmetric matrices to symmetric matrices.
-/

public section

namespace Matrix

variable {m n α β : Type*}

/-- Lifting a matrix entrywise along the section `Function.surjInv hf` of a surjective `f` and
applying `f` again gives back the matrix. -/
theorem map_map_surjInv {f : α → β} (hf : Function.Surjective f) (M : Matrix m n β) :
    (M.map (Function.surjInv hf)).map f = M :=
  ext fun i j => Function.surjInv_eq hf (M i j)

/-- Applying a surjective function entrywise is surjective on matrices. -/
theorem map_surjective {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective fun M : Matrix m n α => M.map f := fun M =>
  ⟨_, map_map_surjInv hf M⟩

end Matrix
