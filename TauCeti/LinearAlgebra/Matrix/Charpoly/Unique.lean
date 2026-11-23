/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The characteristic polynomial of a `1 × 1` matrix

For a singleton index type `n` (`[Unique n]`), the characteristic polynomial of `M : Matrix n n R`
is `X - C m`, where `m = M default default` is its only entry (`Matrix.charpoly_of_unique`).

The lemma takes `[Fintype n]` alongside `[Unique n]`, so that it applies with any ambient `Fintype`
instance (such as the one on `Fin 1`).
-/

public section

open Polynomial

namespace Matrix

variable {n R : Type*} [Unique n] [Fintype n] [DecidableEq n] [CommRing R]

/-- **The characteristic polynomial of a `1 × 1` matrix** is `X - C m`, where `m` is its only
entry. -/
theorem charpoly_of_unique (M : Matrix n n R) : M.charpoly = X - C (M default default) := by
  rw [charpoly, det_unique, charmatrix_apply_eq]

end Matrix

end
