/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Linearly independent forms at a nonzero point

A family of `n` linear forms on `K ^ n`, written as coefficient vectors `l i` so that the `i`-th
form sends `x` to `l i ⬝ᵥ x`, is linearly independent exactly when the square matrix with rows
`l i` is invertible. Its kernel is then trivial, so the forms cannot all vanish at a nonzero point.

## Main results

* `LinearIndependent.exists_dotProduct_ne_zero`: `n` linearly independent forms on `K ^ n` do not
  all vanish at a nonzero point.
-/

public section

open Matrix

/-- `n` linearly independent linear forms on `K ^ n` do not all vanish at a nonzero point. -/
theorem LinearIndependent.exists_dotProduct_ne_zero {K ι : Type*} [Field K] [Fintype ι]
    {l : ι → ι → K} (hl : LinearIndependent K l) {x : ι → K} (hx : x ≠ 0) :
    ∃ i, l i ⬝ᵥ x ≠ 0 := by
  classical
  have hinj : Function.Injective (Matrix.of l).mulVec := mulVec_injective_iff_isUnit.mpr <|
    (linearIndependent_row_iff_isUnit (A := Matrix.of l)).mp hl
  by_contra! h
  exact hx <| hinj <| by ext i; simpa [mulVec] using h i
