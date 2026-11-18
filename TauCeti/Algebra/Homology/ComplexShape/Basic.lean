/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Neighbouring degrees of the chain complex shape on `ℕ`

Mathlib computes the degree below `n` in the shape `ComplexShape.down ℕ` separately for `n = 0`
(`ChainComplex.next_nat_zero`) and for a successor (`ChainComplex.next_nat_succ`). Since
subtraction on `ℕ` is truncated, both cases are the single formula `n - 1`
(`ChainComplex.next_nat`), which lets statements about a degree `n` of a chain complex name its
neighbour without splitting on `n`.
-/

public section

/-- The degree below `n` in a chain complex indexed by `ℕ` is `n - 1`, also for `n = 0`. -/
theorem ChainComplex.next_nat (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  cases n with
  | zero => exact ChainComplex.next_nat_zero
  | succ k => exact ChainComplex.next_nat_succ k
