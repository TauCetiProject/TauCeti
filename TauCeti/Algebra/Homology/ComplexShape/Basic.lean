/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Neighbouring degrees of complex shapes

Mathlib computes the degree below `n` in the shape `ComplexShape.down ℕ` separately for `n = 0`
(`ChainComplex.next_nat_zero`) and for a successor (`ChainComplex.next_nat_succ`). Since
subtraction on `ℕ` is truncated, both cases are the single formula `n - 1`
(`ChainComplex.next_nat`), which lets statements about a degree `n` of a chain complex name its
neighbour without splitting on `n`.

For the shape `ComplexShape.up' a` on an additive group, in which `i` is related to `i + a`, the
next degree after `i` is `i + a` (`ComplexShape.up'_next`) and the previous one is `i - a`
(`ComplexShape.up'_prev`). These describe the neighbours on the pages of spectral sequences.
-/

public section

/-- The degree below `n` in a chain complex indexed by `ℕ` is `n - 1`, also for `n = 0`. -/
theorem ChainComplex.next_nat (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  cases n with
  | zero => exact ChainComplex.next_nat_zero
  | succ k => exact ChainComplex.next_nat_succ k

/-- In the shape `ComplexShape.up' a`, the degree after `i` is `i + a`. -/
@[simp]
theorem ComplexShape.up'_next {α : Type*} [AddRightCancelSemigroup α] (a i : α) :
    (ComplexShape.up' a).next i = i + a :=
  (ComplexShape.up' a).next_eq' rfl

/-- In the shape `ComplexShape.up' a` on an additive group, the degree before `i` is `i - a`. -/
@[simp]
theorem ComplexShape.up'_prev {α : Type*} [AddGroup α] (a i : α) :
    (ComplexShape.up' a).prev i = i - a :=
  (ComplexShape.up' a).prev_eq' (sub_add_cancel i a)
