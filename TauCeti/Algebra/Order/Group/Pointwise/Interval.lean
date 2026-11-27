/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Bounds on iterated sumsets of intervals

The `k`-fold sumset of an interval `[a, b]` is contained in `[k • a, k • b]`.
Only a preorder and monotonicity of addition on both sides are needed.
-/

public section

open scoped Pointwise

namespace Set

/-- The `k`-fold sumset of a closed interval lies between the corresponding multiples of its
endpoints. -/
theorem nsmul_Icc_subset {A : Type*} [AddMonoid A] [Preorder A] [AddLeftMono A]
    [AddRightMono A] (a b : A) (k : ℕ) : k • Icc a b ⊆ Icc (k • a) (k • b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [succ_nsmul]
    exact (add_subset_add ih Subset.rfl).trans (Icc_add_Icc_subset _ _ _ _)

end Set
