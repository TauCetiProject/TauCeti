/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Telescoping bounds for intervals under multiplicative step growth

Along a sequence `f : ℕ → R` in a preordered, not necessarily associative ring with monotone
addition satisfying `c * f k ≤ f (k + 1)` on `Finset.Ico M m` (`M ≤ m`), telescoping gives the
finite-horizon bound `(c - 1) * ∑ j ∈ Finset.Ico M m, f j + f M ≤ f m`.

## Main results

* `TauCeti.sub_one_mul_sum_Ico_add_le_of_mul_le`: finite-horizon `Ico` sum bound from a
  multiplicative step inequality `c * f k ≤ f (k + 1)`.
-/

public section

open Finset

namespace TauCeti

/-- Along a sequence in a preordered, not necessarily associative ring with monotone addition
satisfying `c * f k ≤ f (k + 1)` for `k ∈ Ico M m` (`M ≤ m`),
`(c - 1) * ∑ j ∈ Ico M m, f j + f M ≤ f m`. -/
theorem sub_one_mul_sum_Ico_add_le_of_mul_le {R : Type*} [NonAssocRing R] [Preorder R]
    [IsOrderedAddMonoid R] {f : ℕ → R} {c : R} {M m : ℕ} (hm : M ≤ m)
    (hstep : ∀ k ∈ Ico M m, c * f k ≤ f (k + 1)) :
    (c - 1) * ∑ j ∈ Ico M m, f j + f M ≤ f m := by
  have hle : ∑ k ∈ Ico M m, (c - 1) * f k ≤ ∑ k ∈ Ico M m, (f (k + 1) - f k) :=
    sum_le_sum fun k hk ↦ by
      rw [sub_mul, one_mul]
      exact sub_le_sub_right (hstep k hk) (f k)
  rw [← mul_sum, sum_Ico_sub f hm] at hle
  exact (add_le_add_left hle (f M)).trans_eq (sub_add_cancel (f m) (f M))

end TauCeti
