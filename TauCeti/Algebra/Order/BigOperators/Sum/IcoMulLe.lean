/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Basic

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
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    calc (c - 1) * ∑ j ∈ Ico M (m + 1), f j + f M
        = (c - 1) * ∑ j ∈ Ico M m, f j + f M + (c - 1) * f m := by
            rw [sum_Ico_succ_top hm, mul_add, add_right_comm]
      _ ≤ f m + (c - 1) * f m := by
            gcongr
            exact ih fun k hk ↦ hstep k (Ico_subset_Ico_right m.le_succ hk)
      _ = c * f m := by rw [sub_mul, one_mul, add_comm, sub_add_cancel]
      _ ≤ f (m + 1) := hstep m (mem_Ico.2 ⟨hm, m.lt_succ_self⟩)

end TauCeti
