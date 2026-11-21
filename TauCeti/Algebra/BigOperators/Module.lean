/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Module

/-!
# Summation by parts on positive integer intervals

Mathlib's `Finset.sum_range_by_parts'` differences the module factor in `∑ i ∈ range n, f i • g i`.
Arithmetic sums over `Icc 1 (m + 1)` index their partial sums from `1` rather than `0`; reindexing
`range (m + 1)` along `i ↦ 1 + i` transfers `Finset.sum_range_by_parts'` directly to
`Icc 1 (m + 1)`.

## Main results

* `Finset.sum_Icc_succ_by_parts'`: summation by parts on `Icc 1 (m + 1)`, differencing the module
  factor `g` against the partial sums `i ↦ ∑ j ∈ Icc 1 i, f j`.
-/

public section

namespace Finset

/-- **Summation by parts** on `Icc 1 (m + 1)`, differencing the second (module) factor against the
partial sums `∑ j ∈ Icc 1 i, f j`: the `Icc 1`-indexed counterpart of
`Finset.sum_range_by_parts'`. -/
theorem sum_Icc_succ_by_parts' {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (f : ℕ → R) (g : ℕ → M) (m : ℕ) :
    ∑ i ∈ Icc 1 (m + 1), f i • g i =
      (∑ j ∈ Icc 1 (m + 1), f j) • g (m + 1) -
        ∑ i ∈ Icc 1 m, (∑ j ∈ Icc 1 i, f j) • (g (i + 1) - g i) := by
  simp_rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simpa only [Nat.add_sub_cancel, Nat.add_comm 1, Nat.add_assoc] using
    sum_range_by_parts' (fun i ↦ f (1 + i)) (fun i ↦ g (1 + i)) (m + 1)

end Finset
