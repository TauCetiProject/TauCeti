/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Module

import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Summation by parts on positive integer intervals

Mathlib's `Finset.sum_range_by_parts'` differences the module factor in `∑ i ∈ range n, f i • g i`.
Arithmetic sums over `Icc 1 (m + 1)` index their partial sums from `1` rather than `0`; reindexing
`range (m + 1)` along `i ↦ 1 + i` transfers `Finset.sum_range_by_parts'` directly to
`Icc 1 (m + 1)`. Iterating on `Icc 1 (m + 2)` — optionally after subtracting a constant shift `μ`
from the first partial sums so that zero-mean periodic sequences retain bounded iterated partial
sums — expresses `∑ i ∈ Icc 1 (m + 2), f i • g i` in terms of the second forward differences of `g`.

## Main results

* `Finset.sum_Icc_succ_by_parts'`: summation by parts on `Icc 1 (m + 1)`, differencing the module
  factor `g` against the partial sums `i ↦ ∑ j ∈ Icc 1 i, f j`.
* `Finset.sum_Icc_add_two_by_parts'_sub` and `Finset.sum_Icc_add_two_by_parts'`: second-order
  summation by parts on `Icc 1 (m + 2)` with and without a constant shift `μ` subtracted from the
  first partial sums.
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

/-- **Shifted second-order summation by parts** on `Icc 1 (m + 2)`, expressing
`∑ i ∈ Icc 1 (m + 2), f i • g i` in terms of the second forward differences of `g` and the partial
sums `i ↦ ∑ j ∈ Icc 1 i, ((∑ k ∈ Icc 1 j, f k) - μ)` of the `μ`-shifted first partial sums of
`f`. -/
theorem sum_Icc_add_two_by_parts'_sub {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (f : ℕ → R) (g : ℕ → M) (μ : R) (m : ℕ) :
    ∑ i ∈ Icc 1 (m + 2), f i • g i =
      (∑ j ∈ Icc 1 (m + 2), f j) • g (m + 2) - μ • (g (m + 2) - g 1) -
        (∑ j ∈ Icc 1 (m + 1), ((∑ k ∈ Icc 1 j, f k) - μ)) • (g (m + 2) - g (m + 1)) +
        ∑ i ∈ Icc 1 m,
          (∑ j ∈ Icc 1 i, ((∑ k ∈ Icc 1 j, f k) - μ)) •
            ((g (i + 2) - g (i + 1)) - (g (i + 1) - g i)) := by
  have hsbp1 := sum_Icc_succ_by_parts' f g (m + 1)
  have hsplit : ∑ i ∈ Icc 1 (m + 1), (∑ k ∈ Icc 1 i, f k) • (g (i + 1) - g i) =
      ∑ i ∈ Icc 1 (m + 1), ((∑ k ∈ Icc 1 i, f k) - μ) • (g (i + 1) - g i) +
        μ • (g (m + 2) - g 1) := by
    have h_eq (i : ℕ) : (∑ k ∈ Icc 1 i, f k) • (g (i + 1) - g i) =
        ((∑ k ∈ Icc 1 i, f k) - μ) • (g (i + 1) - g i) + μ • (g (i + 1) - g i) := by
      rw [← add_smul, sub_add_cancel]
    simp_rw [h_eq, sum_add_distrib, ← smul_sum, sum_Icc_sub (Nat.le_add_left 1 m) g]
  have hsbp2 := sum_Icc_succ_by_parts'
    (fun j ↦ (∑ k ∈ Icc 1 j, f k) - μ) (fun i ↦ g (i + 1) - g i) m
  rw [hsbp1, hsplit, hsbp2]
  abel

/-- **Second-order summation by parts** on `Icc 1 (m + 2)`, differencing the module factor `g`
twice against the iterated partial sums `i ↦ ∑ j ∈ Icc 1 i, ∑ k ∈ Icc 1 j, f k`. -/
theorem sum_Icc_add_two_by_parts' {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (f : ℕ → R) (g : ℕ → M) (m : ℕ) :
    ∑ i ∈ Icc 1 (m + 2), f i • g i =
      (∑ j ∈ Icc 1 (m + 2), f j) • g (m + 2) -
        (∑ j ∈ Icc 1 (m + 1), ∑ k ∈ Icc 1 j, f k) • (g (m + 2) - g (m + 1)) +
        ∑ i ∈ Icc 1 m,
          (∑ j ∈ Icc 1 i, ∑ k ∈ Icc 1 j, f k) •
            ((g (i + 2) - g (i + 1)) - (g (i + 1) - g i)) := by
  simpa using sum_Icc_add_two_by_parts'_sub f g 0 m

end Finset
