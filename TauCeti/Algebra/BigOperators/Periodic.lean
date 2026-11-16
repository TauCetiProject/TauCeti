/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Nat.Periodic

/-!
# Partial sums of sequences periodic on positive indices

Sequences arising from arithmetic functions regrouped by norm or extended by zero at `0` satisfy
the periodicity relation `a (k + N) = a k` only for `1 ≤ k`, since `a 0` need not agree with `a N`
(for example when `N = 1` and `a 0 = 0 ≠ a 1`). Nevertheless, every shifted block
`∑ j ∈ Icc (m + 1) (m + N), a j` has the same sum as the initial period `∑ j ∈ Icc 1 N, a j`,
because only indices `j ≥ 1` enter the comparison between adjacent blocks.

When the period sum `∑ j ∈ Icc 1 N, a j` vanishes, the partial-sum sequence
`m ↦ ∑ j ∈ Icc 1 m, a j` is genuinely `N`-periodic on all of `ℕ` (including at `m = 0`), agrees at
`m` with its value at `m % N`, and in a seminormed group is uniformly bounded in norm by
`∑ j ∈ Icc 1 N, ‖a j‖` whenever `N ≠ 0`.

## Main results

* `Finset.sum_Icc_shift_eq_of_periodic`: if `a (k + N) = a k` for all `1 ≤ k`, then
  `∑ j ∈ Icc (m + 1) (m + N), a j = ∑ j ∈ Icc 1 N, a j` for every `m : ℕ`.
* `Finset.sum_Icc_add_right_of_periodic`: extending `Icc 1 m` by `N` adds one period sum.
* `Finset.periodic_sum_Icc_of_sum_eq_zero`: if the period sum vanishes, `m ↦ ∑ j ∈ Icc 1 m, a j`
  is `N`-periodic on all of `ℕ`.
* `Finset.sum_Icc_mod_of_sum_eq_zero`: under zero period sum, `∑ j ∈ Icc 1 m, a j` equals
  `∑ j ∈ Icc 1 (m % N), a j`.
* `Finset.norm_sum_Icc_le_of_sum_eq_zero`: for `N ≠ 0`, `‖∑ j ∈ Icc 1 m, a j‖` is bounded by
  `∑ j ∈ Icc 1 N, ‖a j‖`.
-/

public section

namespace Finset

section AddCommMonoid

variable {M : Type*} [AddCommMonoid M] {a : ℕ → M} {N : ℕ}

/-- **Periodicity of block sums.** If `a (k + N) = a k` for every `k ≥ 1`, every block of `N`
consecutive positive indices has the same sum as `Icc 1 N`. -/
theorem sum_Icc_shift_eq_of_periodic (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (m : ℕ) :
    ∑ j ∈ Icc (m + 1) (m + N), a j = ∑ j ∈ Icc 1 N, a j := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · induction m with
    | zero => simp
    | succ m ih =>
      have h1 : Icc (m + 2) (m + 1 + N) = insert (m + 1 + N) (Icc (m + 2) (m + N)) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      have h2 : Icc (m + 1) (m + N) = insert (m + 1) (Icc (m + 2) (m + N)) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      rw [h1, sum_insert (by simp), hper (m + 1) (Nat.succ_pos m), ← ih, h2,
        sum_insert (by simp)]

/-- Extending `Icc 1 m` by one period `N` adds `∑ j ∈ Icc 1 N, a j`. -/
theorem sum_Icc_add_right_of_periodic (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (m : ℕ) :
    ∑ j ∈ Icc 1 (m + N), a j = ∑ j ∈ Icc 1 m, a j + ∑ j ∈ Icc 1 N, a j := by
  have hunion : Icc 1 (m + N) = Icc 1 m ∪ Icc (m + 1) (m + N) := by
    ext j; simp only [mem_Icc, mem_union]; omega
  have hdisj : Disjoint (Icc 1 m) (Icc (m + 1) (m + N)) := by
    rw [disjoint_left]
    intro j hj1 hj2
    simp only [mem_Icc] at hj1 hj2
    omega
  rw [hunion, sum_union hdisj, sum_Icc_shift_eq_of_periodic hper m]

/-- Summing `m` full periods `Icc 1 (m * N)` gives `m` times the period sum `∑ j ∈ Icc 1 N, a j`. -/
theorem sum_Icc_mul_eq_nsmul_of_periodic (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (m : ℕ) :
    ∑ j ∈ Icc 1 (m * N), a j = m • ∑ j ∈ Icc 1 N, a j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_Icc_add_right_of_periodic hper (m * N), ih, succ_nsmul]

/-- **Partial sums of a zero-mean periodic sequence are periodic on all of `ℕ`.** Even when
`a (k + N) = a k` holds only for `1 ≤ k`, vanishing of the period sum `∑ j ∈ Icc 1 N, a j` makes
`m ↦ ∑ j ∈ Icc 1 m, a j` periodic of period `N` for every `m ≥ 0`. -/
theorem periodic_sum_Icc_of_sum_eq_zero (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hsum : ∑ j ∈ Icc 1 N, a j = 0) :
    Function.Periodic (fun m ↦ ∑ j ∈ Icc 1 m, a j) N := fun m ↦ by
  simp only [sum_Icc_add_right_of_periodic hper m, hsum, add_zero]

/-- If `a` is `N`-periodic on `k ≥ 1` with vanishing period sum, the partial sum up to `m`
depends only on `m % N`. -/
theorem sum_Icc_mod_of_sum_eq_zero (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hsum : ∑ j ∈ Icc 1 N, a j = 0) (m : ℕ) :
    ∑ j ∈ Icc 1 m, a j = ∑ j ∈ Icc 1 (m % N), a j :=
  ((periodic_sum_Icc_of_sum_eq_zero hper hsum).map_mod_nat m).symm

end AddCommMonoid

section SeminormedAddCommGroup

variable {M : Type*} [SeminormedAddCommGroup M] {a : ℕ → M} {N : ℕ}

/-- **Uniform partial-sum bound for a zero-mean periodic sequence.** If `N ≠ 0`, `a (k + N) = a k`
for all `1 ≤ k`, and `∑ j ∈ Icc 1 N, a j = 0`, every partial sum `∑ j ∈ Icc 1 m, a j` has norm at
most `∑ j ∈ Icc 1 N, ‖a j‖`. -/
theorem norm_sum_Icc_le_of_sum_eq_zero (hN : N ≠ 0) (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hsum : ∑ j ∈ Icc 1 N, a j = 0) (m : ℕ) :
    ‖∑ j ∈ Icc 1 m, a j‖ ≤ ∑ j ∈ Icc 1 N, ‖a j‖ := by
  rw [sum_Icc_mod_of_sum_eq_zero hper hsum m]
  have hlt : m % N ≤ N := (Nat.mod_lt m (Nat.pos_of_ne_zero hN)).le
  exact (norm_sum_le _ _).trans
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hlt) fun _ _ _ ↦ norm_nonneg _)

end SeminormedAddCommGroup

end Finset
