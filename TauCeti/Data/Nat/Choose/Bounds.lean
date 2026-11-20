/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity

/-!
# Bounds on binomial-weighted power sums

The sum `∑_{j = k}^{d} choose j k · A ^ (j - k)` is the value at `A` of the `k`-th Hasse
derivative of `1 + X + ⋯ + X^d`, and so bounds evaluated Hasse derivatives of polynomials of degree
at most `d`. Bounding each binomial coefficient by `2 ^ d` and each power by `max 1 A ^ d` gives
the coarse bound `(d + 1) 2 ^ d max(1, A) ^ d`.

The sum `∑ₖ m (m - 1) ⋯ (m - k + 1) · A ^ (m - k)` collects the coefficients of the iterated
derivatives `(d/dX)ᵏ X^m = m (m - 1) ⋯ (m - k + 1) X^(m - k)` evaluated at `A`. Since
`m (m - 1) ⋯ (m - k + 1) ≤ choose m k · m ^ k`, the binomial theorem bounds it by `(m + A) ^ m`.

## Main results

* `Nat.sum_Icc_choose_mul_pow_le`: `∑_{j = k}^{d} choose j k · A ^ (j - k) ≤
  (d + 1) 2 ^ d max(1, A) ^ d` for `0 ≤ A` in a linearly ordered semiring.
* `Nat.sum_range_descFactorial_mul_pow_le`: `∑_{k < N} m.descFactorial k · A ^ (m - k) ≤
  (m + A) ^ m` for `0 ≤ A` in an ordered commutative semiring.
-/

public section

open Finset

/-- The binomial-weighted power sum `∑_{j = k}^{d} choose j k · A ^ (j - k)` is at most
`(d + 1) 2 ^ d max(1, A) ^ d` when `0 ≤ A`. -/
theorem Nat.sum_Icc_choose_mul_pow_le {α : Type*} [Semiring α] [LinearOrder α]
    [IsStrictOrderedRing α] (k d : ℕ) {A : α} (hA : 0 ≤ A) :
    ∑ j ∈ Icc k d, (j.choose k : α) * A ^ (j - k) ≤ (d + 1) * 2 ^ d * max 1 A ^ d := by
  have h1 : (1 : α) ≤ max 1 A := le_max_left 1 A
  calc
    ∑ j ∈ Icc k d, (j.choose k : α) * A ^ (j - k) ≤ ∑ _j ∈ Icc k d, 2 ^ d * max 1 A ^ d := by
      refine sum_le_sum fun j hj ↦ mul_le_mul ?_ ?_ (pow_nonneg hA _) (by positivity)
      · exact_mod_cast (j.choose_le_two_pow k).trans
          (Nat.pow_le_pow_right two_pos (mem_Icc.1 hj).2)
      · exact (pow_le_pow_left₀ hA (le_max_right 1 A) _).trans
          (pow_le_pow_right₀ h1 ((Nat.sub_le j k).trans (mem_Icc.1 hj).2))
    _ ≤ (d + 1) * 2 ^ d * max 1 A ^ d := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Icc, mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast Nat.sub_le (d + 1) k

/-- The descending-factorial-weighted power sum `∑_{k < N} m (m - 1) ⋯ (m - k + 1) · A ^ (m - k)`
is at most `(m + A) ^ m` when `0 ≤ A`, whatever the number `N` of terms: the terms with `k > m`
vanish, and `m (m - 1) ⋯ (m - k + 1) ≤ choose m k · m ^ k`. -/
theorem Nat.sum_range_descFactorial_mul_pow_le {α : Type*} [CommSemiring α] [PartialOrder α]
    [IsOrderedRing α] (m N : ℕ) {A : α} (hA : 0 ≤ A) :
    ∑ k ∈ range N, (m.descFactorial k : α) * A ^ (m - k) ≤ (m + A) ^ m := by
  have hle : ∑ k ∈ range N, (m.descFactorial k : α) * A ^ (m - k) ≤
      ∑ k ∈ range (m + 1), (m.descFactorial k : α) * A ^ (m - k) := by
    rcases le_total N (m + 1) with h | h
    · exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) fun _ _ _ ↦ by positivity
    · refine (sum_subset (range_subset_range.2 h) fun k _ hk ↦ ?_).ge
      rw [Nat.descFactorial_eq_zero_iff_lt.2 (by simpa using hk), Nat.cast_zero, zero_mul]
  refine hle.trans ((sum_le_sum fun k hk ↦ ?_).trans (add_pow (m : α) A m).ge)
  rw [mul_right_comm]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hA _)
  have h : m.descFactorial k ≤ m ^ k * m.choose k :=
    (m.descFactorial_le_pow k).trans
      (Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.lt_succ_iff.1 (mem_range.1 hk))))
  exact (Nat.mono_cast h).trans_eq (by push_cast; ring)
