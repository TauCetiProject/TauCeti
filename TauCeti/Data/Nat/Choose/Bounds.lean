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
import Mathlib.Tactic.Positivity

/-!
# Bounds on binomial-weighted power sums

The sum `∑_{j = k}^{d} choose j k · A ^ (j - k)` is the value at `A` of the `k`-th Hasse
derivative of `1 + X + ⋯ + X^d`, and so bounds evaluated Hasse derivatives of polynomials of degree
at most `d`. Bounding each binomial coefficient by `2 ^ d` and each power by `max 1 A ^ d` gives
the coarse bound `(d + 1) 2 ^ d max(1, A) ^ d`.

## Main results

* `Nat.sum_Icc_choose_mul_pow_le`: `∑_{j = k}^{d} choose j k · A ^ (j - k) ≤
  (d + 1) 2 ^ d max(1, A) ^ d` for `0 ≤ A` in a linearly ordered semiring.
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
