/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Ring.Pow
import TauCeti.Algebra.BigOperators.Finset.Powerset

/-!
# Multinomial upper bounds on elementary symmetric sums

In an ordered commutative semiring, `n!` times the `n`-th elementary symmetric sum of nonnegative
weights on a finite set `s` is bounded above by `(∑ x ∈ s, f x) ^ n`. Each `n`-element subset of
`s` appears `n!` times among the `n`-tuples of distinct elements of `s`, and those `n`-tuples form
a subset of all `n`-tuples from `s`.

## Main results

* `Finset.factorial_mul_sum_powersetCard_prod_le_sum_pow`:
  `(n! : R) * ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n` for nonnegative `f` on `s`.
-/

public section

namespace Finset

/-- For nonnegative weights on a finite set `s` in an ordered commutative semiring, `n!` times the
sum of products over `n`-element subsets of `s` is at most `(∑ x ∈ s, f x) ^ n`. -/
theorem factorial_mul_sum_powersetCard_prod_le_sum_pow {α R : Type*} [CommSemiring R]
    [PartialOrder R] [IsOrderedRing R] {s : Finset α} {f : α → R}
    (hf : ∀ x ∈ s, 0 ≤ f x) (n : ℕ) :
    (n.factorial : R) * ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp
    | succ m =>
      rw [powersetCard_eq_empty.mpr (by simp)]
      simp
  | insert a s ha ih =>
    cases n with
    | zero => simp
    | succ m =>
      have ha0 : 0 ≤ f a := hf a (mem_insert_self a s)
      have hs : ∀ x ∈ s, 0 ≤ f x := fun x hx ↦ hf x (mem_insert_of_mem hx)
      have hS0 : 0 ≤ ∑ x ∈ s, f x := sum_nonneg hs
      have hins : ∑ t ∈ s.powersetCard m, ∏ x ∈ insert a t, f x =
          f a * ∑ t ∈ s.powersetCard m, ∏ x ∈ t, f x := by
        rw [mul_sum]
        refine sum_congr rfl fun t ht ↦ ?_
        exact prod_insert fun h ↦ ha ((mem_powersetCard.mp ht).1 h)
      calc ((m + 1).factorial : R) * ∑ t ∈ (insert a s).powersetCard (m + 1), ∏ x ∈ t, f x
          = ((m + 1).factorial : R) * ∑ t ∈ s.powersetCard (m + 1), ∏ x ∈ t, f x +
              (m + 1 : ℕ) * f a * ((m.factorial : R) * ∑ t ∈ s.powersetCard m, ∏ x ∈ t, f x) := by
            rw [sum_powersetCard_succ_insert ha, hins, Nat.factorial_succ, Nat.cast_mul]
            ring
        _ ≤ (∑ x ∈ s, f x) ^ (m + 1) + (m + 1 : ℕ) * f a * (∑ x ∈ s, f x) ^ m := by
            gcongr
            · exact ih hs (m + 1)
            · exact mul_nonneg (Nat.cast_nonneg _) ha0
            · exact ih hs m
        _ ≤ (∑ x ∈ s, f x + f a) ^ (m + 1) := by
            have h := pow_add_mul_le_add_pow_of_sq_nonneg hS0 (pow_nonneg ha0 2)
              (pow_nonneg (add_nonneg hS0 ha0) 2)
              (add_nonneg (mul_nonneg zero_le_two hS0) ha0) (m + 1)
            simpa only [Nat.add_sub_cancel, mul_right_comm _ _ (f a)] using h
        _ = (∑ x ∈ insert a s, f x) ^ (m + 1) := by
            rw [sum_insert ha, add_comm]

end Finset
