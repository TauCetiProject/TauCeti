/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
import TauCeti.Algebra.BigOperators.Finset.Powerset

/-!
# Multinomial upper bounds on elementary symmetric sums

In an ordered commutative semiring, `n!` times the `n`-th elementary symmetric sum of nonnegative
weights on a finite set `s` is bounded above by `(∑ x ∈ s, f x) ^ n`. Each `n`-element subset of
`s` appears `n!` times among the `n`-tuples of distinct elements of `s`, and those `n`-tuples form
a subset of all `n`-tuples from `s`.

## Main results

* `Finset.factorial_nsmul_sum_powersetCard_prod_le_sum_pow`:
  `n! • ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n` for nonnegative `f` on `s`.
* `Finset.factorial_mul_sum_powersetCard_prod_le_sum_pow`: the cast-multiplication form
  `(n! : R) * ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n`.
-/

public section

namespace Finset

/-- For nonnegative `a` and `b` in an ordered commutative semiring,
`a ^ (n + 1) + (n + 1) * b * a ^ n ≤ (a + b) ^ (n + 1)`. -/
private theorem pow_succ_add_mul_pow_le_add_pow {R : Type*} [CommSemiring R]
    [PartialOrder R] [IsOrderedRing R] {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    a ^ (n + 1) + (n + 1 : ℕ) * b * a ^ n ≤ (a + b) ^ (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    have h0 : 0 ≤ ((k + 1 : ℕ) : R) * b ^ 2 * a ^ k :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hb 2)) (pow_nonneg ha k)
    calc a ^ (k + 2) + (k + 2 : ℕ) * b * a ^ (k + 1)
        = a ^ (k + 2) + (k + 2 : ℕ) * b * a ^ (k + 1) + 0 := (add_zero _).symm
      _ ≤ a ^ (k + 2) + (k + 2 : ℕ) * b * a ^ (k + 1) +
            ((k + 1 : ℕ) : R) * b ^ 2 * a ^ k := add_le_add_right h0 _
      _ = (a ^ (k + 1) + (k + 1 : ℕ) * b * a ^ k) * (a + b) := by
          push_cast
          ring
      _ ≤ (a + b) ^ (k + 1) * (a + b) :=
          mul_le_mul_of_nonneg_right ih (add_nonneg ha hb)
      _ = (a + b) ^ (k + 2) := (pow_succ _ _).symm

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
        _ ≤ (∑ x ∈ s, f x + f a) ^ (m + 1) :=
            pow_succ_add_mul_pow_le_add_pow hS0 ha0 m
        _ = (∑ x ∈ insert a s, f x) ^ (m + 1) := by
            rw [sum_insert ha, add_comm]

/-- Scalar-multiplication form of `Finset.factorial_mul_sum_powersetCard_prod_le_sum_pow`. -/
theorem factorial_nsmul_sum_powersetCard_prod_le_sum_pow {α R : Type*} [CommSemiring R]
    [PartialOrder R] [IsOrderedRing R] {s : Finset α} {f : α → R}
    (hf : ∀ x ∈ s, 0 ≤ f x) (n : ℕ) :
    n.factorial • ∑ t ∈ s.powersetCard n, ∏ x ∈ t, f x ≤ (∑ x ∈ s, f x) ^ n := by
  rw [nsmul_eq_mul]
  exact factorial_mul_sum_powersetCard_prod_le_sum_pow hf n

end Finset
