/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Comparison of binomial coefficient ratios

The ratio choose k m / choose n m is the probability that m draws without
replacement all land in a fixed k-subset of an n-element set. This is bounded by
(k / n)^m, the corresponding probability for draws with replacement.
-/

public section

namespace Nat

/-- Cross-multiplied comparison of the binomial coefficient ratio with the power ratio.
The inequality also holds when one of the binomial coefficients vanishes. -/
theorem choose_mul_pow_le_choose_mul_pow {k n : ℕ} (hkn : k ≤ n) (m : ℕ) :
    k.choose m * n ^ m ≤ n.choose m * k ^ m := by
  apply Nat.le_of_mul_le_mul_right (c := m !) _ (factorial_pos _)
  have hprod (a b : ℕ) :
      a.choose m * b ^ m * m ! = ∏ i ∈ Finset.range m, (a - i) * b := by
    have hfactor : a.choose m * b ^ m * m ! = (m ! * a.choose m) * b ^ m := by ac_rfl
    rw [hfactor, ← descFactorial_eq_factorial_mul_choose, descFactorial_eq_prod_range,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [hprod, hprod]
  exact Finset.prod_le_prod fun i _ ↦ by
    rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm n k]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hkn) _

/-- A multiplicative upper bound on the ratio of binomial coefficients also bounds the
ratio of the corresponding powers. -/
theorem pow_le_mul_pow_of_choose_le_mul_choose {k n m N : ℕ} (hm : m ≤ k) (hkn : k ≤ n)
    (h : n.choose m ≤ N * k.choose m) : n ^ m ≤ N * k ^ m := by
  apply Nat.le_of_mul_le_mul_left (c := k.choose m) _ (choose_pos hm)
  calc
    k.choose m * n ^ m ≤ n.choose m * k ^ m := choose_mul_pow_le_choose_mul_pow hkn m
    _ ≤ (N * k.choose m) * k ^ m := Nat.mul_le_mul_right _ h
    _ = k.choose m * (N * k ^ m) := by ac_rfl

end Nat
