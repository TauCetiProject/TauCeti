/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Defs
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite alternating sums of antitone sequences

For a nonnegative antitone sequence `a : ℕ → R` in an ordered ring, every partial alternating sum
`∑ k ∈ range n, (-1) ^ k * a k` lies between `0` and the first term `a 0`
(`Antitone.sum_range_neg_one_pow_mul_mem_Icc`). Mathlib's alternating-series lemmas, such as
`Antitone.alternating_series_le_tendsto`, bound the limit of these partial sums instead.
-/

public section

open Finset

namespace Antitone

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] {a : ℕ → R}

/-- A finite alternating sum of a nonnegative antitone sequence lies between `0` and its first
term. -/
theorem sum_range_neg_one_pow_mul_mem_Icc (ha : Antitone a) (ha0 : ∀ k, 0 ≤ a k) (n : ℕ) :
    ∑ k ∈ range n, (-1) ^ k * a k ∈ Set.Icc 0 (a 0) := by
  induction n generalizing a with
  | zero => simpa using ha0 0
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (a := fun k ↦ a (k + 1)) (fun i j hij ↦ ha (by omega)) fun k ↦ ha0 _
    rw [sum_range_succ']
    simp only [pow_succ, mul_neg_one, neg_mul, sum_neg_distrib, pow_zero, one_mul,
      neg_add_eq_sub]
    exact ⟨sub_nonneg.2 (h2.trans (ha (Nat.zero_le 1))), sub_le_self _ h1⟩

/-- A finite alternating sum of a nonnegative antitone sequence is nonnegative. -/
theorem sum_range_neg_one_pow_mul_nonneg (ha : Antitone a) (ha0 : ∀ k, 0 ≤ a k) (n : ℕ) :
    0 ≤ ∑ k ∈ range n, (-1) ^ k * a k :=
  (ha.sum_range_neg_one_pow_mul_mem_Icc ha0 n).1

/-- A finite alternating sum of a nonnegative antitone sequence is at most its first term. -/
theorem sum_range_neg_one_pow_mul_le (ha : Antitone a) (ha0 : ∀ k, 0 ≤ a k) (n : ℕ) :
    ∑ k ∈ range n, (-1) ^ k * a k ≤ a 0 :=
  (ha.sum_range_neg_one_pow_mul_mem_Icc ha0 n).2

end Antitone
