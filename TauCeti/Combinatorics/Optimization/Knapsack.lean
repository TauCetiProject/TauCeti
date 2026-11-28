/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The prefix bound for knapsacks

Items carry nonnegative values `v i` and weights `w i`. When the items are listed in order of
nonincreasing value per unit of weight, written without division as `v j * w i ≤ v i * w j` for
all `i < j`, a set of items that weighs strictly less than the first `k` items is worth at most
as much as they are. For a knapsack of capacity `W`, this bounds the value of every set of
weight at most `W` by the value of the first `k` items plus the value of item `k`, for each `k`
such that the items up to and including item `k` weigh more than `W`.

## Main statements

* `TauCeti.sum_value_le_of_sum_weight_lt`: an exchange bound for two finite sets `A` and `P`.
  If each item of `A \ P` has at most the value per unit of weight of each item of `P \ A`, and
  `A` weighs strictly less than `P`, then `A` is worth at most as much as `P`.
* `TauCeti.sum_value_le_sum_prefix`: prefix dominance for items sorted by value per unit of
  weight.
* `TauCeti.sum_value_le_sum_prefix_add`: the knapsack bound by the first `k` items and item `k`.
* `TauCeti.sum_value_le_two_mul_max`: the same bound by twice the larger of the two parts, so the
  better of the first `k` items and item `k` alone is worth at least half of every set of weight
  at most `W` when both weigh at most `W`.

## References

* D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, Cambridge
  University Press, 2011, Exercise 3.1.
-/

public section

open Finset

namespace TauCeti

variable {ι R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- An exchange bound: if each item of `A \ P` has at most the value per unit of weight of each
item of `P \ A` (written without division), the items of `P \ A` have nonnegative values, the
items of `A \ P` have nonnegative weights, and `A` weighs strictly less than `P`, then `A` is
worth at most as much as `P`. -/
theorem sum_value_le_of_sum_weight_lt [DecidableEq ι] {v w : ι → R} {A P : Finset ι}
    (hv : ∀ i ∈ P \ A, 0 ≤ v i) (hw : ∀ j ∈ A \ P, 0 ≤ w j)
    (hvw : ∀ i ∈ P \ A, ∀ j ∈ A \ P, v j * w i ≤ v i * w j)
    (hA : ∑ i ∈ A, w i < ∑ i ∈ P, w i) :
    ∑ i ∈ A, v i ≤ ∑ i ∈ P, v i := by
  rw [← sum_inter_add_sum_sdiff A P, ← sum_inter_add_sum_sdiff P A, inter_comm P A] at hA ⊢
  have hXY : ∑ j ∈ A \ P, w j < ∑ i ∈ P \ A, w i := lt_of_add_lt_add_left hA
  have hY : 0 ≤ ∑ i ∈ P \ A, v i := sum_nonneg hv
  have key : (∑ j ∈ A \ P, v j) * ∑ i ∈ P \ A, w i ≤ (∑ i ∈ P \ A, v i) * ∑ j ∈ A \ P, w j := by
    rw [sum_mul_sum, sum_mul_sum, sum_comm]
    exact sum_le_sum fun i hi => sum_le_sum fun j hj => hvw i hi j hj
  have hpos : 0 < ∑ i ∈ P \ A, w i := (sum_nonneg hw).trans_lt hXY
  exact add_le_add le_rfl (le_of_mul_le_mul_right
    (key.trans (mul_le_mul_of_nonneg_left hXY.le hY)) hpos)

/-- Prefix dominance: for nonnegative values and weights listed in order of nonincreasing value
per unit of weight, written without division, a set of items that weighs strictly less than the
first `k` items is worth at most as much as they are. -/
theorem sum_value_le_sum_prefix {n : ℕ} {v w : Fin n → R} (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) (hsort : ∀ i j, i < j → v j * w i ≤ v i * w j) (k : ℕ)
    {A : Finset (Fin n)} (hA : ∑ i ∈ A, w i < ∑ i with i.val < k, w i) :
    ∑ i ∈ A, v i ≤ ∑ i with i.val < k, v i := by
  refine sum_value_le_of_sum_weight_lt (fun i _ => hv i) (fun j _ => hw j)
    (fun i hi j hj => hsort i j ?_) hA
  simp only [mem_sdiff, mem_filter, mem_univ, true_and, not_lt] at hi hj
  exact Fin.lt_def.2 (hi.1.trans_le hj.2)

/-- The knapsack bound: for nonnegative values and weights listed in order of nonincreasing
value per unit of weight, if the items up to and including item `k` weigh more than the capacity
`W`, then every set of items of weight at most `W` is worth at most the first `k` items together
with item `k`. -/
theorem sum_value_le_sum_prefix_add {n : ℕ} {v w : Fin n → R} (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) (hsort : ∀ i j, i < j → v j * w i ≤ v i * w j) {W : R} (k : Fin n)
    (hW : W < ∑ i with i ≤ k, w i) {A : Finset (Fin n)} (hA : ∑ i ∈ A, w i ≤ W) :
    ∑ i ∈ A, v i ≤ ∑ i with i < k, v i + v k := by
  have hk : univ.filter (· ≤ k) = insert k (univ.filter (· < k)) := by
    ext i
    simp [le_iff_lt_or_eq, or_comm]
  have := sum_value_le_of_sum_weight_lt (P := univ.filter (· ≤ k)) (fun i _ => hv i)
    (fun j _ => hw j) (fun i hi j hj => hsort i j ?_) (hA.trans_lt hW)
  · rwa [hk, sum_insert (by simp), add_comm] at this
  · simp only [mem_sdiff, mem_filter, mem_univ, true_and, not_le] at hi hj
    exact hi.1.trans_lt hj.2

/-- The half bound for knapsacks: under the hypotheses of `sum_value_le_sum_prefix_add`, every
set of items of weight at most `W` is worth at most twice the larger of the value of the first
`k` items and the value of item `k`. When the first `k` items and item `k` each weigh at most
`W`, the more valuable of these two sets is thus a set of weight at most `W` worth at least half
of every such set. -/
theorem sum_value_le_two_mul_max {n : ℕ} {v w : Fin n → R} (hv : ∀ i, 0 ≤ v i)
    (hw : ∀ i, 0 ≤ w i) (hsort : ∀ i j, i < j → v j * w i ≤ v i * w j) {W : R} (k : Fin n)
    (hW : W < ∑ i with i ≤ k, w i) {A : Finset (Fin n)} (hA : ∑ i ∈ A, w i ≤ W) :
    ∑ i ∈ A, v i ≤ 2 * max (∑ i with i < k, v i) (v k) :=
  (sum_value_le_sum_prefix_add hv hw hsort k hW hA).trans <| by
    rw [two_mul]
    exact add_le_add (le_max_left _ _) (le_max_right _ _)

end TauCeti
