/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.GroupWithZero.Indicator

/-!
# Fractional covers of finite set systems

A fractional cover assigns a nonnegative weight to each member of an indexed family of finite
sets. Every element in the union must receive total weight at least one. An ordinary cover
gives a fractional cover of the same cost by taking its indicator.

Weak duality bounds the total price of the elements by the cost of any fractional cover,
provided the prices are nonnegative and the elements of each set cost at most its budget.
This is the price bound used in the analysis of greedy set cover.

## References

* D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, §1.4,
  p. 21 (weak duality for set cover).
-/

public section

namespace TauCeti

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- Nonnegative weights on the sets of `S` form a fractional cover if the weights of the sets
containing each element of the system sum to at least one. -/
@[mk_iff]
structure IsFractionalCover (S : ι → Finset α) (x : ι → ℝ) : Prop where
  /-- Each set has nonnegative weight, including an empty set. -/
  nonneg (i : ι) : 0 ≤ x i
  /-- Every element in a member of the family receives total weight at least one. -/
  one_le_sum (j : ι) (e : α) (he : e ∈ S j) : 1 ≤ ∑ i with e ∈ S i, x i

variable {S : ι → Finset α} {x c : ι → ℝ}

/-- When all sets are empty, the fractional covers are exactly the nonnegative weights. -/
@[simp] theorem isFractionalCover_empty_iff :
    IsFractionalCover (fun _ : ι ↦ (∅ : Finset α)) x ↔ ∀ i, 0 ≤ x i := by
  simp [isFractionalCover_iff]

/-- The indicator of a set of indices is a fractional cover exactly when the selected sets
cover every element of the system. -/
@[simp] theorem isFractionalCover_indicator_one_iff {J : Set ι} :
    IsFractionalCover S (J.indicator 1) ↔ ∀ j, ∀ e ∈ S j, ∃ i ∈ J, e ∈ S i := by
  classical
  have hnonneg (i : ι) : 0 ≤ J.indicator (1 : ι → ℝ) i :=
    Set.indicator_nonneg (fun _ _ ↦ zero_le_one) i
  rw [isFractionalCover_iff, and_iff_right hnonneg]
  simp [Set.indicator_apply, Nat.one_le_cast, Finset.Nonempty, and_comm]

/-- Every cover has a fractional cover of the same cost. Thus a bound valid for every
fractional cover applies to every ordinary cover, even for signed set costs. -/
theorem exists_isFractionalCover_sum_mul_eq {J : Set ι}
    (hJ : ∀ j, ∀ e ∈ S j, ∃ i ∈ J, e ∈ S i) (c : ι → ℝ) :
    ∃ x, IsFractionalCover S x ∧ ∑ i, c i * x i = ∑ᶠ i ∈ J, c i := by
  refine ⟨J.indicator 1, isFractionalCover_indicator_one_iff.mpr hJ, ?_⟩
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  simp only [← Set.indicator_mul_right, Pi.one_apply, mul_one]

/-- Weak duality for set cover. If the prices on the union are nonnegative and each set's
total price is within its budget, their sum is at most the cost of any fractional cover. -/
theorem IsFractionalCover.sum_le_sum_mul (hx : IsFractionalCover S x) {y : α → ℝ}
    (hy : ∀ e ∈ univ.biUnion S, 0 ≤ y e) (hc : ∀ i, ∑ e ∈ S i, y e ≤ c i) :
    ∑ e ∈ univ.biUnion S, y e ≤ ∑ i, c i * x i := by
  calc
    _ ≤ ∑ e ∈ univ.biUnion S, y e * (∑ i with e ∈ S i, x i) := by
      refine sum_le_sum fun e he ↦ ?_
      obtain ⟨j, _, hj⟩ := mem_biUnion.mp he
      exact le_mul_of_one_le_right (hy e he) (hx.one_le_sum j e hj)
    _ = ∑ i, (∑ e ∈ S i, y e) * x i := by
      simp_rw [mul_sum, sum_mul]
      apply sum_comm'
      intro e i
      simp only [mem_filter, mem_univ, true_and, and_true]
      exact and_iff_right_of_imp fun he ↦ subset_biUnion_of_mem S (mem_univ i) he
    _ ≤ _ := sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hc i) (hx.nonneg i)

end TauCeti
