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

Let every element lie in at most `f` sets. Then the sets `i` with `1 ≤ f * x i` form a cover
whose cost is at most `f` times the cost of the fractional cover `x` (Hochbaum). For prices as
in weak duality, the sets whose elements cost exactly their budget have total cost at most `f`
times the total price, and thus at most `f` times the cost of every fractional cover
(Bar-Yehuda and Even).

## Main statements

* `TauCeti.IsFractionalCover.sum_le_sum_mul`: weak duality.
* `TauCeti.IsFractionalCover.exists_one_le_mul_and_mem`: an element in at most `f` sets lies in
  a set `i` with `1 ≤ f * x i`.
* `TauCeti.IsFractionalCover.sum_cost_le_mul_of_card_le`: rounding by frequency.
* `TauCeti.sum_tight_cost_le_mul_sum`: the sets that a pricing pays exactly cost at most `f`
  times the total price.
* `TauCeti.IsFractionalCover.sum_tight_cost_le_mul`: the cost bound for the sets that a pricing
  pays exactly.

## References

* D. P. Williamson and D. B. Shmoys, *The Design of Approximation Algorithms*, §1.3 to §1.5,
  pp. 19 to 24 (rounding by frequency: Lemma 1.5 and Theorem 1.6; weak duality: §1.4, p. 21;
  the pricing bound: proof of Theorem 1.8, p. 22).
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

/-- Rounding by frequency, for one element. If `e` lies in at most `f` sets of the system, then
one of the sets that contain `e` has weight at least `1 / f` in a fractional cover, that is,
`1 ≤ f * x i`. -/
theorem IsFractionalCover.exists_one_le_mul_and_mem (hx : IsFractionalCover S x) {f : ℕ}
    {j : ι} {e : α} (he : e ∈ S j) (hf : #{i | e ∈ S i} ≤ f) :
    ∃ i, 1 ≤ f * x i ∧ e ∈ S i := by
  have hne : ({i | e ∈ S i} : Finset ι).Nonempty := ⟨j, by simpa using he⟩
  obtain ⟨i, hi, h⟩ := exists_le_of_sum_le (f := fun _ ↦ (1 : ℝ)) (g := fun i ↦ f * x i) hne
    (calc ∑ _ ∈ {i | e ∈ S i}, (1 : ℝ) = #{i | e ∈ S i} := by simp
      _ ≤ f * 1 := by rw [mul_one]; exact_mod_cast hf
      _ ≤ f * ∑ i with e ∈ S i, x i :=
        mul_le_mul_of_nonneg_left (hx.one_le_sum j e he) (Nat.cast_nonneg f)
      _ = ∑ i with e ∈ S i, f * x i := mul_sum ..)
  exact ⟨i, h, by simpa using hi⟩

/-- Rounding by frequency (Hochbaum). Let every element lie in at most `f` sets of the system
and let the costs be nonnegative. Then the sets `i` of a fractional cover `x` with
`1 ≤ f * x i` cover every element of the system, and their total cost is at most `f` times the
cost of `x`. -/
theorem IsFractionalCover.sum_cost_le_mul_of_card_le (hx : IsFractionalCover S x)
    (hc : ∀ i, 0 ≤ c i) {f : ℕ} (hf : ∀ e, #{i | e ∈ S i} ≤ f) :
    (∀ j, ∀ e ∈ S j, ∃ i, 1 ≤ f * x i ∧ e ∈ S i) ∧
      ∑ᶠ i ∈ {i | 1 ≤ f * x i}, c i ≤ f * ∑ i, c i * x i := by
  refine ⟨fun j e he ↦ hx.exists_one_le_mul_and_mem he (hf e), ?_⟩
  rw [← coe_filter_univ, finsum_mem_coe_finset, mul_sum]
  calc ∑ i with 1 ≤ f * x i, c i ≤ ∑ i with 1 ≤ f * x i, f * (c i * x i) :=
        sum_le_sum fun i hi ↦ by
          rw [mul_left_comm]
          exact le_mul_of_one_le_right (hc i) (mem_filter.mp hi).2
    _ ≤ ∑ i, f * (c i * x i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ ↦
          mul_nonneg (Nat.cast_nonneg f) (mul_nonneg (hc i) (hx.nonneg i))

/-- Pricing, the double counting step. Let every element lie in at most `f` sets of the system
and let `y` be nonnegative prices on the union. Then the sets whose elements cost exactly their
budget have total cost at most `f` times the total price. -/
theorem sum_tight_cost_le_mul_sum {f : ℕ} (hf : ∀ e, #{i | e ∈ S i} ≤ f) {y : α → ℝ}
    (hy₀ : ∀ e ∈ univ.biUnion S, 0 ≤ y e) :
    ∑ᶠ i ∈ {i | ∑ e ∈ S i, y e = c i}, c i ≤ f * ∑ e ∈ univ.biUnion S, y e := by
  rw [← coe_filter_univ, finsum_mem_coe_finset, mul_sum]
  calc ∑ i with ∑ e ∈ S i, y e = c i, c i = ∑ i with ∑ e ∈ S i, y e = c i, ∑ e ∈ S i, y e :=
        sum_congr rfl fun i hi ↦ (mem_filter.mp hi).2.symm
    _ = ∑ e ∈ univ.biUnion S, ∑ i with ∑ e ∈ S i, y e = c i ∧ e ∈ S i, y e := by
        refine sum_comm' fun i e ↦ ?_
        simp only [mem_filter, mem_univ, true_and, mem_biUnion]
        exact ⟨fun h ↦ ⟨⟨h.1, h.2⟩, i, h.2⟩, fun h ↦ h.1⟩
    _ ≤ ∑ e ∈ univ.biUnion S, f * y e := by
        refine sum_le_sum fun e he ↦ ?_
        rw [sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (hy₀ e he)
        refine Nat.cast_le.mpr ((card_le_card fun i hi ↦ ?_).trans (hf e))
        exact mem_filter.mpr ⟨mem_univ i, (mem_filter.mp hi).2.2⟩

/-- Pricing (Bar-Yehuda and Even). Let every element lie in at most `f` sets of the system, and
let `y` be nonnegative prices on the union under which the elements of each set cost at most its
budget. Then the sets whose elements cost exactly their budget have total cost at most `f` times
the cost of any fractional cover. -/
theorem IsFractionalCover.sum_tight_cost_le_mul (hx : IsFractionalCover S x) {f : ℕ}
    (hf : ∀ e, #{i | e ∈ S i} ≤ f) {y : α → ℝ} (hy₀ : ∀ e ∈ univ.biUnion S, 0 ≤ y e)
    (hy : ∀ i, ∑ e ∈ S i, y e ≤ c i) :
    ∑ᶠ i ∈ {i | ∑ e ∈ S i, y e = c i}, c i ≤ f * ∑ i, c i * x i :=
  (sum_tight_cost_le_mul_sum hf hy₀).trans
    (mul_le_mul_of_nonneg_left (hx.sum_le_sum_mul hy₀ hy) (Nat.cast_nonneg f))

end TauCeti
