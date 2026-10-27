/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite partial sums

This file contains basic facts about finite partial sums.

## Main definitions

* `TauCeti.prefixSum k x`: the sum of the first `k` coordinates of a tuple `x : Fin n → M`.

## Main results

* `TauCeti.prefixSum_succ`, `TauCeti.prefixSum_of_le`: the recurrence for prefix sums, and the
  prefix sum of full length is the total sum.
* `TauCeti.prefixSum_eq_sum_range`: prefix sums of a sequence restricted to `Fin n` are its
  partial sums over `range`, capped at `n`.
* `TauCeti.map_prefixSum`, `TauCeti.prefixSum_smul`: additive monoid homomorphisms and
  distributive scalar actions commute with prefix sums.
* `TauCeti.prefixSum_le_of_sum_le`: a tuple with smaller total sum and larger tail has smaller
  prefix sums.
* `TauCeti.eq_of_forall_prefixSum_eq`: a finite sequence is determined by its prefix sums.
* `TauCeti.eq_zero_of_forall_sum_Iic_eq_zero`: a finite sequence whose inclusive partial sums
  all vanish is zero.
-/

public section

namespace TauCeti

open Finset

section PrefixSum

variable {M : Type*} [AddCommMonoid M] {n : ℕ}

/-- The prefix sum `∑_{i < k} x i` of the first `k` coordinates of `x`. For `n ≤ k` it is the
sum of all coordinates. -/
def prefixSum (k : ℕ) (x : Fin n → M) : M :=
  ∑ i : Fin n with i.val < k, x i

/-- The defining formula of `prefixSum` as a filtered sum. -/
theorem prefixSum_def (k : ℕ) (x : Fin n → M) :
    prefixSum k x = ∑ i : Fin n with i.val < k, x i := by
  rw [prefixSum]

@[simp]
theorem prefixSum_zero (x : Fin n → M) : prefixSum 0 x = 0 := by
  simp [prefixSum]

/-- Each further coordinate adds its value to the prefix sum. -/
theorem prefixSum_succ {k : ℕ} (hk : k < n) (x : Fin n → M) :
    prefixSum (k + 1) x = prefixSum k x + x ⟨k, hk⟩ := by
  have hfilter : univ.filter (fun i : Fin n => (i : ℕ) < k + 1) =
      insert ⟨k, hk⟩ (univ.filter fun i : Fin n => (i : ℕ) < k) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [prefixSum, prefixSum, hfilter, sum_insert (by simp), add_comm]

/-- A prefix sum of length at least `n` is the total sum. -/
theorem prefixSum_of_le {k : ℕ} (hk : n ≤ k) (x : Fin n → M) : prefixSum k x = ∑ i, x i := by
  rw [prefixSum, filter_true_of_mem fun i _ ↦ i.isLt.trans_le hk]

/-- Capping the length of a prefix sum at `n` does not change it. -/
@[simp]
theorem prefixSum_min (k : ℕ) (x : Fin n → M) : prefixSum (min k n) x = prefixSum k x := by
  rcases le_total k n with hk | hk
  · rw [min_eq_left hk]
  · rw [min_eq_right hk, prefixSum_of_le le_rfl, prefixSum_of_le hk]

/-- The prefix sums of the first `n` terms of a sequence `f : ℕ → M` are its partial sums, capped
at `n`. -/
theorem prefixSum_eq_sum_range (k : ℕ) (f : ℕ → M) :
    prefixSum k (fun i : Fin n ↦ f i) = ∑ i ∈ range (min k n), f i := by
  rw [prefixSum, sum_filter, Fin.sum_univ_eq_sum_range (fun i ↦ if i < k then f i else 0),
    ← sum_filter]
  congr 1
  ext i
  simp [lt_min_iff, and_comm]

/-- Prefix sums are additive in the tuple. -/
@[simp]
theorem prefixSum_add (k : ℕ) (x y : Fin n → M) :
    prefixSum k (x + y) = prefixSum k x + prefixSum k y := by
  simp [prefixSum, sum_add_distrib]

/-- Additive monoid homomorphisms commute with prefix sums. -/
theorem map_prefixSum {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (k : ℕ) (x : Fin n → M) : f (prefixSum k x) = prefixSum k fun i ↦ f (x i) :=
  map_sum f x _

/-- Prefix sums commute with scalar multiplication of the tuple. -/
@[simp]
theorem prefixSum_smul {R : Type*} [DistribSMul R M] (k : ℕ) (c : R) (x : Fin n → M) :
    prefixSum k (c • x) = c • prefixSum k x :=
  (map_prefixSum (DistribSMul.toAddMonoidHom M c) k x).symm

/-- Prefix sums are monotone in the tuple for the coordinatewise order. -/
theorem prefixSum_mono [Preorder M] [IsOrderedAddMonoid M] (k : ℕ) {x y : Fin n → M}
    (h : x ≤ y) : prefixSum k x ≤ prefixSum k y :=
  sum_le_sum fun i _ ↦ h i

/-- If `y` has at least the total sum of `x` and lies below `x` from coordinate `k` on, then the
prefix sum of length `k` of `x` is at most that of `y`. -/
theorem prefixSum_le_of_sum_le [Preorder M] [IsOrderedCancelAddMonoid M] {k : ℕ}
    {x y : Fin n → M} (hsum : ∑ i, x i ≤ ∑ i, y i) (h : ∀ i : Fin n, k ≤ (i : ℕ) → y i ≤ x i) :
    prefixSum k x ≤ prefixSum k y := by
  have htail : ∑ i : Fin n with ¬i.val < k, y i ≤ ∑ i : Fin n with ¬i.val < k, x i :=
    sum_le_sum fun i hi ↦ h i (not_lt.1 (mem_filter.1 hi).2)
  rw [← sum_filter_add_sum_filter_not univ (fun i : Fin n ↦ (i : ℕ) < k) x,
    ← sum_filter_add_sum_filter_not univ (fun i : Fin n ↦ (i : ℕ) < k) y] at hsum
  rw [prefixSum_def, prefixSum_def]
  exact le_of_add_le_add_right (hsum.trans (add_le_add le_rfl htail))

/-- Prefix sums of length `k` only see the coordinates below `k`. -/
theorem prefixSum_congr {k : ℕ} {x y : Fin n → M} (h : ∀ i : Fin n, (i : ℕ) < k → x i = y i) :
    prefixSum k x = prefixSum k y :=
  sum_congr rfl fun i hi ↦ h i (mem_filter.1 hi).2

/-- Up to the length of the shorter tuple, prefix sums do not see the last coordinate. -/
theorem prefixSum_init {k : ℕ} (hk : k ≤ n) (x : Fin (n + 1) → M) :
    prefixSum k (Fin.init x) = prefixSum k x := by
  simp only [prefixSum, sum_filter, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last,
    not_lt.2 hk, ite_false, add_zero, Fin.init_def]

/-- Padding with zeros does not change prefix sums. -/
@[simp]
theorem prefixSum_append_zero {m : ℕ} (k : ℕ) (x : Fin n → M) :
    prefixSum k (Fin.append x (0 : Fin m → M)) = prefixSum k x := by
  simp [prefixSum, sum_filter, Fin.sum_univ_add]

/-- **A finite sequence is determined by its prefix sums**: consecutive prefix sums differ by a
single coordinate, so cancelling the shorter one off the longer recovers that coordinate. -/
theorem eq_of_forall_prefixSum_eq [IsLeftCancelAdd M] {y z : Fin n → M}
    (h : ∀ m : ℕ, prefixSum m y = prefixSum m z) : y = z := by
  funext i
  have hi := h ((i : ℕ) + 1)
  rw [prefixSum_succ i.isLt, prefixSum_succ i.isLt, h (i : ℕ)] at hi
  exact add_left_cancel hi

end PrefixSum

/-- **A finite sequence all of whose inclusive partial sums vanish is zero.** -/
theorem eq_zero_of_forall_sum_Iic_eq_zero {M : Type*} [AddCommMonoid M] (n : ℕ)
    {y : Fin (n + 1) → M} (hy : ∀ k, ∑ j ∈ Iic k, y j = 0) : y = 0 := by
  funext k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    have h := hy k
    rw [Iic_eq_cons_Iio, sum_cons, sum_eq_zero fun j hj ↦ ih j (mem_Iio.mp hj), add_zero] at h
    exact h

end TauCeti
