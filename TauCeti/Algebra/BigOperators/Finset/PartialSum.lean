/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.Abel

/-!
# Finite partial sums

This file contains basic facts about finite partial sums.

## Main definitions

* `TauCeti.prefixSum k x`: the sum of the first `k` coordinates of a tuple `x : Fin n → M`.

## Main results

* `TauCeti.prefixSum_succ`, `TauCeti.prefixSum_of_le`: the recurrence for prefix sums, and the
  prefix sum of full length is the total sum.
* `TauCeti.sum_sub_prefixSum`: successive differences of a function of the prefix sums
  telescope.
* `TauCeti.eq_of_forall_prefixSum_eq`, `TauCeti.monotone_prefixSum`: a tuple is determined by its
  prefix sums, which are monotone in the length for nonnegative tuples.
* `TauCeti.prefixSum_eq_sum_castLE`, `TauCeti.prefixSum_comp_rev`: up to `n`, prefix sums are sums
  over the first indices, and prefix sums of a reversed tuple are suffix sums.
* `TauCeti.prefixSum_eq_sum_range`: prefix sums of a sequence restricted to `Fin n` are its
  partial sums over `range`, capped at `n`.
* `TauCeti.prefixSum_sum`, `TauCeti.prefixSum_sub`, `TauCeti.prefixSum_single`: prefix sums of
  finite sums and differences of tuples, and of a tuple supported at one coordinate.
* `TauCeti.prefixSum_sum_single_castSucc_sub_single_succ`: prefix sums of a combination
  `∑ᵢ cᵢ (eᵢ - eᵢ₊₁)` of consecutive coordinate differences.
* `TauCeti.map_prefixSum`, `TauCeti.prefixSum_smul`: additive monoid homomorphisms and
  distributive scalar actions commute with prefix sums.
* `TauCeti.sum_smul_by_parts_prefixSum`, `TauCeti.sum_smul_by_parts_prefixSum_extend`: summation
  by parts, writing `∑ᵢ yᵢ • xᵢ` through the prefix sums of `x`.
* `TauCeti.prefixSum_le_of_sum_le`: a tuple with smaller total sum and larger tail has smaller
  prefix sums.
* `TauCeti.eq_zero_of_forall_sum_Iic_eq_zero`: a function on a locally finite order whose sums
  over all lower intervals `Iic k` vanish is zero.
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

@[simp]
theorem prefixSum_zero_right (k : ℕ) : prefixSum k (0 : Fin n → M) = 0 := by
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

/-- The prefix sum of length one is the first coordinate. -/
@[simp]
theorem prefixSum_one (x : Fin (n + 1) → M) : prefixSum 1 x = x 0 := by
  rw [prefixSum_succ n.succ_pos, prefixSum_zero, zero_add, Fin.mk_zero]

/-- A prefix sum of length at least `n` is the total sum. -/
theorem prefixSum_of_le {k : ℕ} (hk : n ≤ k) (x : Fin n → M) : prefixSum k x = ∑ i, x i := by
  rw [prefixSum, filter_true_of_mem fun i _ ↦ i.isLt.trans_le hk]

/-- Successive differences of a function of the prefix sums telescope. -/
theorem sum_sub_prefixSum {G : Type*} [AddCommGroup G] (F : M → G) (k : ℕ) (x : Fin n → M) :
    ∑ i : Fin n with i.val < k, (F (prefixSum (i.val + 1) x) - F (prefixSum i.val x)) =
      F (prefixSum k x) - F 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk : k < n
    · have h := prefixSum_succ hk fun i : Fin n ↦
        F (prefixSum (i.val + 1) x) - F (prefixSum i.val x)
      rw [prefixSum_def, prefixSum_def] at h
      rw [h, ih, prefixSum_succ hk x]
      exact sub_add_sub_cancel' _ _ _
    · rw [filter_congr (q := fun i : Fin n ↦ i.val < k) (fun i _ ↦ by omega), ih,
        prefixSum_of_le (by omega), prefixSum_of_le (by omega)]

/-- A tuple is determined by its prefix sums. -/
theorem eq_of_forall_prefixSum_eq [IsLeftCancelAdd M] {x y : Fin n → M}
    (h : ∀ k, prefixSum k x = prefixSum k y) : x = y := by
  funext i
  have := h (i.val + 1)
  rwa [prefixSum_succ i.isLt, prefixSum_succ i.isLt, h, add_right_inj] at this

/-- For `k ≤ n`, the prefix sum of length `k` is the sum over the first `k` indices of `Fin n`. -/
theorem prefixSum_eq_sum_castLE {k : ℕ} (hk : k ≤ n) (x : Fin n → M) :
    prefixSum k x = ∑ j : Fin k, x (Fin.castLE hk j) := by
  have hmap := sum_map univ (Fin.castLEEmb hk) x
  simp only [Fin.castLEEmb_apply] at hmap
  rw [prefixSum_def, ← hmap]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb_apply]
  exact ⟨fun hi ↦ ⟨⟨i, hi⟩, rfl⟩, fun ⟨j, hj⟩ ↦ hj ▸ j.isLt⟩

/-- For `k ≤ n`, the prefix sum of length `k` of `i ↦ x i.rev` is the suffix sum over indices
`n - k ≤ j`. -/
theorem prefixSum_comp_rev {k : ℕ} (hk : k ≤ n) (x : Fin n → M) :
    prefixSum k (fun i ↦ x i.rev) = ∑ j : Fin n with n - k ≤ j.val, x j := by
  rw [prefixSum_def, sum_filter, sum_filter]
  refine (sum_congr rfl fun i _ ↦ ?_).trans
    (Equiv.sum_comp Fin.revPerm fun j : Fin n ↦ if n - k ≤ j.val then x j else 0)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  by_cases hi : i.val < k
  · rw [ite_eq_left hi, ite_eq_left (by omega)]
  · rw [ite_eq_right hi, ite_eq_right (by have := i.isLt; omega)]

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

/-- Prefix sums of a finite sum of tuples are the sums of their prefix sums. -/
@[simp]
theorem prefixSum_sum {ι : Type*} (s : Finset ι) (k : ℕ) (x : ι → Fin n → M) :
    prefixSum k (∑ j ∈ s, x j) = ∑ j ∈ s, prefixSum k (x j) := by
  simp only [prefixSum, Finset.sum_apply]
  exact sum_comm

/-- The prefix sum of length `k` of the tuple supported at `a` with value `m` is `m` when `a` is
among the first `k` coordinates, and `0` otherwise. -/
@[simp]
theorem prefixSum_single [DecidableEq (Fin n)] (k : ℕ) (a : Fin n) (m : M) :
    prefixSum k (Pi.single a m) = if (a : ℕ) < k then m else 0 := by
  simp [prefixSum]

/-- Prefix sums are subtractive in the tuple. -/
@[simp]
theorem prefixSum_sub {G : Type*} [SubtractionCommMonoid G] (k : ℕ) (x y : Fin n → G) :
    prefixSum k (x - y) = prefixSum k x - prefixSum k y := by
  simp [prefixSum, sum_sub_distrib]

/-- The prefix sums of the combination `∑ᵢ cᵢ (eᵢ - eᵢ₊₁)` of consecutive coordinate differences:
the prefix sum of length `k` is `c (k - 1)` when `1 ≤ k ≤ n`, and `0` otherwise. -/
theorem prefixSum_sum_single_castSucc_sub_single_succ {G : Type*} [AddCommGroup G]
    (c : Fin n → G) (k : ℕ) :
    prefixSum k (∑ i, (Pi.single i.castSucc (c i) - Pi.single i.succ (c i))) =
      ∑ i : Fin n with i.val + 1 = k, c i := by
  rw [prefixSum_sum, sum_filter]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [prefixSum_sub, prefixSum_single, prefixSum_single, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | omega | simp

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

/-- The prefix sums of a nonnegative tuple are monotone in the length. -/
theorem monotone_prefixSum [Preorder M] [IsOrderedAddMonoid M] {x : Fin n → M} (hx : 0 ≤ x) :
    Monotone fun k ↦ prefixSum k x :=
  fun _ _ h ↦ sum_le_sum_of_subset_of_nonneg
    (fun i hi ↦ by simp only [mem_filter, mem_univ, true_and] at hi ⊢; omega)
    (fun i _ _ ↦ hx i)

/-- The prefix sums of an antitone tuple are concave in the length: the increment from `k + 1`
to `k + 2` is at most the increment from `k` to `k + 1`. -/
theorem prefixSum_add_prefixSum_add_two_le [Preorder M] [IsOrderedAddMonoid M] {x : Fin n → M}
    (hx : Antitone x) {k : ℕ} (hk : k + 2 ≤ n) :
    prefixSum k x + prefixSum (k + 2) x ≤ prefixSum (k + 1) x + prefixSum (k + 1) x := by
  have h₁ := prefixSum_succ (k := k) (by omega) x
  have h₂ : prefixSum (k + 2) x = prefixSum (k + 1) x + x ⟨k + 1, by omega⟩ :=
    prefixSum_succ (by omega) x
  calc prefixSum k x + prefixSum (k + 2) x
      = prefixSum (k + 1) x + (prefixSum k x + x ⟨k + 1, by omega⟩) := by
        rw [h₂, add_left_comm]
    _ ≤ prefixSum (k + 1) x + (prefixSum k x + x ⟨k, by omega⟩) := by
        gcongr; exact hx (Fin.mk_le_mk.mpr (by omega))
    _ = prefixSum (k + 1) x + prefixSum (k + 1) x := by rw [← h₁]

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

/-- **Summation by parts** for prefix sums: for coefficients `y : ℕ → R`,
`∑ᵢ yᵢ xᵢ = ∑ₖ (yₖ - yₖ₊₁) (x₀ + ⋯ + xₖ) + yₙ (x₀ + ⋯ + xₙ₋₁)`. -/
theorem sum_smul_by_parts_prefixSum {R : Type*} [Ring R] {G : Type*} [AddCommGroup G] [Module R G]
    (y : ℕ → R) (x : Fin n → G) :
    ∑ i : Fin n, y i • x i =
      ∑ k : Fin n, (y k - y (k + 1)) • prefixSum (k + 1) x + y n • ∑ i, x i := by
  -- Induct on the length `k ≤ n` of the prefix being summed.
  suffices h : ∀ k ≤ n, prefixSum k (fun i ↦ y i • x i) =
      prefixSum k (fun j : Fin n ↦ (y j - y (j + 1)) • prefixSum (j + 1) x) + y k • prefixSum k x by
    simpa only [prefixSum_of_le le_rfl] using h n le_rfl
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < n := hk
    rw [prefixSum_succ hk', prefixSum_succ hk', ih hk'.le, prefixSum_succ hk' x]
    simp only [sub_smul, smul_add]
    abel

/-- **Summation by parts** for prefix sums with weights `y : Fin n → R`: extending `y` by zero
to `ℕ`, `∑ᵢ yᵢ xᵢ = ∑ₖ (yₖ - yₖ₊₁) (x₀ + ⋯ + xₖ)`. -/
theorem sum_smul_by_parts_prefixSum_extend {R : Type*} [Ring R] {G : Type*} [AddCommGroup G]
    [Module R G] (y : Fin n → R) (x : Fin n → G) :
    ∑ i, y i • x i = ∑ k : Fin n,
      (Function.extend Fin.val y 0 k - Function.extend Fin.val y 0 (k + 1)) •
        prefixSum (k + 1) x := by
  have hY (j : Fin n) : Function.extend Fin.val y 0 j = y j :=
    Fin.val_injective.extend_apply y 0 j
  have hYN : Function.extend Fin.val y (0 : ℕ → R) n = 0 :=
    Function.extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ j.isLt.ne hj
  simpa [hY, hYN] using sum_smul_by_parts_prefixSum (Function.extend Fin.val y 0) x

end PrefixSum

/-- **A function all of whose sums over the lower intervals `Iic k` vanish is zero.** The index
type is any partial order whose lower intervals are finite, such as `Fin n` or `ℕ`. -/
theorem eq_zero_of_forall_sum_Iic_eq_zero {ι M : Type*} [PartialOrder ι] [LocallyFiniteOrderBot ι]
    [AddCommMonoid M] {y : ι → M} (hy : ∀ k, ∑ j ∈ Iic k, y j = 0) : y = 0 := by
  funext k
  induction k using WellFoundedLT.induction with
  | _ k ih =>
    have h := hy k
    rw [Iic_eq_cons_Iio, sum_cons, sum_eq_zero fun j hj ↦ ih j (mem_Iio.mp hj), add_zero] at h
    exact h

end TauCeti
