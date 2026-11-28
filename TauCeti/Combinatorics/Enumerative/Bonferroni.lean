/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Sum

/-!
# Bonferroni's inequalities for the subsets of a finite set

For a finite set `B`, the alternating sum `∑_{G ⊆ B} (-1) ^ |G|` is the indicator of `B = ∅`.
Truncating it to the subsets with at most `m` elements gives `(-1) ^ m * choose (|B| - 1) m` when
`B` is nonempty. Hence the truncations at odd size are lower bounds for the indicator and the
truncations at even size are upper bounds, and the even truncations are nonnegative. These are the
brackets used by Brun's sieve: with `B` the set of sifting conditions satisfied by an element,
they replace the exact inclusion–exclusion count by a sum over few conditions at a time.

## Main results

* `Finset.sum_powerset_filter_card_le_neg_one_pow`: for nonempty `B`,
  `∑_{G ⊆ B, |G| ≤ m} (-1) ^ |G| = (-1) ^ m * choose (|B| - 1) m`.
* `Finset.sum_powerset_filter_card_le_two_mul_add_one_le`: the odd truncation is at most the
  indicator of `B = ∅`.
* `Finset.le_sum_powerset_filter_card_le_two_mul`: the even truncation is at least the indicator
  of `B = ∅`.
* `Finset.sum_powerset_filter_card_le_two_mul_nonneg`: the even truncation is nonnegative.

## References

* L. Bary-Soroker, D. Koukoulopoulos, G. Kozma, *Irreducibility of random polynomials: general
  measures*, Invent. Math. 233 (2023), §8, (8.1)–(8.3).
-/

public section

namespace Finset

variable {α : Type*} {B : Finset α}

/-- **The truncated alternating sum over subsets.** For a nonempty finite set `B`, the sum of
`(-1) ^ |G|` over the subsets `G ⊆ B` with at most `m` elements is
`(-1) ^ m * choose (|B| - 1) m`. -/
theorem sum_powerset_filter_card_le_neg_one_pow (hB : B.Nonempty) (m : ℕ) :
    ∑ G ∈ B.powerset with #G ≤ m, (-1 : ℤ) ^ #G = (-1) ^ m * (#B - 1).choose m := by
  obtain ⟨n, hn⟩ : ∃ n, #B = n + 1 := Nat.exists_eq_succ_of_ne_zero hB.card_pos.ne'
  have hterm (k : ℕ) (hk : k ∈ range (n + 1 + 1 + (m + 1))) (hk' : k ∉ range (n + 1 + 1)) :
      (n + 1).choose k • (if k ≤ m then (-1 : ℤ) ^ k else 0) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by have := mem_range.not.1 hk'; omega), zero_nsmul]
  have hterm' (k : ℕ) (hk : k ∈ range (n + 1 + 1 + (m + 1))) (hk' : k ∉ range (m + 1)) :
      (n + 1).choose k • (if k ≤ m then (-1 : ℤ) ^ k else 0) = 0 := by
    rw [ite_eq_right (by have := mem_range.not.1 hk'; omega), nsmul_zero]
  rw [sum_filter, sum_powerset_apply_card fun k ↦ if k ≤ m then (-1 : ℤ) ^ k else 0, hn,
    Nat.add_sub_cancel, ← Int.alternating_sum_range_choose_eq_choose,
    sum_subset (range_subset_range.2 (Nat.le_add_right _ (m + 1))) hterm,
    ← sum_subset (range_subset_range.2 (Nat.le_add_left (m + 1) (n + 1 + 1))) hterm']
  refine sum_congr rfl fun k hk ↦ ?_
  rw [ite_eq_left (Nat.lt_succ_iff.1 (mem_range.1 hk)), nsmul_eq_mul, mul_comm]

/-- The truncation at size `0` of the alternating sum over subsets is `1`: only `G = ∅`
contributes. -/
theorem sum_powerset_filter_card_le_zero (B : Finset α) :
    ∑ G ∈ B.powerset with #G ≤ 0, (-1 : ℤ) ^ #G = 1 := by
  rw [sum_eq_single ∅]
  · simp
  · intro G hG hne
    exact absurd (card_eq_zero.1 (Nat.le_zero.1 (mem_filter.1 hG).2)) hne
  · intro h
    exact absurd (mem_filter.2 ⟨empty_mem_powerset B, by simp⟩) h

/-- Every truncation of the alternating sum over the subsets of the empty set is `1`. -/
theorem sum_powerset_empty_filter_card_le (m : ℕ) :
    ∑ G ∈ (∅ : Finset α).powerset with #G ≤ m, (-1 : ℤ) ^ #G = 1 := by
  rw [powerset_empty, filter_true_of_mem fun G hG ↦ by rw [mem_singleton.1 hG]; simp,
    sum_singleton, card_empty, pow_zero]

/-- For a nonempty `B`, the truncation of the alternating sum at an odd size is nonpositive. -/
theorem sum_powerset_filter_card_le_two_mul_add_one_nonpos (hB : B.Nonempty) (v : ℕ) :
    ∑ G ∈ B.powerset with #G ≤ 2 * v + 1, (-1 : ℤ) ^ #G ≤ 0 := by
  rw [sum_powerset_filter_card_le_neg_one_pow hB, (odd_two_mul_add_one v).neg_one_pow]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Int.natCast_nonneg _)

/-- **The upper Bonferroni bracket is nonnegative.** The truncation of the alternating sum over
subsets at an even size is nonnegative, for every finite set. -/
theorem sum_powerset_filter_card_le_two_mul_nonneg (B : Finset α) (v : ℕ) :
    0 ≤ ∑ G ∈ B.powerset with #G ≤ 2 * v, (-1 : ℤ) ^ #G := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · rw [sum_powerset_empty_filter_card_le]
    exact zero_le_one
  · rw [sum_powerset_filter_card_le_neg_one_pow hB, (even_two_mul v).neg_one_pow, one_mul]
    exact Int.natCast_nonneg _

variable [DecidableEq α]

/-- **The lower Bonferroni bracket.** The truncation of the alternating sum over subsets at an
odd size is at most the indicator of `B = ∅`. -/
theorem sum_powerset_filter_card_le_two_mul_add_one_le (B : Finset α) (v : ℕ) :
    ∑ G ∈ B.powerset with #G ≤ 2 * v + 1, (-1 : ℤ) ^ #G ≤ if B = ∅ then 1 else 0 := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · rw [sum_powerset_empty_filter_card_le, ite_eq_left rfl]
  · rw [ite_eq_right hB.ne_empty]
    exact sum_powerset_filter_card_le_two_mul_add_one_nonpos hB v

/-- **The upper Bonferroni bracket.** The truncation of the alternating sum over subsets at an
even size is at least the indicator of `B = ∅`. -/
theorem le_sum_powerset_filter_card_le_two_mul (B : Finset α) (v : ℕ) :
    (if B = ∅ then 1 else 0) ≤ ∑ G ∈ B.powerset with #G ≤ 2 * v, (-1 : ℤ) ^ #G := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · rw [sum_powerset_empty_filter_card_le, ite_eq_left rfl]
  · rw [ite_eq_right hB.ne_empty]
    exact sum_powerset_filter_card_le_two_mul_nonneg B v

/-! ### Examples -/

/-- For a two-element set the brackets at sizes `1` and `2` are `1 - 2 = -1 ≤ 0` and
`1 - 2 + 1 = 0`. -/
example : ∑ G ∈ ({0, 1} : Finset ℕ).powerset with #G ≤ 1, (-1 : ℤ) ^ #G = -1 ∧
    ∑ G ∈ ({0, 1} : Finset ℕ).powerset with #G ≤ 2, (-1 : ℤ) ^ #G = 0 := by
  constructor <;> decide

end Finset
