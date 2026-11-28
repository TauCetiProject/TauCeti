/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, OpenAI Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Count
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Counting in natural intervals

The exact number of multiples of `d` in `(a, b]` is `b / d - a / d`.
This supplies the exact local counts for interval sieves. A sum over the multiples of `p` in
`[1, K]` is the sum over `p * k` for `k ∈ [1, K / p]`.
The counting argument is adapted from [Arend Mellendijk, PNT+, BrunTitchmarsh.lean]
(https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/7c7892801a0937aa6925e531a5e2c105bd20690b/PrimeNumberTheoremAnd/BrunTitchmarsh.lean).

For a decidable predicate `p`, the number of `n` in a closed interval `[l, u]` satisfying `p` is
the difference `Nat.count p (u + 1) - Nat.count p l` of two initial counts
(`Nat.card_filter_Icc_eq_count_sub`).

A window `[lo, a + b)` whose lower end `lo` is at least the truncated difference `a - b` has at
most `2 * b` elements. This covers both `[a - b, a + b)`, the `k` with `a ≤ k + b` and
`k < a + b`, and `[a + 1 - b, a + b)`, the `k` with `a < k + b` and `k < a + b`. Dyadic
decompositions sum over such windows of neighbouring scales.
-/

public section

namespace Nat

/-- The number of multiples in a half-open natural interval is a difference of quotients.
This includes a zero divisor and intervals whose endpoints are reversed. -/
theorem Ioc_filter_dvd_card (a b d : ℕ) :
    ((Finset.Ioc a b).filter (d ∣ ·)).card = b / d - a / d := by
  rcases le_total a b with h | h
  · have hcard := Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
      (s := Finset.Ioc 0 a) (t := Finset.Ioc a b) (p := (d ∣ ·)) (q := (d ∣ ·))
      (Finset.Ioc_disjoint_Ioc_of_le le_rfl))
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) h,
      Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hcard
    omega
  · simp [Finset.Ioc_eq_empty_of_le h, Nat.div_le_div_right h]

/-- A sum over the multiples of `p` in `[1, K]` is a sum over `p * k` for `k ∈ [1, K / p]`. Both
sides vanish for `p = 0`. -/
theorem sum_Icc_filter_dvd_eq {M : Type*} [AddCommMonoid M] (g : ℕ → M) (p K : ℕ) :
    ∑ n ∈ Finset.Icc 1 K with p ∣ n, g n = ∑ k ∈ Finset.Icc 1 (K / p), g (p * k) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [Nat.div_zero, Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty]
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_Icc, zero_dvd_iff] at hn
    omega
  have hp' : 0 < p := Nat.pos_of_ne_zero hp
  refine Eq.trans ?_ (Finset.sum_map (Finset.Icc 1 (K / p)) ⟨(p * ·), mul_right_injective₀ hp⟩ g)
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨h1, hK⟩, k, rfl⟩
    refine ⟨k, ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1), ?_⟩, rfl⟩
    rwa [Nat.le_div_iff_mul_le hp', mul_comm]
  · rintro ⟨k, ⟨hk1, hkK⟩, rfl⟩
    rw [Nat.le_div_iff_mul_le hp', mul_comm] at hkK
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp (by omega)), hkK⟩, dvd_mul_right p k⟩

/-- For a decidable predicate `p`, the number of `n` in a closed interval `[l, u]` satisfying `p` is
the difference `Nat.count p (u + 1) - Nat.count p l` of two initial counts
(`Nat.card_filter_Icc_eq_count_sub`).

A window `[lo, a + b)` whose lower end `lo` is at least the truncated difference `a - b` has
at most `2 * b` elements. The bound is attained by `[a - b, a + b)` when `b ≤ a`. -/
theorem card_Ico_add_le_two_mul_of_sub_le (a b : ℕ) {lo : ℕ} (h : a - b ≤ lo) :
    (Finset.Ico lo (a + b)).card ≤ 2 * b := by
  rw [card_Ico]
  omega

/-- The number of `n` in `[l, u]` satisfying `p` is `Nat.count p (u + 1) - Nat.count p l`, with
natural-number subtraction. For `l > u` the interval is empty and both sides are zero.

This is the splitting of a filtered initial range at `l` with which Mathlib's
`Nat.primeCounting'_add_le` begins, stated for an arbitrary decidable predicate and as an
equality. -/
theorem card_filter_Icc_eq_count_sub (p : ℕ → Prop) [DecidablePred p] (l u : ℕ) :
    ((Finset.Icc l u).filter p).card = count p (u + 1) - count p l := by
  rcases le_or_gt l (u + 1) with h | h
  · have hsplit := Finset.sum_range_add_sum_Ico (fun n ↦ if p n then 1 else 0) h
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.card_filter, count_eq_card_filter_range,
      count_eq_card_filter_range, Finset.card_filter, Finset.card_filter, ← hsplit,
      Nat.add_sub_cancel_left]
  · rw [Finset.Icc_eq_empty (by omega), Finset.filter_empty, Finset.card_empty, eq_comm,
      Nat.sub_eq_zero_iff_le]
    exact count_monotone p (by omega)

end Nat
