/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, OpenAI Codex
-/
module

public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Counting in natural intervals

The exact number of multiples of `d` in `(a, b]` is `b / d - a / d`.
This supplies the exact local counts for interval sieves.
The counting argument is adapted from [Arend Mellendijk, PNT+, BrunTitchmarsh.lean]
(https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/7c7892801a0937aa6925e531a5e2c105bd20690b/PrimeNumberTheoremAnd/BrunTitchmarsh.lean).

The window `[a + 1 - b, a + b)` of the natural numbers `k` with `|k - a| < b` has at most `2 * b`
elements; dyadic decompositions sum over such windows of neighbouring scales.
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

/-- The window `[a + 1 - b, a + b)` of the natural numbers `k` with `|k - a| < b` has at most
`2 * b` elements. -/
theorem card_Ico_add_one_sub_add_le (a b : ℕ) :
    (Finset.Ico (a + 1 - b) (a + b)).card ≤ 2 * b := by
  rw [card_Ico]
  omega

end Nat
