/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, OpenAI Codex
-/
module

public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Multiples in natural intervals

The exact number of multiples of `d` in `(a, b]` is `b / d - a / d`.
This supplies the exact local counts for interval sieves. Complementing Mathlib's
`Nat.Ioc_filter_dvd_card_eq_div`, the non-multiples of `d` in `(0, n]` combine with `n / d` to
give `n`, and those in `[1, n)` combine with `(n - 1) / d` to give `n - 1`.
The counting argument is adapted from [Arend Mellendijk, PNT+, BrunTitchmarsh.lean]
(https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/7c7892801a0937aa6925e531a5e2c105bd20690b/PrimeNumberTheoremAnd/BrunTitchmarsh.lean).
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

/-- Among the naturals in `(0, n]`, those not divisible by `d` together with the `n / d`
multiples of `d` account for all `n` elements. -/
theorem Ioc_filter_not_dvd_card_add_div (n d : ℕ) :
    ((Finset.Ioc 0 n).filter (¬ d ∣ ·)).card + n / d = n := by
  have hpart := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 n) (fun x ↦ d ∣ x)
  rw [Ioc_filter_dvd_card_eq_div, Nat.card_Ioc, Nat.sub_zero, add_comm] at hpart
  exact hpart

/-- Among the naturals in `[1, n)`, those not divisible by `d` together with the `(n - 1) / d`
multiples of `d` account for all `n - 1` elements. -/
theorem Ico_filter_not_dvd_card_add_div (n d : ℕ) :
    ((Finset.Ico 1 n).filter (¬ d ∣ ·)).card + (n - 1) / d = n - 1 := by
  rcases n with _ | m
  · simp
  · have hIco : Finset.Ico 1 (m + 1) = Finset.Ioc 0 m := by
      simpa only [Nat.zero_add] using Finset.Ico_add_one_add_one_eq_Ioc 0 m
    rw [hIco, Nat.add_sub_cancel, Ioc_filter_not_dvd_card_add_div]

end Nat
