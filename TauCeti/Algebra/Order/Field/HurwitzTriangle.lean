/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# The sharp reciprocal bound for hyperbolic triples

For natural numbers `a, b, c ≥ 2` with `1/a + 1/b + 1/c < 1`, the deficit
`1 - 1/a - 1/b - 1/c` is at least `1/42`, attained at `(2, 3, 7)`. Applied to
ramification indices, this is the numerical part of Hurwitz's sharp `84(g - 1)`
bound for finite automorphism groups.

The bound is stated in any linearly ordered field, for arbitrary orders of the three indices.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Exercise 3.18.
-/

public section

namespace TauCeti

variable {K : Type*}

/-- The sharp numerical bound for a hyperbolic triple of natural numbers, read in a linearly
ordered field. The equality case is realized by the indices `(2, 3, 7)`. -/
theorem one_div_forty_two_le_hyperbolic_triangle_deficit
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hhyper : (1 : K) / a + 1 / b + 1 / c < 1) :
    (1 : K) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  wlog hab : a ≤ b generalizing a b c
  · linarith [this hb ha hc (by linarith) (by omega)]
  wlog hbc : b ≤ c generalizing a b c
  · rcases le_total a c with hac | hca
    · linarith [this ha hc hb (by linarith) hac (by omega)]
    · linarith [this hc ha hb (by linarith) hca hab]
  -- A sorted hyperbolic triple dominates `(2, 3, 7)`, `(2, 4, 5)` or `(3, 3, 4)` entrywise, and
  -- the deficit increases in each entry.
  rcases (by omega : a = 2 ∧ b = 2 ∨ a = 2 ∧ b = 3 ∨ a = 2 ∧ 4 ≤ b ∨ 3 ≤ a) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hb4⟩ | ha3
  · norm_num at hhyper
    exact absurd hhyper c.cast_nonneg.not_gt
  · have hc7 : 7 ≤ c := by
      by_contra
      interval_cases c <;> norm_num at hhyper
    calc (1 : K) / 42 = 1 - 1 / (2 : ℕ) - 1 / (3 : ℕ) - 1 / (7 : ℕ) := by norm_num
      _ ≤ _ := by gcongr
  · have hc5 : 5 ≤ c := by
      by_contra
      obtain ⟨rfl, rfl⟩ : b = 4 ∧ c = 4 := by omega
      norm_num at hhyper
    calc (1 : K) / 42 ≤ 1 - 1 / (2 : ℕ) - 1 / (4 : ℕ) - 1 / (5 : ℕ) := by norm_num
      _ ≤ _ := by gcongr
  · have hc4 : 4 ≤ c := by
      by_contra
      obtain ⟨rfl, rfl, rfl⟩ : a = 3 ∧ b = 3 ∧ c = 3 := by omega
      norm_num at hhyper
    calc (1 : K) / 42 ≤ 1 - 1 / (3 : ℕ) - 1 / (3 : ℕ) - 1 / (4 : ℕ) := by norm_num
      _ ≤ _ := by gcongr; omega

/-- The triangle indices `(2, 3, 7)` attain the bound. -/
theorem two_three_seven_deficit_eq_one_div_forty_two [DivisionRing K] [CharZero K] :
    (1 : K) - 1 / 2 - 1 / 3 - 1 / 7 = 1 / 42 := by
  norm_num

end TauCeti
