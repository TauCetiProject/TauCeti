/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Bounds from natural reciprocals

A nonzero natural number whose reciprocal, cast into a preordered division semiring, is less than
one is at least two. This converts the reciprocal-sum hypothesis for a hyperbolic triangle group
into the parameter bounds needed for its trigonometric matrix representation.

For three hyperbolic triangle indices, the orbifold deficit
`1 - 1/a - 1/b - 1/c` is at least `1/42`, attained at `(2, 3, 7)`.

The triangle bound follows the numerical case split in H. Stichtenoth,
*Algebraic Function Fields and Codes*, second edition, Exercise 3.18.
-/

public section

namespace TauCeti

/-- A nonzero natural number whose reciprocal is less than one is at least two. -/
theorem two_le_of_cast_inv_lt_one {α : Type*} [DivisionSemiring α] [Preorder α]
    {p : ℕ} (hp : p ≠ 0) (h : (p : α)⁻¹ < 1) : 2 ≤ p := by
  refine (Nat.two_le_iff p).2 ⟨hp, ?_⟩
  rintro rfl
  simp at h

private theorem one_div_nat_le {m n : ℕ} (hm : 0 < m) (h : m ≤ n) :
    (1 : ℚ) / n ≤ 1 / m :=
  one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast h)

/-- For ordered hyperbolic triangle indices, the orbifold deficit is at least `1/42`.
The equality case is realized by `(2, 3, 7)`. -/
private theorem one_div_forty_two_le_hyperbolic_triangle_ordered
    {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hhyper : (1 : ℚ) / a + 1 / b + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  have hc0 : 0 < c := by omega
  -- If the least index is at least four, every reciprocal is at most `1/4`.
  by_cases ha4 : 4 ≤ a
  · have h₁ := one_div_nat_le (m := 4) (by omega) ha4
    have h₂ := one_div_nat_le (m := 4) (by omega) (by omega : 4 ≤ b)
    have h₃ := one_div_nat_le (m := 4) (by omega) (by omega : 4 ≤ c)
    norm_num at h₁ h₂ h₃ ⊢
    linarith
  -- For least index three, the next is three or at least four.
  by_cases ha3 : a = 3
  · subst a
    by_cases hb4 : 4 ≤ b
    · have h₂ := one_div_nat_le (m := 4) (by omega) hb4
      have h₃ := one_div_nat_le (m := 4) (by omega) (hb4.trans hbc)
      norm_num at h₂ h₃ ⊢
      linarith
    · have hb3 : b = 3 := by omega
      subst b
      have hc4 : 4 ≤ c := by
        by_contra h
        have : c = 3 := by omega
        subst c
        norm_num at hhyper
      have h₃ := one_div_nat_le (m := 4) (by omega) hc4
      norm_num at h₃ ⊢
      linarith
  · have ha2 : a = 2 := by omega
    subst a
    -- Only the second indices two, three and four need separate treatment.
    by_cases hb5 : 5 ≤ b
    · have h₂ := one_div_nat_le (m := 5) (by omega) hb5
      have h₃ := one_div_nat_le (m := 5) (by omega) (hb5.trans hbc)
      norm_num at h₂ h₃ ⊢
      linarith
    by_cases hb4 : b = 4
    · subst b
      have hc5 : 5 ≤ c := by
        by_contra h
        have : c = 4 := by omega
        subst c
        norm_num at hhyper
      have h₃ := one_div_nat_le (m := 5) (by omega) hc5
      norm_num at h₃ ⊢
      linarith
    by_cases hb3 : b = 3
    · subst b
      have hc7 : 7 ≤ c := by
        by_contra h
        have hc6 : c ≤ 6 := by omega
        have h₃ := one_div_nat_le (m := c) hc0 hc6
        simp only [one_div] at hhyper
        norm_num at h₃ hhyper
        linarith
      have h₃ := one_div_nat_le (m := 7) (by omega) hc7
      norm_num at h₃ ⊢
      linarith
    · have hb2 : b = 2 := by omega
      subst b
      have hc : 0 ≤ (1 : ℚ) / c := by positivity
      norm_num at hhyper
      linarith

/-- The sharp numerical bound for a hyperbolic triangle of ramification indices.
The equality case is realized by the indices `(2, 3, 7)`. -/
theorem one_div_forty_two_le_hyperbolic_triangle
    {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hhyper : (1 : ℚ) / a + 1 / b + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact one_div_forty_two_le_hyperbolic_triangle_ordered ha hab hbc hhyper
    · rcases le_total a c with hac | hca
      · have h := one_div_forty_two_le_hyperbolic_triangle_ordered ha hac hcb
          (by linarith : (1 : ℚ) / a + 1 / c + 1 / b < 1)
        linarith
      · have h := one_div_forty_two_le_hyperbolic_triangle_ordered hc hca hab
          (by linarith : (1 : ℚ) / c + 1 / a + 1 / b < 1)
        linarith
  · rcases le_total a c with hac | hca
    · have h := one_div_forty_two_le_hyperbolic_triangle_ordered hb hba hac
        (by linarith : (1 : ℚ) / b + 1 / a + 1 / c < 1)
      linarith
    · rcases le_total b c with hbc | hcb
      · have h := one_div_forty_two_le_hyperbolic_triangle_ordered hb hbc hca
          (by linarith : (1 : ℚ) / b + 1 / c + 1 / a < 1)
        linarith
      · have h := one_div_forty_two_le_hyperbolic_triangle_ordered hc hcb hba
          (by linarith : (1 : ℚ) / c + 1 / b + 1 / a < 1)
        linarith

/-- The triangle indices `(2, 3, 7)` attain the bound. -/
theorem two_three_seven_deficit_eq_one_div_forty_two :
    (1 : ℚ) - 1 / 2 - 1 / 3 - 1 / 7 = 1 / 42 := by
  norm_num

end TauCeti
