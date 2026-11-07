/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# The sharp reciprocal bound for hyperbolic triples

For natural numbers `a, b, c ≥ 2` with `1/a + 1/b + 1/c < 1`, the deficit
`1 - 1/a - 1/b - 1/c` is at least `1/42`, attained at `(2, 3, 7)`. Applied to
ramification indices, this is the numerical part of Hurwitz's sharp `84(g - 1)`
bound for finite automorphism groups.

The result is stated for arbitrary orders of the three indices.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Exercise 3.18.
-/

public section

namespace TauCeti

/-- If the least of three indices is at least four, the deficit is at least `1/4`, which is
at least `1/42`. -/
private theorem one_div_forty_two_le_deficit_of_four_le
    {a b c : ℕ} (ha4 : 4 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (1 : ℚ) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  have h₁ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (a : ℚ))
      (by norm_num) (by exact_mod_cast ha4)
  have h₂ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (b : ℚ))
      (by norm_num) (by exact_mod_cast (by omega : 4 ≤ b))
  have h₃ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (c : ℚ))
      (by norm_num) (by exact_mod_cast (by omega : 4 ≤ c))
  norm_num at h₁ h₂ h₃ ⊢
  linarith

/-- For least index three, the deficit of a hyperbolic triple is at least `1/42`. -/
private theorem one_div_forty_two_le_deficit_of_eq_three
    {b c : ℕ} (hab : 3 ≤ b) (hbc : b ≤ c)
    (hhyper : (1 : ℚ) / (3 : ℕ) + 1 / b + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / (3 : ℕ) - 1 / b - 1 / c := by
  by_cases hb4 : 4 ≤ b
  · have h₂ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (b : ℚ))
      (by norm_num) (by exact_mod_cast hb4)
    have h₃ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (c : ℚ))
      (by norm_num) (by exact_mod_cast (hb4.trans hbc))
    norm_num at h₂ h₃ ⊢
    linarith
  · have hb3 : b = 3 := by omega
    subst b
    have hc4 : 4 ≤ c := by
      by_contra h
      have : c = 3 := by omega
      subst c
      norm_num at hhyper
    have h₃ := one_div_le_one_div_of_le (a := (4 : ℚ)) (b := (c : ℚ))
      (by norm_num) (by exact_mod_cast hc4)
    norm_num at h₃ ⊢
    linarith

/-- For least index two and second index three, the deficit of a hyperbolic triple is at least
`1/42`. -/
private theorem one_div_forty_two_le_deficit_of_two_three
    {c : ℕ} (hc0 : 0 < c)
    (hhyper : (1 : ℚ) / (2 : ℕ) + 1 / (3 : ℕ) + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / (2 : ℕ) - 1 / (3 : ℕ) - 1 / c := by
  have hc7 : 7 ≤ c := by
    by_contra h
    have hc6 : c ≤ 6 := by omega
    have h₃ := one_div_le_one_div_of_le (a := (c : ℚ)) (b := (6 : ℚ))
      (by exact_mod_cast hc0) (by exact_mod_cast hc6)
    simp only [one_div] at hhyper
    norm_num at h₃ hhyper
    linarith
  have h₃ := one_div_le_one_div_of_le (a := (7 : ℚ)) (b := (c : ℚ))
    (by norm_num) (by exact_mod_cast hc7)
  norm_num at h₃ ⊢
  linarith

/-- For least index two, the deficit of a hyperbolic triple is at least `1/42`. -/
private theorem one_div_forty_two_le_deficit_of_eq_two
    {b c : ℕ} (hab : 2 ≤ b) (hbc : b ≤ c) (hc0 : 0 < c)
    (hhyper : (1 : ℚ) / (2 : ℕ) + 1 / b + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / (2 : ℕ) - 1 / b - 1 / c := by
  -- Only the second indices two, three and four need separate treatment.
  by_cases hb5 : 5 ≤ b
  · have h₂ := one_div_le_one_div_of_le (a := (5 : ℚ)) (b := (b : ℚ))
      (by norm_num) (by exact_mod_cast hb5)
    have h₃ := one_div_le_one_div_of_le (a := (5 : ℚ)) (b := (c : ℚ))
      (by norm_num) (by exact_mod_cast (hb5.trans hbc))
    norm_num at h₂ h₃ ⊢
    linarith
  by_cases hb4 : b = 4
  · subst b
    have hc5 : 5 ≤ c := by
      by_contra h
      have : c = 4 := by omega
      subst c
      norm_num at hhyper
    have h₃ := one_div_le_one_div_of_le (a := (5 : ℚ)) (b := (c : ℚ))
      (by norm_num) (by exact_mod_cast hc5)
    norm_num at h₃ ⊢
    linarith
  by_cases hb3 : b = 3
  · subst b
    exact one_div_forty_two_le_deficit_of_two_three hc0 hhyper
  · have hb2 : b = 2 := by omega
    subst b
    norm_num at hhyper
    linarith

/-- For ordered hyperbolic triangle indices, the orbifold deficit is at least `1/42`.
The equality case is realized by `(2, 3, 7)`. -/
private theorem one_div_forty_two_le_hyperbolic_triangle_deficit_ordered
    {a b c : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hhyper : (1 : ℚ) / a + 1 / b + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  have hc0 : 0 < c := by omega
  by_cases ha4 : 4 ≤ a
  · exact one_div_forty_two_le_deficit_of_four_le ha4 hab hbc
  by_cases ha3 : a = 3
  · subst a
    exact one_div_forty_two_le_deficit_of_eq_three hab hbc hhyper
  · have ha2 : a = 2 := by omega
    subst a
    exact one_div_forty_two_le_deficit_of_eq_two hab hbc hc0 hhyper

/-- The sharp numerical bound for a hyperbolic triple of natural numbers.
The equality case is realized by the indices `(2, 3, 7)`. -/
theorem one_div_forty_two_le_hyperbolic_triangle_deficit
    {a b c : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hhyper : (1 : ℚ) / a + 1 / b + 1 / c < 1) :
    (1 : ℚ) / 42 ≤ 1 - 1 / a - 1 / b - 1 / c := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact one_div_forty_two_le_hyperbolic_triangle_deficit_ordered ha hab hbc hhyper
    · rcases le_total a c with hac | hca
      · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered ha hac hcb
          (by linarith : (1 : ℚ) / a + 1 / c + 1 / b < 1)
        linarith
      · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered hc hca hab
          (by linarith : (1 : ℚ) / c + 1 / a + 1 / b < 1)
        linarith
  · rcases le_total a c with hac | hca
    · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered hb hba hac
        (by linarith : (1 : ℚ) / b + 1 / a + 1 / c < 1)
      linarith
    · rcases le_total b c with hbc | hcb
      · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered hb hbc hca
          (by linarith : (1 : ℚ) / b + 1 / c + 1 / a < 1)
        linarith
      · have h := one_div_forty_two_le_hyperbolic_triangle_deficit_ordered hc hcb hba
          (by linarith : (1 : ℚ) / c + 1 / b + 1 / a < 1)
        linarith

/-- The triangle indices `(2, 3, 7)` attain the bound. -/
theorem two_three_seven_deficit_eq_one_div_forty_two :
    (1 : ℚ) - 1 / 2 - 1 / 3 - 1 / 7 = 1 / 42 := by
  norm_num

end TauCeti
