/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas

import Mathlib.Tactic.LinearCombination

/-!
# A primitive common denominator of two rationals

For rationals `x` and `y` there is a positive integer `a` clearing both denominators, `a x = b` and
`a y = c` with `b, c ∈ ℤ`, such that the triple `(a, b, c)` is primitive: some integer
combination of `a`, `b` and `c` equals `1`. Applied to the coefficients of a monic rational
quadratic `t² = x t + y`, it rescales the relation to a primitive integral one
`a t² - b t - c = 0`, which is how primitive quadratic equations of irrational numbers enter the
theory of lattices in quadratic fields (D. A. Cox, *Primes of the Form x² + ny²*, §7).

The integer `a` is `x.den` times the denominator of `x.den * y`, that is, the least common
multiple of the two denominators. Dually, any two rationals satisfy a primitive integral linear
relation `u x + v y = 0` with `u, v` coprime.
-/

public section

namespace Rat

/-- **A primitive common denominator.** For rationals `x` and `y` there are integers `a`, `b`, `c`
with `0 < a`, `a x = b` and `a y = c` such that `a`, `b` and `c` generate the unit ideal of `ℤ`. -/
theorem exists_primitive_common_denominator (x y : ℚ) :
    ∃ a b c : ℤ, 0 < a ∧ (a : ℚ) * x = b ∧ (a : ℚ) * y = c ∧
      ∃ u v w : ℤ, u * a + v * b + w * c = 1 := by
  -- Clear the denominator of `x` first, then that of the rational `y' = x.den * y`.
  set y' : ℚ := x.den * y with hy'
  obtain ⟨α, β, hx⟩ := x.isCoprime_num_den
  obtain ⟨γ, δ, hy⟩ := y'.isCoprime_num_den
  -- The Bézout relation for the triple is `δ * y'.den` times `hx`, plus `hy`.
  refine ⟨x.den * y'.den, x.num * y'.den, y'.num,
    mul_pos (mod_cast x.den_pos) (mod_cast y'.den_pos), ?_, ?_, δ * β, δ * α, γ,
    by linear_combination (δ * y'.den) * hx + hy⟩
  · push_cast
    linear_combination (y'.den : ℚ) * x.mul_den_eq_num
  · push_cast
    linear_combination y'.mul_den_eq_num - (y'.den : ℚ) * hy'

/-- **A coprime integral linear relation.** Any two rationals `x` and `y` satisfy `u x + v y = 0`
for coprime integers `u` and `v`. -/
theorem exists_isCoprime_intCast_mul_add_intCast_mul_eq_zero (x y : ℚ) :
    ∃ u v : ℤ, IsCoprime u v ∧ (u : ℚ) * x + (v : ℚ) * y = 0 := by
  by_cases hy : y = 0
  · exact ⟨0, 1, isCoprime_one_right, by simp [hy]⟩
  · refine ⟨(x / y).den, -(x / y).num, (x / y).isCoprime_num_den.symm.neg_right, ?_⟩
    push_cast
    linear_combination y * (x / y).mul_den_eq_num - ((x / y).den : ℚ) * div_mul_cancel₀ x hy

end Rat
