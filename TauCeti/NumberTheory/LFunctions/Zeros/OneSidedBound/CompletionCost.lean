/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The cost of completing a family in the covolume lower bound

When a family misses at most a fraction `4 / b²` of the target dimension, the vectors
added to complete it to a basis cost at most `d * b` if each costs at most `2 * x₁² * b² + b`.
Here `d` is the target dimension, `2 * x₁² * b²` bounds each added vector's logarithmic squared
norm, and `b` is a height allowance for its denominator. Together with the error in the
determinant ratio, this cost fits inside the fourth-logarithmic-power error in the lower bound.

The budgets and comparison are those of `New.Data.mul_completion_cost_le` and the final
estimate in `New.Data.integral_forms_long`, in `grh/src/New/Determinant/Twist/LongForms.lean`
of lsernau/grh-lean at commit `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound

/-- At the separated scales `2 ≤ x₁` and `x₁⁶ ≤ b`, the cost of the `n'` vectors added to
complete a nearly spanning family to a basis in dimension `d` is at most `d * b`. -/
theorem mul_completion_cost_le {n' d : ℕ} {x₁ b : ℝ}
    (hx₁ : 2 ≤ x₁) (hb : x₁ ^ 6 ≤ b) (hn' : (n' : ℝ) ≤ 4 / b ^ 2 * d) :
    (n' : ℝ) * (2 * x₁ ^ 2 * b ^ 2 + b) ≤ d * b := by
  have h₁ : 16 ≤ x₁ ^ 4 := by
    calc
      16 = (2 : ℝ) ^ 4 := by norm_num
      _ ≤ x₁ ^ 4 := pow_le_pow_left₀ (by norm_num) hx₁ 4
  have h₂ : 16 * x₁ ^ 2 ≤ b := by
    calc
      16 * x₁ ^ 2 ≤ x₁ ^ 4 * x₁ ^ 2 := by gcongr
      _ = x₁ ^ 6 := by ring
      _ ≤ b := hb
  have hb₄ : 4 ≤ b := by nlinarith
  have hb₀ : 0 < b := by linarith
  have hsmall : 4 / b ≤ b / 2 := by
    calc
      4 / b ≤ 4 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hb₄
      _ ≤ b / 2 := by linarith
  calc
    (n' : ℝ) * (2 * x₁ ^ 2 * b ^ 2 + b) ≤ (4 / b ^ 2 * d) * (2 * x₁ ^ 2 * b ^ 2 + b) :=
      mul_le_mul_of_nonneg_right hn' (by positivity)
    _ = (d : ℝ) * (8 * x₁ ^ 2 + 4 / b) := by
      field_simp [hb₀.ne']
      ring
    _ ≤ d * b := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

/-- The cost of the added basis vectors and the error in the determinant ratio fit within
`3 d A (log b)^4`, where `A` is the product of the number of places and the large derivative
order. The same bound works in dimension zero. -/
theorem completion_cost_add_ratio_error_le {n' d : ℕ} {x₁ b A : ℝ}
    (hx₁ : 2 ≤ x₁) (hb : x₁ ^ 6 ≤ b) (hn' : (n' : ℝ) ≤ 4 / b ^ 2 * d)
    (herror : b ≤ A * Real.log b ^ 4) :
    (n' : ℝ) * (2 * x₁ ^ 2 * b ^ 2 + b) + d * (b + A * Real.log b ^ 4) ≤
      3 * d * A * Real.log b ^ 4 := by
  have hcomp := mul_completion_cost_le hx₁ hb hn'
  have habsorb := mul_le_mul_of_nonneg_left herror (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  linear_combination hcomp + 2 * habsorb

end TauCeti.OneSidedBound
