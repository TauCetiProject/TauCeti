/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The subtracted Perron kernel at negative integers

At a negative integer the two powers are real. Taking their difference before estimating
therefore gives a geometric majorant with no factor of two.
-/

public section

open Complex

namespace TauCeti

/-- At `s = -j` with `j` a positive integer, the subtracted Perron quotient for `(a, b]` has norm
at most `a⁻ʲ`. The inequality includes the totalized quotient at `j = 0`. -/
theorem norm_sub_cpow_div_neg_natCast_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (j : ℕ) :
    ‖((b : ℂ) ^ (-(j : ℂ)) - (a : ℂ) ^ (-(j : ℂ))) / (-(j : ℂ))‖ ≤ a⁻¹ ^ j := by
  by_cases hj : j = 0
  · simp [hj]
  have hj₀ := Nat.pos_of_ne_zero hj
  have hj' : (1 : ℝ) ≤ j := Nat.one_le_cast.mpr hj₀
  have hb := ha.trans_le hab
  have hpow : b⁻¹ ^ j ≤ a⁻¹ ^ j :=
    pow_le_pow_left₀ (by positivity : 0 ≤ b⁻¹) (inv_anti₀ ha hab) _
  rw [div_neg, ← neg_div, neg_sub]
  have hcast : (((a⁻¹ ^ j - b⁻¹ ^ j) / (j : ℝ) : ℝ) : ℂ) =
      ((a : ℂ) ^ (-(j : ℂ)) - (b : ℂ) ^ (-(j : ℂ))) / (j : ℂ) := by
    push_cast
    simp only [cpow_neg, cpow_natCast, inv_pow]
  rw [← hcast, norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hpow) (Nat.cast_nonneg j))]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hj₀ : (0 : ℝ) < j)).2
  calc
    a⁻¹ ^ j - b⁻¹ ^ j ≤ a⁻¹ ^ j := sub_le_self _ (by positivity : 0 ≤ b⁻¹ ^ j)
    _ ≤ a⁻¹ ^ j * j := le_mul_of_one_le_right (by positivity) hj'

end TauCeti
