/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lower bound for the gap from a decaying exponential

The gap `1 - exp (-t)` admits a lower bound linear in `t` up to `t = 1` and constant
thereafter. This quantifies the difference between a main term and an exponentially
attenuated copy of it.
-/

public section

namespace Real

/-- For nonnegative `t`, the gap `1 - exp (-t)` is at least half of `min 1 t`. -/
theorem min_one_div_two_le_one_sub_exp_neg {t : ℝ} (ht : 0 ≤ t) :
    min 1 t / 2 ≤ 1 - exp (-t) := by
  have hden : 0 < 1 + t := by linarith
  have hinv : exp (-t) ≤ (1 + t)⁻¹ := by
    rw [exp_neg]
    exact inv_anti₀ hden (by simpa [add_comm] using add_one_le_exp t)
  have hfrac : min 1 t / 2 ≤ t / (1 + t) := by
    rcases le_total t 1 with h | h
    · rw [min_eq_right h, div_le_div_iff₀ (by norm_num) hden]
      nlinarith [mul_nonneg ht (sub_nonneg.mpr h)]
    · rw [min_eq_left h, div_le_div_iff₀ (by norm_num) hden]
      linarith
  calc
    _ ≤ t / (1 + t) := hfrac
    _ = 1 - (1 + t)⁻¹ := by field_simp; ring
    _ ≤ _ := sub_le_sub_left hinv _

end Real
