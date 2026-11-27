/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Endpoint variation of complex power kernels

On `[1, ∞)`, the interval kernel `(b^s - a^s) / s` has norm at most the length of the
interval if `Re s ≤ 1`. In an explicit formula this pays for rounding endpoints without
introducing a reciprocal of the magnitude of a zero near the origin.
-/

public section

namespace Complex

/-- On an interval above one and for `Re s ≤ 1`, the norm of the power difference divided by
`s` is at most the interval length. The bound is uniform as `s` approaches zero. -/
theorem norm_ofReal_cpow_sub_ofReal_cpow_div_le_sub {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {s : ℂ} (hs : s.re ≤ 1) : ‖((b : ℂ) ^ s - (a : ℂ) ^ s) / s‖ ≤ b - a := by
  by_cases hs₀ : s = 0
  · simp [hs₀, sub_nonneg.mpr hab]
  simp only [sub_div]
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt (fun x : ℝ ↦ (x : ℂ) ^ s / s) ((t : ℂ) ^ (s - 1)) (Set.Icc a b) t := by
    have ht₀ := zero_lt_one.trans_le (ha.trans ht.1)
    simpa only [mul_div_cancel_left₀ _ hs₀] using
      ((hasDerivAt_ofReal_cpow_const ht₀.ne' hs₀).div_const s).hasDerivWithinAt
  have hnorm (t : ℝ) (ht : t ∈ Set.Ico a b) : ‖(t : ℂ) ^ (s - 1)‖ ≤ 1 := by
    have ht₁ := ha.trans ht.1
    rw [norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ht₁), sub_re, one_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos ht₁ (sub_nonpos.mpr hs)
  simpa only [one_mul] using norm_image_sub_le_of_norm_deriv_le_segment' hderiv hnorm b
    (Set.right_mem_Icc.mpr hab)

end Complex
