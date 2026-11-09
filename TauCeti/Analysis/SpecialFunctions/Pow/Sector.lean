/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Principal complex powers on a sector

This file records pointwise facts about symmetric angular sectors and principal complex powers.
A closed symmetric sector can be described by a continuous inequality, and the principal
`β`-th root maps the open sector of opening `βπ` to the right half-plane. Recovering a point
from its principal root is `TauCeti.cpow_inv_cpow_of_arg_mem_Ioc`.

## Main results

* `TauCeti.arg_mem_Icc_iff_norm_mul_cos_le_re` characterizes a closed symmetric sector without
  referring to the discontinuous argument function on the target side.
* `TauCeti.cpow_inv_re_pos_of_arg_mem_sector` maps an open sector into the right half-plane.
-/

public section

open Complex Set

namespace TauCeti

/-- A complex number lies in the closed sector of half-opening `a ≤ π` around the positive real
axis exactly when `‖z‖ * cos a ≤ z.re`. The right-hand side is continuous in `z`, so this
characterization passes to limits, unlike the argument itself. For `a = π / 2` this specializes
to `Complex.abs_arg_le_pi_div_two_iff`. -/
theorem arg_mem_Icc_iff_norm_mul_cos_le_re {z : ℂ} {a : ℝ} (ha : a ∈ Icc (0 : ℝ) Real.pi) :
    z.arg ∈ Icc (-a) a ↔ ‖z‖ * Real.cos a ≤ z.re := by
  rw [mem_Icc, ← abs_le]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [ha.1]
  rw [← norm_mul_cos_arg z, ← Real.cos_abs z.arg, mul_le_mul_iff_right₀ (norm_pos_iff.mpr hz),
    Real.strictAntiOn_cos.le_iff_ge ha ⟨abs_nonneg _, abs_arg_le_pi z⟩]

/-- The principal inverse power maps the sector of opening `βπ` into the open right
half-plane. -/
theorem cpow_inv_re_pos_of_arg_mem_sector {z : ℂ} {β : ℝ} (hβ : 0 < β) (hz : z ≠ 0)
    (harg : z.arg ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2)) :
    0 < (z ^ ((β⁻¹ : ℝ) : ℂ)).re := by
  rw [cpow_ofReal_re, ← div_eq_mul_inv]
  refine mul_pos (by positivity) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · rw [lt_div_iff₀ hβ]
    linarith [harg.1]
  · rw [div_lt_iff₀ hβ]
    linarith [harg.2]

end TauCeti

end
