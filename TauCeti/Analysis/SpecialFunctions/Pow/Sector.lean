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
* `TauCeti.cos_mul_norm_le_re_exp_mul_cpow` bounds `z ^ β` on the closed upper half-plane below
  by a cone inequality, for `0 ≤ β ≤ 2`.
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

/-- In the closed upper half-plane with `0 ≤ β ≤ 2`, the power `z ^ β`, rotated by
`exp (-(β π / 2) i)`, lies in the cone of real part at least `cos (β π / 2)` times the norm. -/
theorem cos_mul_norm_le_re_exp_mul_cpow {z : ℂ} {β : ℝ} (hβ : 0 ≤ β) (hβ2 : β ≤ 2)
    (hz : 0 ≤ z.im) :
    Real.cos (β * Real.pi / 2) * ‖z ^ (β : ℂ)‖ ≤
      (exp ((-(β * Real.pi / 2) : ℝ) * Complex.I) * z ^ (β : ℂ)).re := by
  rcases hβ.eq_or_lt with rfl | hβ
  · simp
  set θ : ℝ := β * Real.pi / 2 with hθdef
  have hθ : 0 ≤ θ ∧ θ ≤ Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  set u : ℂ := exp ((-θ : ℝ) * Complex.I)
  set P : ℂ := z ^ (β : ℂ)
  have harg : |z.arg * β - θ| ≤ θ := by
    apply abs_le.mpr
    constructor <;> dsimp [θ] <;>
      nlinarith [arg_nonneg_iff.mpr hz, arg_le_pi z]
  have hcos : Real.cos θ ≤ Real.cos (z.arg * β - θ) := by
    simpa only [Real.cos_abs] using
      Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hθ.2 harg
  have hure : u.re = Real.cos θ := by
    simpa only [Real.cos_neg] using exp_ofReal_mul_I_re (-θ)
  have huim : u.im = -Real.sin θ := by
    simpa only [Real.sin_neg] using exp_ofReal_mul_I_im (-θ)
  have hre : (u * P).re = ‖P‖ * Real.cos (z.arg * β - θ) := by
    rcases eq_or_ne z 0 with rfl | hz0
    · simp [P, hβ.ne']
    have hPn : ‖P‖ = ‖z‖ ^ β := by
      simp [P]
    simp [P, Complex.mul_re, cpow_ofReal_re, cpow_ofReal_im, hure, huim, Real.cos_sub, hPn]
    ring
  rw [hre]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcos (norm_nonneg P)

end TauCeti

end
