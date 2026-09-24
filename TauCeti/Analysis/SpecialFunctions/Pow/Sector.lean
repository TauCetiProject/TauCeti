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
A closed symmetric sector can be described by a continuous linear inequality, the principal
inverse power maps the corresponding open sector to the right half-plane, and raising that root
back to the original power recovers the starting point.

## Main results

* `TauCeti.arg_mem_Icc_iff_norm_mul_cos_le_re` characterizes a closed symmetric sector without
  referring to the discontinuous argument function on the target side.
* `TauCeti.cpow_inv_re_pos_of_arg_mem_sector` maps an open sector into the right half-plane.
* `TauCeti.cpow_inv_cpow_of_sector` recovers a point after taking its principal inverse power.
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
  simp only [mem_Icc]
  rw [← abs_le]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [ha.1]
  constructor
  · intro harg
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg z.arg) ha.2 harg
    rw [Real.cos_abs] at hcos
    nlinarith [norm_nonneg z, norm_mul_cos_arg z]
  · intro hsector
    by_contra harg
    have harg' : a < |z.arg| := lt_of_not_ge harg
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi ha.1 (abs_arg_le_pi z) harg'
    rw [Real.cos_abs] at hcos
    nlinarith [norm_pos_iff.mpr hz, norm_mul_cos_arg z]

/-- The principal inverse power maps the sector of opening `βπ` into the open right
half-plane. -/
theorem cpow_inv_re_pos_of_arg_mem_sector {z : ℂ} {β : ℝ} (hβ : 0 < β) (hz : z ≠ 0)
    (harg : z.arg ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2)) :
    0 < (z ^ ((β⁻¹ : ℝ) : ℂ)).re := by
  rw [cpow_ofReal_re]
  have hnorm : 0 < ‖z‖ ^ β⁻¹ := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _
  have hangle : z.arg * β⁻¹ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [← (Set.mem_preimage (f := fun x : ℝ => x * β⁻¹)),
      preimage_mul_const_Ioo₀ _ _ (inv_pos.mpr hβ)]
    simpa [div_inv_eq_mul, div_eq_mul_inv, hβ.ne', mul_comm, mul_left_comm, mul_assoc] using harg
  exact mul_pos hnorm (Real.cos_pos_of_mem_Ioo hangle)

/-- On a sector of half-angle `β * π / 2`, the principal `β`-th root followed by the
principal `β`-th power is the identity, including at zero. -/
theorem cpow_inv_cpow_of_sector {w : ℂ} {β : ℝ} (hβ : 0 < β)
    (hw : |w.arg| ≤ β * Real.pi / 2) :
    (w ^ ((β⁻¹ : ℝ) : ℂ)) ^ (β : ℂ) = w := by
  have hb : |w.arg * β⁻¹| ≤ Real.pi / 2 := by
    rw [← div_eq_mul_inv, abs_div, abs_of_pos hβ, div_le_iff₀ hβ]
    nlinarith [hw]
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  rw [← Complex.cpow_mul]
  · simp [hβ.ne']
  · simp only [mul_im, log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    linarith [Real.pi_pos]
  · simp only [mul_im, log_im, ofReal_re, ofReal_im, mul_zero, zero_add]
    linarith [Real.pi_pos]

end TauCeti

end
