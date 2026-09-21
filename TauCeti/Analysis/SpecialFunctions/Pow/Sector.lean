/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Principal powers on an angular sector

The principal power `z ^ (1 / β)` straightens the sector of opening `βπ` centred on the
positive real axis into the right half-plane.  This file records the three pointwise facts needed
for that construction: the sector avoids the branch cut when its opening is less than `2π`, the
straightened point has positive real part, and raising it back to the power `β` recovers `z`.

These facts are useful when a polygonal corner is normalized to a symmetric sector.  Multiplication
by `I` then carries the right half-plane to the upper half-plane, where Schwarz reflection applies.

## Main results

* `Complex.mem_slitPlane_of_arg_mem_sector` -- a nonzero point in a sector of opening less than
  `2π` avoids the principal branch cut.
* `Complex.cpow_inv_re_pos_of_arg_mem_sector` -- the inverse power maps the sector into the right
  half-plane.
* `Complex.cpow_inv_cpow_eq_of_arg_mem_closed_sector` -- the inverse power is a genuine inverse on
  the closed sector.
-/

public section

open Set

namespace Complex

private theorem mem_slitPlane_of_ne_zero_of_arg_lt_pi {z : ℂ} (hz : z ≠ 0)
    (harg : z.arg < Real.pi) : z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hre0 : z.re ≠ 0 := fun hre0 => hz (ext hre0 h.2)
  have hre : z.re < 0 := lt_of_le_of_ne h.1 hre0
  rw [arg_eq_pi_iff.mpr ⟨hre, h.2⟩] at harg
  exact harg.false

private theorem mul_inv_mem_Ioo_of_mem_sector {x β : ℝ} (hβ : 0 < β)
    (hx : x ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2)) :
    x * β⁻¹ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hβinv : 0 < β⁻¹ := inv_pos.mpr hβ
  constructor
  · have h := mul_lt_mul_of_pos_right hx.1 hβinv
    convert h using 1
    field_simp
  · have h := mul_lt_mul_of_pos_right hx.2 hβinv
    convert h using 1
    field_simp

private theorem mul_inv_mem_Icc_of_mem_closed_sector {x β : ℝ} (hβ : 0 < β)
    (hx : x ∈ Icc (-(Real.pi * β / 2)) (Real.pi * β / 2)) :
    x * β⁻¹ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hβinv : 0 < β⁻¹ := inv_pos.mpr hβ
  constructor
  · have h := mul_le_mul_of_nonneg_right hx.1 hβinv.le
    convert h using 1
    field_simp
  · have h := mul_le_mul_of_nonneg_right hx.2 hβinv.le
    convert h using 1
    field_simp

/-- A nonzero point in a sector of opening `βπ < 2π`, centred on the positive real axis,
belongs to the slit plane. -/
theorem mem_slitPlane_of_arg_mem_sector {z : ℂ} {β : ℝ} (hβ : β < 2) (hz : z ≠ 0)
    (harg : z.arg ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2)) : z ∈ slitPlane := by
  have hlt : Real.pi * β / 2 < Real.pi := by
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hβ)]
  exact mem_slitPlane_of_ne_zero_of_arg_lt_pi hz (harg.2.trans hlt)

/-- A nonzero point in the corresponding closed sector also belongs to the slit plane, provided
the opening is strictly less than `2π`. -/
theorem mem_slitPlane_of_arg_mem_closed_sector {z : ℂ} {β : ℝ} (hβ : β < 2) (hz : z ≠ 0)
    (harg : z.arg ∈ Icc (-(Real.pi * β / 2)) (Real.pi * β / 2)) : z ∈ slitPlane := by
  have hlt : Real.pi * β / 2 < Real.pi := by
    nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hβ)]
  exact mem_slitPlane_of_ne_zero_of_arg_lt_pi hz (harg.2.trans_lt hlt)

/-- The principal inverse power maps the sector of opening `βπ` into the open right
half-plane. -/
theorem cpow_inv_re_pos_of_arg_mem_sector {z : ℂ} {β : ℝ} (hβ : 0 < β) (hz : z ≠ 0)
    (harg : z.arg ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2)) :
    0 < (z ^ ((β⁻¹ : ℝ) : ℂ)).re := by
  rw [cpow_ofReal_re]
  have hnorm : 0 < ‖z‖ ^ β⁻¹ := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _
  have hangle := mul_inv_mem_Ioo_of_mem_sector hβ harg
  exact mul_pos hnorm (Real.cos_pos_of_mem_Ioo hangle)

/-- On the closed sector of opening `βπ`, raising the principal inverse power back to the power
`β` recovers the original point.  The endpoint rays are included. -/
theorem cpow_inv_cpow_eq_of_arg_mem_closed_sector {z : ℂ} {β : ℝ} (hβ : 0 < β)
    (harg : z.arg ∈ Icc (-(Real.pi * β / 2)) (Real.pi * β / 2)) :
    (z ^ ((β⁻¹ : ℝ) : ℂ)) ^ (β : ℂ) = z := by
  have hangle := mul_inv_mem_Icc_of_mem_closed_sector hβ harg
  rw [← cpow_mul]
  · rw [← ofReal_mul, inv_mul_cancel₀ hβ.ne', ofReal_one, cpow_one]
  · simp only [log_im, mul_im, ofReal_re, ofReal_im, mul_zero]
    linarith [hangle.1, Real.pi_pos]
  · simp only [log_im, mul_im, ofReal_re, ofReal_im, mul_zero]
    linarith [hangle.2, Real.pi_pos]

end Complex

end
