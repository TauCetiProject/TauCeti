/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Principal powers on an angular sector

The principal power `z ^ (1 / β)` straightens the sector of opening `βπ` centred on the
positive real axis into the right half-plane.  This file records the two pointwise power facts
needed for that construction: the straightened point has positive real part, and raising it back
to the power `β` recovers `z`.

These facts are useful when a polygonal corner is normalized to a symmetric sector.  Multiplication
by `I` then carries the right half-plane to the upper half-plane, where Schwarz reflection applies.

## Main results

* `Complex.cpow_inv_re_pos_of_arg_mem_sector` -- the inverse power maps the sector into the right
  half-plane.
* `Complex.cpow_inv_cpow_eq_of_arg_mem_closed_sector` -- the inverse power is a genuine inverse on
  the closed sector.
-/

public section

open Set

namespace Complex

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
@[simp] theorem cpow_inv_cpow_eq_of_arg_mem_closed_sector {z : ℂ} {β : ℝ} (hβ : 0 < β)
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
