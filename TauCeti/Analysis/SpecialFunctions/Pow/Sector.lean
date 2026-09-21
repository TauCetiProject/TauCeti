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
positive real axis into the right half-plane.  This file records the pointwise facts needed for
that construction: a closed symmetric sector is cut out by a single linear inequality, the
straightened point has positive real part, and raising it back to the power `β` recovers `z`.

These facts are useful when a polygonal corner is normalized to a symmetric sector.  Multiplication
by `I` then carries the right half-plane to the upper half-plane, where Schwarz reflection applies.

## Main results

* `Complex.arg_mem_Icc_iff_norm_mul_cos_le_re` -- a closed symmetric sector of half-opening `a` is
  the set where `‖z‖ * cos a ≤ z.re`, a description free of the argument branch cut.
* `Complex.cpow_inv_re_pos_of_arg_mem_sector` -- the inverse power maps the sector into the right
  half-plane.
* `Complex.cpow_inv_cpow_eq_of_arg_mem` -- the inverse power is a genuine inverse throughout the
  principal-branch range.
-/

public section

open Set

namespace Complex

/-- A complex number lies in the closed sector of half-opening `a ≤ π` around the positive real
axis exactly when `‖z‖ * cos a ≤ z.re`.  The right-hand side is continuous in `z`, so this
characterization passes to limits, unlike the argument itself.  For `a = π / 2` this specializes
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

/-- If dividing the argument by `β` stays in the principal-argument range, raising the principal
inverse power back to the power `β` recovers the original point. -/
@[simp] theorem cpow_inv_cpow_eq_of_arg_mem {z : ℂ} {β : ℝ} (hβ : 0 < β)
    (harg : z.arg ∈ Ioc (-(Real.pi * β)) (Real.pi * β)) :
    (z ^ (β : ℂ)⁻¹) ^ (β : ℂ) = z := by
  rw [← ofReal_inv]
  have hangle : z.arg * β⁻¹ ∈ Ioc (-Real.pi) Real.pi := by
    rw [← (Set.mem_preimage (f := fun x : ℝ => x * β⁻¹)),
      preimage_mul_const_Ioc₀ _ _ (inv_pos.mpr hβ)]
    simpa [div_inv_eq_mul, hβ.ne', mul_comm] using harg
  rw [← cpow_mul]
  · rw [← ofReal_mul, inv_mul_cancel₀ hβ.ne', ofReal_one, cpow_one]
  · simp only [log_im, mul_im, ofReal_re, ofReal_im, mul_zero]
    linarith [hangle.1, Real.pi_pos]
  · simp only [log_im, mul_im, ofReal_re, ofReal_im, mul_zero]
    linarith [hangle.2, Real.pi_pos]

end Complex

end
