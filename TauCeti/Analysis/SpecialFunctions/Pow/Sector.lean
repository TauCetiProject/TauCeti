/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Complex.ReImTopology

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
* `TauCeti.arg_mem_Icc_of_arg_mem_sector` passes the closed-sector condition on the open upper
  part of a set to its closed upper part by continuity.
* `TauCeti.im_I_mul_cpow_inv_eq_zero` sends the boundary rays of a sector to the real axis under
  the power coordinate `I * w ^ (1 / β)`.
* `TauCeti.cos_mul_norm_rpow_le_re_exp_mul_cpow` is the cone inequality
  `cos δ ‖z‖ ^ y ≤ Re (exp (-φ i) z ^ y)` when the phase `arg z * y` lies within `δ ≤ π` of `φ`;
  the next three results are its special cases.
* `TauCeti.cos_mul_norm_le_re_exp_mul_cpow` bounds `z ^ β` on the closed upper half-plane below
  by a cone inequality, for `0 ≤ β ≤ 2`.
* `TauCeti.cos_mul_norm_le_re_cpow` is the same cone inequality on the closed right half-plane.
* `TauCeti.cos_mul_pi_div_two_pos`: the cone constant `cos (β π / 2)` is positive for
  `0 ≤ β < 1`.
* `TauCeti.cos_mul_norm_rpow_le_re_cpow` bounds the real part of `z ^ y` below by
  `cos (y π) ‖z‖ ^ y` on the whole plane, for `|y| ≤ 1`.
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
theorem cpow_inv_re_pos_of_arg_mem_sector {z : ℂ} {β : ℝ} (hz : z ≠ 0)
    (harg : z.arg ∈ Ioo (-(Real.pi * β / 2)) (Real.pi * β / 2)) :
    0 < (z ^ ((β⁻¹ : ℝ) : ℂ)).re := by
  -- a nonempty sector has positive opening
  have hβ : 0 < β := by
    by_contra hb
    nlinarith [harg.1.trans harg.2, mul_nonneg Real.pi_pos.le (neg_nonneg.2 (not_lt.1 hb))]
  rw [cpow_ofReal_re, ← div_eq_mul_inv]
  refine mul_pos (by positivity) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
  · rw [lt_div_iff₀ hβ]
    linarith [harg.1]
  · rw [div_lt_iff₀ hβ]
    linarith [harg.2]

/-- A sector of opening `β * π` with `β < 2` has half-opening less than `π`. -/
theorem pi_mul_div_two_lt_pi {β : ℝ} (hβ : β < 2) :
    β * Real.pi / 2 < Real.pi := by
  nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hβ)]

/-- The closed upper part stays in the closed sector of half-opening `a`: the closed-sector
argument condition on the open upper part passes to its closure by continuity of `f`. -/
theorem arg_mem_Icc_of_arg_mem_sector {Ω : Set ℂ} {f : ℂ → ℂ} {a : ℝ}
    (hΩopen : IsOpen Ω) (ha : a ∈ Icc (0 : ℝ) Real.pi)
    (hfcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hsector_open : ∀ z ∈ Ω ∩ {z : ℂ | 0 < z.im}, (f z).arg ∈ Icc (-a) a)
    {z : ℂ} (hz : z ∈ Ω ∩ {z : ℂ | 0 ≤ z.im}) :
    (f z).arg ∈ Icc (-a) a := by
  have hzclosure : z ∈ closure (Ω ∩ {y : ℂ | 0 < y.im}) := by
    apply hΩopen.inter_closure
    exact ⟨hz.1, by simpa only [Complex.closure_setOfPred_lt_im, mem_ofPred_eq] using hz.2⟩
  have hqcont : ContinuousWithinAt f (Ω ∩ {y : ℂ | 0 < y.im}) z :=
    (hfcont z hz).mono fun y hy => ⟨hy.1, by simpa only [mem_ofPred_eq] using hy.2.le⟩
  have htarget : IsClosed {q : ℂ | ‖q‖ * Real.cos a ≤ q.re} :=
    isClosed_le (continuous_norm.mul continuous_const) Complex.continuous_re
  apply (arg_mem_Icc_iff_norm_mul_cos_le_re ha).2
  have hmem : f z ∈ closure {q : ℂ | ‖q‖ * Real.cos a ≤ q.re} := by
    apply hqcont.mem_closure hzclosure
    intro y hy
    exact (arg_mem_Icc_iff_norm_mul_cos_le_re ha).1 (hsector_open y hy)
  simpa only [htarget.closure_eq, mem_ofPred_eq] using hmem

/-- A point `w` that is zero or whose argument has absolute value `β * π / 2` goes to the real axis
under the power coordinate `I * w ^ (1 / β)`: the boundary rays of the sector of opening `β * π`
become the real axis. -/
theorem im_I_mul_cpow_inv_eq_zero {w : ℂ} {β : ℝ} (hβ : 0 < β)
    (hw : w ≠ 0 → |w.arg| = β * Real.pi / 2) :
    (Complex.I * w ^ ((β⁻¹ : ℝ) : ℂ)).im = 0 := by
  by_cases hw0 : w = 0
  · simp [hw0, ofReal_ne_zero.mpr hβ.ne']
  · have heq : |w.arg * β⁻¹| = Real.pi / 2 := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hβ), hw hw0]
      field_simp [hβ.ne']
    simp only [I_mul_im, cpow_ofReal_re]
    rw [← Real.cos_abs, heq, Real.cos_pi_div_two, mul_zero]

/-- For `0 ≤ β < 1`, the cone constant `cos (β π / 2)` is positive. -/
theorem cos_mul_pi_div_two_pos {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) :
    0 < Real.cos (β * Real.pi / 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

/-- **Cone bound for a rotated real power.** If the phase `arg z * y` of the cosine formula for
the real part of `z ^ y` lies within `δ ≤ π` of `φ`, then `z ^ y`, rotated by `exp (-φ i)`, has
real part at least `cos δ` times `‖z‖ ^ y`. -/
theorem cos_mul_norm_rpow_le_re_exp_mul_cpow {z : ℂ} {y φ δ : ℝ} (h : |arg z * y - φ| ≤ δ)
    (hδ : δ ≤ Real.pi) :
    Real.cos δ * ‖z‖ ^ y ≤ (exp ((-φ : ℝ) * Complex.I) * z ^ (y : ℂ)).re := by
  have hre : (exp ((-φ : ℝ) * Complex.I) * z ^ (y : ℂ)).re =
      ‖z‖ ^ y * Real.cos (arg z * y - φ) := by
    rw [mul_re, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, cpow_ofReal_re, cpow_ofReal_im,
      Real.cos_neg, Real.sin_neg, Real.cos_sub]
    ring
  rw [hre, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (norm_nonneg z) y)
  rw [← Real.cos_abs (arg z * y - φ)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hδ h

/-- In the closed right half-plane with `0 ≤ β ≤ 2`, the power `z ^ β` lies in the cone of real
part at least `cos (β π / 2)` times the norm. -/
theorem cos_mul_norm_le_re_cpow {z : ℂ} {β : ℝ} (hβ : 0 ≤ β) (hβ2 : β ≤ 2) (hz : 0 ≤ z.re) :
    Real.cos (β * Real.pi / 2) * ‖z ^ (β : ℂ)‖ ≤ (z ^ (β : ℂ)).re := by
  have harg : |z.arg| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr hz
  have h := cos_mul_norm_rpow_le_re_exp_mul_cpow (z := z) (y := β) (φ := 0)
    (δ := β * Real.pi / 2) (by
      rw [sub_zero, abs_mul, abs_of_nonneg hβ]
      nlinarith) (by nlinarith [Real.pi_pos])
  simpa [norm_cpow_real] using h

/-- In the closed upper half-plane with `0 ≤ β ≤ 2`, the power `z ^ β`, rotated by
`exp (-(β π / 2) i)`, lies in the cone of real part at least `cos (β π / 2)` times the norm. -/
theorem cos_mul_norm_le_re_exp_mul_cpow {z : ℂ} {β : ℝ} (hβ : 0 ≤ β) (hβ2 : β ≤ 2)
    (hz : 0 ≤ z.im) :
    Real.cos (β * Real.pi / 2) * ‖z ^ (β : ℂ)‖ ≤
      (exp ((-(β * Real.pi / 2) : ℝ) * Complex.I) * z ^ (β : ℂ)).re := by
  rw [norm_cpow_real]
  refine cos_mul_norm_rpow_le_re_exp_mul_cpow (abs_le.mpr ⟨?_, ?_⟩) (by nlinarith [Real.pi_pos])
  · nlinarith [arg_nonneg_iff.mpr hz]
  · nlinarith [arg_le_pi z]

/-- For `|y| ≤ 1`, the principal power `z ^ y` has real part at least `cos (y π) ‖z‖ ^ y`: the
phase `arg z * y` of the cosine formula for its real part has modulus at most `|y| π ≤ π`. -/
theorem cos_mul_norm_rpow_le_re_cpow {z : ℂ} {y : ℝ} (hy : |y| ≤ 1) :
    Real.cos (y * Real.pi) * ‖z‖ ^ y ≤ (z ^ (y : ℂ)).re := by
  have h := cos_mul_norm_rpow_le_re_exp_mul_cpow (z := z) (φ := 0) (δ := |y| * Real.pi)
    (by
      rw [sub_zero, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (abs_arg_le_pi z) (abs_nonneg y))
    (by nlinarith [Real.pi_pos])
  rw [← abs_of_pos Real.pi_pos, ← abs_mul, Real.cos_abs] at h
  simpa using h

end TauCeti

end
