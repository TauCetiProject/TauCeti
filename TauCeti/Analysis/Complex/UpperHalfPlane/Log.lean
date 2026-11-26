/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# The logarithm maps the upper half-plane onto a strip

The principal logarithm is a holomorphic bijection from the open upper half-plane
onto the horizontal strip with imaginary part between `0` and `π`. Its inverse is
complex exponentiation. This supplies the logarithmic coordinate for parallel-sided
conformal ends.

The rescaled exponential `z ↦ exp (π z) + a` is the corresponding coordinate on the strip
`0 < z.im < 1` of height `1`: it maps the open strip onto the upper half-plane, the closed strip
onto the closed upper half-plane with `a` removed, the two boundary lines onto the real line with
`a` removed, and the negative and positive ends of the strip to `a` and to infinity.
-/

public section

open Bornology Complex Filter Function Set Topology UpperHalfPlane
open scoped Real

namespace TauCeti

/-- The principal logarithm maps the upper half-plane bijectively onto the open
horizontal strip of height `π`. -/
theorem bijOn_log_upperHalfPlaneSet :
    BijOn Complex.log upperHalfPlaneSet {w : ℂ | w.im ∈ Ioo 0 Real.pi} := by
  refine InvOn.bijOn ⟨fun z hz => exp_log (ne_of_apply_ne Complex.im hz.ne'),
    fun w hw => log_exp ((neg_neg_of_pos Real.pi_pos).trans hw.1) hw.2.le⟩
    (fun z hz => ?_) fun w hw => ?_
  · rw [mem_ofPred_eq, log_im]
    exact ⟨(arg_nonneg_iff.mpr hz.le).lt_of_ne fun h => hz.ne' (arg_eq_zero_iff.mp h.symm).2,
      arg_lt_pi_iff.mpr (.inr hz.ne')⟩
  · simpa only [upperHalfPlaneSet, mem_ofPred_eq, exp_im] using
      mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hw.1 hw.2)

/-! ### The exponential coordinate of the strip of height `1` -/

/-- The map `w ↦ log (w - a) / π` inverts `z ↦ exp (π z) + a` between the closed strip and the
closed upper half-plane with `a` removed. -/
theorem invOn_log_sub_div_pi_exp_pi_mul_add (a : ℝ) :
    InvOn (fun w : ℂ => log (w - a) / π) (fun z : ℂ => cexp (π * z) + a)
      {z : ℂ | z.im ∈ Icc 0 1} ({w : ℂ | 0 ≤ w.im} \ {(a : ℂ)}) := by
  refine ⟨fun z hz => ?_, fun w hw => ?_⟩
  · have him : (π * z : ℂ).im = π * z.im := by simp
    have hz₁ : -π < (π * z : ℂ).im := by
      rw [him]; nlinarith [Real.pi_pos, hz.1]
    have hz₂ : (π * z : ℂ).im ≤ π := by
      rw [him]; nlinarith [Real.pi_pos, hz.2]
    simp only [add_sub_cancel_right, log_exp hz₁ hz₂]
    field_simp
  · have hw : w - a ≠ 0 := sub_ne_zero.mpr hw.2
    simp only
    rw [mul_div_cancel₀ _ (ofReal_ne_zero.mpr Real.pi_ne_zero), exp_log hw, sub_add_cancel]

/-- The inverse pair of `invOn_log_sub_div_pi_exp_pi_mul_add` restricted to the open strip and the
open upper half-plane. -/
theorem invOn_log_sub_div_pi_exp_pi_mul_add_strip (a : ℝ) :
    InvOn (fun w : ℂ => log (w - a) / π) (fun z : ℂ => cexp (π * z) + a)
      {z : ℂ | z.im ∈ Ioo 0 1} upperHalfPlaneSet :=
  (invOn_log_sub_div_pi_exp_pi_mul_add a).mono (fun z hz => Ioo_subset_Icc_self hz)
    fun w (hw : 0 < w.im) => ⟨hw.le, fun h => by
      rw [mem_singleton_iff] at h
      simp [h] at hw⟩

/-- `exp (π z) + a` maps the open strip of height `1` bijectively onto the upper half-plane. -/
theorem bijOn_exp_pi_mul_add_strip (a : ℝ) :
    BijOn (fun z : ℂ => cexp (π * z) + a) {z : ℂ | z.im ∈ Ioo 0 1} upperHalfPlaneSet := by
  refine (invOn_log_sub_div_pi_exp_pi_mul_add_strip a).bijOn
    (fun z hz => ?_) fun w (hw : 0 < w.im) => ?_
  · change 0 < (cexp (π * z) + a).im
    rw [add_im, ofReal_im, add_zero, exp_im]
    refine mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) <;>
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] <;>
      nlinarith [Real.pi_pos, hz.1, hz.2]
  · have harg : 0 < arg (w - a) ∧ arg (w - a) < π := by
      have hw' : 0 < (w - a).im := by simpa using hw
      exact ⟨(arg_nonneg_iff.mpr hw'.le).lt_of_ne fun h => hw'.ne' (arg_eq_zero_iff.mp h.symm).2,
        arg_lt_pi_iff.mpr (.inr hw'.ne')⟩
    simp only [mem_ofPred_eq, div_ofReal_im, log_im, mem_Ioo]
    exact ⟨div_pos harg.1 Real.pi_pos, (div_lt_one Real.pi_pos).mpr harg.2⟩

/-- `exp (π z) + a` maps the closed strip of height `1` bijectively onto the closed upper
half-plane with `a` removed. -/
theorem bijOn_exp_pi_mul_add_closedStrip (a : ℝ) :
    BijOn (fun z : ℂ => cexp (π * z) + a) {z : ℂ | z.im ∈ Icc 0 1}
      ({w : ℂ | 0 ≤ w.im} \ {(a : ℂ)}) := by
  refine (invOn_log_sub_div_pi_exp_pi_mul_add a).bijOn (fun z hz => ⟨?_, ?_⟩) fun w hw => ?_
  · change 0 ≤ (cexp (π * z) + a).im
    rw [add_im, ofReal_im, add_zero, exp_im]
    refine mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_) <;>
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero] <;>
      nlinarith [Real.pi_pos, hz.1, hz.2]
  · simp
  · have hw' : 0 ≤ (w - a).im := by simpa using hw.1
    simp only [mem_ofPred_eq, div_ofReal_im, log_im, mem_Icc]
    exact ⟨div_nonneg (arg_nonneg_iff.mpr hw') Real.pi_pos.le,
      (div_le_one Real.pi_pos).mpr (arg_le_pi _)⟩

/-- `exp (π z) + a` maps the two boundary lines of the strip of height `1` bijectively onto the
real line with `a` removed: the lower line onto the points to the right of `a`, the upper line
onto those to its left. -/
theorem bijOn_exp_pi_mul_add_strip_boundary (a : ℝ) :
    BijOn (fun z : ℂ => cexp (π * z) + a) {z : ℂ | z.im = 0 ∨ z.im = 1}
      ({w : ℂ | w.im = 0} \ {(a : ℂ)}) := by
  have hsub : {z : ℂ | z.im = 0 ∨ z.im = 1} ⊆ {z : ℂ | z.im ∈ Icc 0 1} := fun z hz =>
    hz.elim (fun h => by simp [h]) fun h => by simp [h]
  have hsub' : {w : ℂ | w.im = 0} \ {(a : ℂ)} ⊆ {w : ℂ | 0 ≤ w.im} \ {(a : ℂ)} :=
    fun w hw => ⟨le_of_eq (Eq.symm hw.1), hw.2⟩
  refine ((invOn_log_sub_div_pi_exp_pi_mul_add a).mono hsub hsub').bijOn
    (fun z hz => ⟨?_, ?_⟩) fun w hw => ?_
  · change (cexp (π * z) + a).im = 0
    rw [add_im, ofReal_im, add_zero, exp_im]
    rcases hz with h | h <;> simp [h]
  · simp
  · have him : (w - a).im = 0 := by simpa using hw.1
    have hne : w - a ≠ 0 := sub_ne_zero.mpr hw.2
    simp only [mem_ofPred_eq, div_ofReal_im, log_im]
    rcases lt_or_gt_of_ne (fun h : (w - a).re = 0 => hne (Complex.ext h him)) with h | h
    · exact .inr (by rw [arg_eq_pi_iff.mpr ⟨h, him⟩, div_self Real.pi_ne_zero])
    · exact .inl (by rw [arg_eq_zero_iff.mpr ⟨h.le, him⟩, zero_div])

/-- `exp (π z) + a` tends to `a` at the negative end of the strip. -/
theorem tendsto_exp_pi_mul_add_comap_re_atBot (a : ℝ) :
    Tendsto (fun z : ℂ => cexp (π * z) + a) (comap re atBot) (𝓝 a) := by
  have h : Tendsto (fun z : ℂ => (π : ℂ) * z) (comap re atBot) (comap re atBot) :=
    tendsto_comap_iff.mpr (by
      simpa [comp_def] using tendsto_comap.const_mul_atBot Real.pi_pos)
  simpa using (tendsto_exp_comap_re_atBot.comp h).add_const (a : ℂ)

/-- `exp (π z) + a` tends to infinity at the positive end of the strip. -/
theorem tendsto_exp_pi_mul_add_comap_re_atTop (a : ℝ) :
    Tendsto (fun z : ℂ => cexp (π * z) + a) (comap re atTop) (cobounded ℂ) := by
  have h : Tendsto (fun z : ℂ => (π : ℂ) * z) (comap re atTop) (comap re atTop) :=
    tendsto_comap_iff.mpr (by
      simpa [comp_def] using tendsto_comap.const_mul_atTop Real.pi_pos)
  exact (tendsto_add_const_cobounded (a : ℂ)).comp (tendsto_exp_comap_re_atTop.comp h)

end TauCeti
