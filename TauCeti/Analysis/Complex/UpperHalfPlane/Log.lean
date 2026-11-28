/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Bornology.BoundedOperation
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

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

Conversely, for real `p < q` the coordinate `w ↦ log ((w - q) / (w - p)) / π` is a holomorphic
bijection of the upper half-plane onto that strip. It sends the real points `q` and `p` to the
negative and positive ends of the strip, and is continuous at every real point `r ∉ [p, q]`, which
it sends to the point `log ((r - q) / (r - p)) / π` of the lower boundary line.
-/

public section

open Bornology Complex Filter Function Set Topology UpperHalfPlane
open scoped Real

namespace TauCeti

/-- The open upper half-plane lies in the closed one. -/
theorem upperHalfPlaneSet_subset_im_nonneg : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} :=
  ofPred_subset_ofPred.mpr fun _ => le_of_lt

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

/-- The imaginary part of `exp (π z) + a` for real `a`. -/
theorem exp_pi_mul_add_im (a : ℝ) (z : ℂ) :
    (cexp (π * z) + a).im = Real.exp (π * z.re) * Real.sin (π * z.im) := by
  simp [exp_im]

/-- The imaginary part of `log (w - a) / π` for real `a`. -/
theorem log_sub_div_pi_im (a : ℝ) (w : ℂ) : (log (w - a) / π).im = arg (w - a) / π := by
  rw [div_ofReal_im, log_im]

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
  · rw [mem_ofPred_eq, exp_pi_mul_add_im]
    refine mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) <;>
      nlinarith [Real.pi_pos, hz.1, hz.2]
  · have harg : 0 < arg (w - a) ∧ arg (w - a) < π := by
      have hw' : 0 < (w - a).im := by simpa using hw
      exact ⟨(arg_nonneg_iff.mpr hw'.le).lt_of_ne fun h => hw'.ne' (arg_eq_zero_iff.mp h.symm).2,
        arg_lt_pi_iff.mpr (.inr hw'.ne')⟩
    simp only [mem_ofPred_eq, log_sub_div_pi_im, mem_Ioo]
    exact ⟨div_pos harg.1 Real.pi_pos, (div_lt_one Real.pi_pos).mpr harg.2⟩

/-- `exp (π z) + a` maps the closed strip of height `1` bijectively onto the closed upper
half-plane with `a` removed. -/
theorem bijOn_exp_pi_mul_add_closedStrip (a : ℝ) :
    BijOn (fun z : ℂ => cexp (π * z) + a) {z : ℂ | z.im ∈ Icc 0 1}
      ({w : ℂ | 0 ≤ w.im} \ {(a : ℂ)}) := by
  refine (invOn_log_sub_div_pi_exp_pi_mul_add a).bijOn (fun z hz => ⟨?_, ?_⟩) fun w hw => ?_
  · rw [mem_ofPred_eq, exp_pi_mul_add_im]
    refine mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_) <;>
      nlinarith [Real.pi_pos, hz.1, hz.2]
  · simp
  · have hw' : 0 ≤ (w - a).im := by simpa using hw.1
    simp only [mem_ofPred_eq, log_sub_div_pi_im, mem_Icc]
    exact ⟨div_nonneg (arg_nonneg_iff.mpr hw') Real.pi_pos.le,
      (div_le_one Real.pi_pos).mpr (arg_le_pi _)⟩

/-- `exp (π z) + a` maps the union of the two boundary lines of the strip of height `1`
bijectively onto the real line with `a` removed. -/
theorem bijOn_exp_pi_mul_add_strip_boundary (a : ℝ) :
    BijOn (fun z : ℂ => cexp (π * z) + a) {z : ℂ | z.im = 0 ∨ z.im = 1}
      ({w : ℂ | w.im = 0} \ {(a : ℂ)}) := by
  have hsub : {z : ℂ | z.im = 0 ∨ z.im = 1} ⊆ {z : ℂ | z.im ∈ Icc 0 1} := fun z hz =>
    hz.elim (fun h => by simp [h]) fun h => by simp [h]
  have hsub' : {w : ℂ | w.im = 0} \ {(a : ℂ)} ⊆ {w : ℂ | 0 ≤ w.im} \ {(a : ℂ)} :=
    fun w hw => ⟨le_of_eq (Eq.symm hw.1), hw.2⟩
  refine ((invOn_log_sub_div_pi_exp_pi_mul_add a).mono hsub hsub').bijOn
    (fun z hz => ⟨?_, ?_⟩) fun w hw => ?_
  · rw [mem_ofPred_eq, exp_pi_mul_add_im]
    rcases hz with h | h <;> simp [h]
  · simp
  · have him : (w - a).im = 0 := by simpa using hw.1
    have hne : w - a ≠ 0 := sub_ne_zero.mpr hw.2
    simp only [mem_ofPred_eq, log_sub_div_pi_im]
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

/-! ### A logarithmic coordinate of the upper half-plane -/

/-- For `p < q`, the coordinate `w ↦ log ((w - q) / (w - p)) / π` maps the upper half-plane
bijectively onto the open strip of height `1`. -/
theorem bijOn_log_sub_div_sub_div_pi {p q : ℝ} (hpq : p < q) :
    BijOn (fun w : ℂ => log ((w - q) / (w - p)) / π) upperHalfPlaneSet
      {z : ℂ | z.im ∈ Ioo 0 1} := by
  have hL : BijOn (fun w : ℂ => log w / π) upperHalfPlaneSet {z : ℂ | z.im ∈ Ioo 0 1} := by
    simpa using
      (bijOn_exp_pi_mul_add_strip 0).symm (invOn_log_sub_div_pi_exp_pi_mul_add_strip 0).symm
  exact hL.comp (bijOn_sub_div_sub_upperHalfPlaneSet hpq)

/-- For `p < q`, the coordinate `w ↦ log ((w - q) / (w - p)) / π` is holomorphic on the upper
half-plane. -/
theorem differentiableOn_log_sub_div_sub_div_pi {p q : ℝ} (hpq : p < q) :
    DifferentiableOn ℂ (fun w : ℂ => log ((w - q) / (w - p)) / π) upperHalfPlaneSet := by
  intro w hw
  have hm := (bijOn_sub_div_sub_upperHalfPlaneSet hpq).mapsTo hw
  rw [mem_ofPred_eq] at hm
  have hd : DifferentiableAt ℂ (fun w : ℂ => (w - q) / (w - p)) w := by
    fun_prop (disch := exact sub_ofReal_ne_zero_of_mem_upperHalfPlaneSet hw p)
  exact ((hd.clog (mem_slitPlane_iff.mpr (.inr hm.ne'))).div_const _).differentiableWithinAt

/-- For `p < q`, the coordinate `w ↦ log ((w - q) / (w - p)) / π` tends to the negative end of the
strip at the real point `q`. -/
theorem tendsto_log_sub_div_sub_div_pi_comap_re_atBot {p q : ℝ} (hpq : p < q) :
    Tendsto (fun w : ℂ => log ((w - q) / (w - p)) / π) (𝓝[upperHalfPlaneSet] q)
      (comap re atBot ⊓ 𝓟 {z : ℂ | z.im ∈ Ioo 0 1}) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr
    (eventually_nhdsWithin_of_forall fun w hw => (bijOn_log_sub_div_sub_div_pi hpq).mapsTo hw)⟩
  have hm : Tendsto (fun w : ℂ => (w - q) / (w - p)) (𝓝 (q : ℂ)) (𝓝 0) := by
    have : ContinuousAt (fun w : ℂ => (w - q) / (w - p)) q :=
      (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr (ofReal_injective.ne hpq.ne'))
    simpa using this.tendsto
  have hnorm : Tendsto (fun w : ℂ => ‖(w - q) / (w - p)‖) (𝓝[upperHalfPlaneSet] q) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using (hm.mono_left nhdsWithin_le_nhds).norm,
      eventually_nhdsWithin_of_forall fun w hw => norm_pos_iff.mpr
        (div_ne_zero (sub_ofReal_ne_zero_of_mem_upperHalfPlaneSet hw q)
          (sub_ofReal_ne_zero_of_mem_upperHalfPlaneSet hw p))⟩
  simpa [comp_def, div_ofReal_re, log_re] using
    (Real.tendsto_log_nhdsGT_zero.comp hnorm).atBot_div_const Real.pi_pos

/-- For `p < q`, the coordinate `w ↦ log ((w - q) / (w - p)) / π` tends to the positive end of the
strip at the real point `p`. -/
theorem tendsto_log_sub_div_sub_div_pi_comap_re_atTop {p q : ℝ} (hpq : p < q) :
    Tendsto (fun w : ℂ => log ((w - q) / (w - p)) / π) (𝓝[upperHalfPlaneSet] p)
      (comap re atTop ⊓ 𝓟 {z : ℂ | z.im ∈ Ioo 0 1}) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr
    (eventually_nhdsWithin_of_forall fun w hw => (bijOn_log_sub_div_sub_div_pi hpq).mapsTo hw)⟩
  have hnum : Tendsto (fun w : ℂ => ‖w - q‖) (𝓝[upperHalfPlaneSet] p) (𝓝 ‖(p : ℂ) - q‖) :=
    ((continuous_sub_right (q : ℂ)).norm.tendsto _).mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun w : ℂ => ‖w - p‖) (𝓝[upperHalfPlaneSet] p) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa using
      ((continuous_sub_right (p : ℂ)).norm.tendsto (p : ℂ)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun w hw =>
        norm_pos_iff.mpr (sub_ofReal_ne_zero_of_mem_upperHalfPlaneSet hw p)⟩
  have hnorm : Tendsto (fun w : ℂ => ‖(w - q) / (w - p)‖) (𝓝[upperHalfPlaneSet] p) atTop :=
    (hnum.pos_mul_atTop (norm_pos_iff.mpr (sub_ne_zero.mpr (ofReal_injective.ne hpq.ne)))
      (tendsto_inv_nhdsGT_zero.comp hden)).congr fun w => by
        rw [comp_apply, norm_div, div_eq_mul_inv]
  simpa [comp_def, div_ofReal_re, log_re] using
    (Real.tendsto_log_atTop.comp hnorm).atTop_div_const Real.pi_pos

/-- For `p < q` and a real point `r` outside `[p, q]`, the coordinate
`w ↦ log ((w - q) / (w - p)) / π` tends to the point `log ((r - q) / (r - p)) / π` of the lower
boundary line of the strip at `r`. -/
theorem tendsto_log_sub_div_sub_div_pi_of_notMem_Icc {p q r : ℝ} (hpq : p < q)
    (hr : r ∉ Icc p q) :
    Tendsto (fun w : ℂ => log ((w - q) / (w - p)) / π) (𝓝[upperHalfPlaneSet] r)
      (𝓝[{z : ℂ | z.im ∈ Ioo 0 1}] ((Real.log ((r - q) / (r - p)) / π : ℝ) : ℂ)) := by
  have hpos : 0 < (r - q) / (r - p) := by
    rcases not_and_or.mp hr with h | h
    · exact div_pos_of_neg_of_neg (by linarith [not_le.mp h]) (by linarith [not_le.mp h])
    · exact div_pos (by linarith [not_le.mp h]) (by linarith [not_le.mp h])
  have hrp : r - p ≠ 0 := fun h => by simp [h] at hpos
  have hval : ((r : ℂ) - q) / ((r : ℂ) - p) = (((r - q) / (r - p) : ℝ) : ℂ) := by push_cast; ring
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
    (bijOn_log_sub_div_sub_div_pi hpq).mapsTo hw⟩
  have hc : ContinuousAt (fun w : ℂ => log ((w - q) / (w - p)) / π) r := by
    refine (ContinuousAt.clog ?_ ?_).div_const _
    · exact (continuousAt_id.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const)
        (by exact_mod_cast hrp)
    · rw [hval]
      exact ofReal_mem_slitPlane.mpr hpos
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := upperHalfPlaneSet))
  rwa [hval, ← ofReal_log hpos.le, ← ofReal_div] at this

end TauCeti
