/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Topology.Connected.AtInfinity

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import TauCeti.Analysis.Normed.Group.Basic

/-!
# The model ends of a polygonal domain are preconnected at infinity

Far out, a polygonal domain decomposes into ends of three kinds: half-strips between two parallel
sides, sectors between two rays, and exteriors of half-strips (ends of opening `2 * π`).  In the
normalized coordinate `z = (w - c) / b`, with `b ≠ 0`, they are

* the half-strip `{ρ < re z, 0 < im z < π}`,
* the sector `{ρ < ‖w - c‖, |arg z| < α}`,
* the half-strip exterior `{ρ < ‖w - c‖, re z < 0 ∨ im z ∉ [0, π]}`.

This file shows that each of them is preconnected at infinity inside itself, in the sense of
`TauCeti.IsPreconnectedAtInfinityIn`.  An end contained in the image `U` of a conformal map is then
preconnected at infinity inside `U` by `TauCeti.IsPreconnectedAtInfinityIn.mono`, which is the
hypothesis under which distinct boundary zeros of an inverted coordinate lie in distinct ends
(`TauCeti.eq_of_eventually_mem_of_inverted_coordinate_eq_zero`).

The far parts of all three kinds of ends are also open and unbounded. A finite disjoint
family covering a domain far out can be replaced by such open far parts.

## Main results

* `TauCeti.isPreconnectedAtInfinityIn_halfStrip`: a half-strip is preconnected at infinity.
* `TauCeti.isPreconnectedAtInfinityIn_sector`: the far part of a sector is preconnected at
  infinity.
* `TauCeti.isPreconnectedAtInfinityIn_halfStripExterior`: the far part of the exterior of a closed
  half-strip is preconnected at infinity.

* `TauCeti.exists_far_ends`: replace a finite family of model ends by open,
  unbounded far parts that remain disjoint, preconnected at infinity and cover the domain far out.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology

namespace TauCeti

/-- The model half-strip `{ρ < re z, 0 < im z < π}` is preconnected at infinity. -/
private theorem isPreconnectedAtInfinityIn_halfStrip_zero_one (ρ : ℝ) :
    IsPreconnectedAtInfinityIn {z : ℂ | ρ < z.re ∧ z.im ∈ Ioo 0 Real.pi}
      {z : ℂ | ρ < z.re ∧ z.im ∈ Ioo 0 Real.pi} := by
  refine isPreconnectedAtInfinityIn_iff.2 fun B hB => ?_
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall 0).1 hB
  refine ⟨{z : ℂ | max ρ R < z.re ∧ z.im ∈ Ioo 0 Real.pi},
    fun z hz => ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩,
    ((convex_halfSpace_re_gt _).inter
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))).isPreconnected, ?_, ?_⟩
  · refine disjoint_left.2 fun z hz hzB => ?_
    have := mem_closedBall_zero_iff.1 (hR hzB)
    linarith [le_max_right ρ R, re_le_norm z, hz.1]
  · -- far out, the bounded imaginary part forces a large real part
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop (|ρ| + |R| + Real.pi)]
      with z hz hzE
    obtain ⟨hρ, him₀, himπ⟩ := hzE
    have hre : |ρ| + |R| < |z.re| := by
      linarith [norm_le_abs_re_add_abs_im z, abs_of_pos him₀]
    refine ⟨max_lt hρ ?_, him₀, himπ⟩
    rcases abs_cases z.re with ⟨h, -⟩ | ⟨h, -⟩ <;>
      linarith [le_abs_self R, neg_abs_le ρ, abs_nonneg ρ, abs_nonneg R]

/-- **A half-strip is preconnected at infinity.**  For `b ≠ 0`, the half-strip
`{w | ρ < re ((w - c) / b), 0 < im ((w - c) / b) < π}` is preconnected at infinity inside
itself. -/
theorem isPreconnectedAtInfinityIn_halfStrip (ρ : ℝ) {c b : ℂ} (hb : b ≠ 0) :
    IsPreconnectedAtInfinityIn
      {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi}
      {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} :=
  (isPreconnectedAtInfinityIn_halfStrip_zero_one ρ).preimage_div_sub hb

/-- The far part `{r < ‖z‖, |arg z| < α}` of the model sector is preconnected at infinity. -/
private theorem isPreconnectedAtInfinityIn_sector_zero_one (r α : ℝ) :
    IsPreconnectedAtInfinityIn {z : ℂ | r < ‖z‖ ∧ |z.arg| < α}
      {z : ℂ | r < ‖z‖ ∧ |z.arg| < α} := by
  refine isPreconnectedAtInfinityIn_iff.2 fun B hB => ?_
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall 0).1 hB
  -- the far part of the sector is the image of a convex set of polar coordinates
  set polar : ℝ × ℝ → ℂ := fun p => p.1 * (cos p.2 + sin p.2 * I)
  have hpolar : ∀ p : ℝ × ℝ, 0 < p.1 → p.2 ∈ Ioc (-Real.pi) Real.pi →
      ‖polar p‖ = p.1 ∧ (polar p).arg = p.2 := fun p hp hθ => by
    refine ⟨?_, arg_mul_cos_add_sin_mul_I hp hθ⟩
    simp [polar, norm_cos_add_sin_mul_I, abs_of_pos hp]
  refine ⟨polar '' (Ioi (|r| + |R|) ×ˢ (Ioc (-Real.pi) Real.pi ∩ Ioo (-α) α)), ?_,
    ((convex_Ioi _).prod ((convex_Ioc _ _).inter (convex_Ioo _ _))).isPreconnected.image _
      (by fun_prop), ?_, ?_⟩
  · rintro _ ⟨p, ⟨hp, hθ, hθα⟩, rfl⟩
    have hp0 : 0 < p.1 := lt_of_le_of_lt (by positivity) hp
    obtain ⟨hn, ha⟩ := hpolar p hp0 hθ
    refine ⟨?_, ?_⟩
    · rw [hn]
      linarith [le_abs_self r, abs_nonneg R, mem_Ioi.1 hp]
    · rw [ha]
      exact abs_lt.2 hθα
  · refine disjoint_left.2 ?_
    rintro _ ⟨p, ⟨hp, hθ, -⟩, rfl⟩ hpB
    have hp0 : 0 < p.1 := lt_of_le_of_lt (by positivity) hp
    have := mem_closedBall_zero_iff.1 (hR hpB)
    rw [(hpolar p hp0 hθ).1] at this
    linarith [le_abs_self R, abs_nonneg r, mem_Ioi.1 hp]
  · filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop (|r| + |R|)]
      with z hz hzE
    exact ⟨(‖z‖, z.arg), ⟨hz, arg_mem_Ioc z, abs_lt.1 hzE.2⟩, norm_mul_cos_add_sin_mul_I z⟩

/-- **A sector is preconnected at infinity.**  For `b ≠ 0`, the far part
`{w | ρ < ‖w - c‖, |arg ((w - c) / b)| < α}` of the sector of half-opening `α` with vertex `c` and
axis direction `b` is preconnected at infinity inside itself.  No restriction on `α` is needed: for
`α > π` this is the exterior of a disc. -/
theorem isPreconnectedAtInfinityIn_sector (ρ α : ℝ) {c b : ℂ} (hb : b ≠ 0) :
    IsPreconnectedAtInfinityIn {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < α}
      {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < α} := by
  have hset : {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < α} =
      (fun w => (w - c) / b) ⁻¹' {z : ℂ | ρ / ‖b‖ < ‖z‖ ∧ |z.arg| < α} := by
    ext w
    simp [div_lt_div_iff_of_pos_right (norm_pos_iff.2 hb)]
  rw [hset]
  exact (isPreconnectedAtInfinityIn_sector_zero_one _ α).preimage_div_sub hb

/-- The far part `{r < ‖z‖, re z < 0 ∨ im z ∉ [0, π]}` of the exterior of the model closed
half-strip is preconnected at infinity. -/
private theorem isPreconnectedAtInfinityIn_halfStripExterior_zero_one (r : ℝ) :
    IsPreconnectedAtInfinityIn {z : ℂ | r < ‖z‖ ∧ (z.re < 0 ∨ z.im ∉ Icc 0 Real.pi)}
      {z : ℂ | r < ‖z‖ ∧ (z.re < 0 ∨ z.im ∉ Icc 0 Real.pi)} := by
  refine isPreconnectedAtInfinityIn_iff.2 fun B hB => ?_
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall 0).1 hB
  obtain ⟨M, hMπ, hrM, hRM⟩ : ∃ M, Real.pi ≤ M ∧ r ≤ M ∧ R ≤ M :=
    ⟨|r| + |R| + Real.pi, by linarith [abs_nonneg r, abs_nonneg R],
      by linarith [le_abs_self r, abs_nonneg R, Real.pi_pos],
      by linarith [le_abs_self R, abs_nonneg r, Real.pi_pos]⟩
  have hM : 0 < M := Real.pi_pos.trans_le hMπ
  -- far out, the exterior is a chain of five overlapping convex pieces around the half-strip
  let C : Set ℂ := {z | M < z.re ∧ Real.pi < z.im} ∪ {z | M < z.im} ∪ {z | z.re < -M} ∪
    {z | z.im < -M} ∪ {z | M < z.re ∧ z.im < 0}
  have hCM : ∀ z ∈ C, M < ‖z‖ ∧ (z.re < 0 ∨ z.im ∉ Icc 0 Real.pi) := by
    intro z hz
    simp only [C, mem_union, mem_ofPred_eq] at hz
    rcases hz with (((⟨h₁, h₂⟩ | h) | h) | h) | ⟨h₁, h₂⟩
    · exact ⟨h₁.trans_le (re_le_norm z), .inr fun h => h₂.not_ge h.2⟩
    · exact ⟨h.trans_le (im_le_norm z), .inr fun h' => (hMπ.trans_lt h).not_ge h'.2⟩
    · exact ⟨by linarith [neg_abs_le z.re, abs_re_le_norm z], .inl (by linarith)⟩
    · exact ⟨by linarith [neg_abs_le z.im, abs_im_le_norm z], .inr fun h' => by linarith [h'.1]⟩
    · exact ⟨h₁.trans_le (re_le_norm z), .inr fun h => h₂.not_ge h.1⟩
  refine ⟨C, fun z hz => ⟨hrM.trans_lt (hCM z hz).1, (hCM z hz).2⟩, ?_, ?_, ?_⟩
  · have h₁ := ((convex_halfSpace_re_gt M).inter
      (convex_halfSpace_im_gt Real.pi)).isPreconnected.union (⟨M + 1, M + 1⟩ : ℂ)
      (by simp; linarith) (by simp) (convex_halfSpace_im_gt M).isPreconnected
    have h₂ := h₁.union (⟨-(M + 1), M + 1⟩ : ℂ) (by simp) (by simp)
      (convex_halfSpace_re_lt (-M)).isPreconnected
    have h₃ := h₂.union (⟨-(M + 1), -(M + 1)⟩ : ℂ) (by simp) (by simp)
      (convex_halfSpace_im_lt (-M)).isPreconnected
    exact h₃.union (⟨M + 1, -(M + 1)⟩ : ℂ) (by simp) (by simp; linarith)
      ((convex_halfSpace_re_gt M).inter (convex_halfSpace_im_lt 0)).isPreconnected
  · refine disjoint_left.2 fun z hz hzB => ?_
    have := mem_closedBall_zero_iff.1 (hR hzB)
    linarith [(hCM z hz).1]
  · -- far out, a point leaves the box `|re|, |im| ≤ M`, and off the half-strip it lies in a piece
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop (2 * M)] with z hz hzE
    have hsum := norm_le_abs_re_add_abs_im z
    rcases lt_or_ge M z.im with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    rcases lt_or_ge z.im (-M) with h' | h'
    · exact Or.inl (Or.inr h')
    rcases lt_or_ge z.re (-M) with h'' | h''
    · exact Or.inl (Or.inl (Or.inr h''))
    have hre : M < z.re := by
      rcases abs_cases z.re with ⟨hr, -⟩ | ⟨hr, -⟩ <;>
        rcases abs_cases z.im with ⟨hi, -⟩ | ⟨hi, -⟩ <;> linarith
    rcases hzE.2 with hz' | hz'
    · linarith
    rcases lt_or_ge z.im 0 with h₀ | h₀
    · exact Or.inr ⟨hre, h₀⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hre, lt_of_not_ge fun hπ => hz' ⟨h₀, hπ⟩⟩)))

/-- **The exterior of a half-strip is preconnected at infinity.**  For `b ≠ 0`, the far part
`{w | ρ < ‖w - c‖, re ((w - c) / b) < 0 ∨ im ((w - c) / b) ∉ [0, π]}` of the exterior of a closed
half-strip, an end of opening `2 * π`, is preconnected at infinity inside itself. -/
theorem isPreconnectedAtInfinityIn_halfStripExterior (ρ : ℝ) {c b : ℂ} (hb : b ≠ 0) :
    IsPreconnectedAtInfinityIn
      {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)}
      {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} := by
  have hset : {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} =
      (fun w => (w - c) / b) ⁻¹'
        {z : ℂ | ρ / ‖b‖ < ‖z‖ ∧ (z.re < 0 ∨ z.im ∉ Icc 0 Real.pi)} := by
    ext w
    simp only [mem_ofPred_eq, mem_preimage, norm_div,
      div_lt_div_iff_of_pos_right (norm_pos_iff.2 hb)]
  rw [hset]
  exact (isPreconnectedAtInfinityIn_halfStripExterior_zero_one _).preimage_div_sub hb

/-- A sector of nonnegative radius is open. -/
theorem isOpen_sector {ρ α : ℝ} {c b : ℂ} (hρ : 0 ≤ ρ) :
    IsOpen {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < α} := by
  have hnorm : Continuous fun w : ℂ => ‖w - c‖ := by fun_prop
  -- With `b = 0` or half-opening above `π`, the angular condition does not depend on `w`.
  rcases eq_or_ne b 0 with rfl | hb
  · by_cases hα : 0 < α <;> simp [hα, isOpen_lt continuous_const hnorm]
  rcases lt_or_ge Real.pi α with hα | hα
  · simpa [(abs_arg_le_pi _).trans_lt hα] using isOpen_lt continuous_const hnorm
  have hdiv : Continuous fun w : ℂ => (w - c) / b := by fun_prop
  refine isOpen_iff_mem_nhds.mpr fun w hw => ?_
  -- Off the centre, the argument is continuous inside the sector, including half-opening `π`.
  have hne : (w - c) / b ≠ 0 := div_ne_zero (norm_pos_iff.mp (hρ.trans_lt hw.1)) hb
  have hslit : (w - c) / b ∈ slitPlane := by
    refine mem_slitPlane_iff_arg.mpr ⟨fun h => ?_, hne⟩
    have := hw.2
    rw [h, abs_of_pos Real.pi_pos] at this
    exact (this.trans_le hα).false
  have harg : ContinuousAt (fun y : ℂ => |((y - c) / b).arg|) w :=
    continuous_abs.continuousAt.comp
      ((continuousAt_arg hslit).comp (f := fun y : ℂ => (y - c) / b) hdiv.continuousAt)
  filter_upwards [continuousAt_const.eventually_lt hnorm.continuousAt hw.1,
    harg.eventually_lt continuousAt_const hw.2] with y h₁ h₂ using ⟨h₁, h₂⟩

/-- The half-strip in an affine coordinate is open. -/
theorem isOpen_halfStrip (ρ : ℝ) (c b : ℂ) :
    IsOpen {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} := by
  have hre : Continuous fun w : ℂ => ((w - c) / b).re := by fun_prop
  have him : Continuous fun w : ℂ => ((w - c) / b).im := by fun_prop
  exact (isOpen_lt continuous_const hre).inter (isOpen_Ioo.preimage him)

/-- A sector of positive half-opening is unbounded. -/
theorem not_isBounded_sector {ρ α : ℝ} {c b : ℂ} (hα : 0 < α) :
    ¬IsBounded {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < α} := by
  rcases eq_or_ne b 0 with rfl | hb
  · -- with `b = 0` the angular condition is vacuous
    convert not_isBounded_inter_lt_norm_sub (NormedSpace.unbounded_univ ℝ ℂ) c ρ using 2
    ext w
    simp [hα]
  intro hE
  obtain ⟨M, hM⟩ := hE.subset_closedBall c
  let t := (|M| + |ρ| + 1) / ‖b‖
  have ht : 0 < t := by dsimp [t]; positivity
  have hbt : ‖b‖ * t = |M| + |ρ| + 1 :=
    mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hb)
  have hn : ‖c + b * t - c‖ = ‖b‖ * t := by
    simp [abs_of_pos ht]
  have hmem : c + b * t ∈ {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < α} := by
    refine ⟨?_, ?_⟩
    · rw [hn, hbt]; linarith [le_abs_self ρ, abs_nonneg M]
    · simpa [mul_div_cancel_left₀ _ hb, arg_ofReal_of_nonneg ht.le] using hα
  have := mem_closedBall_iff_norm.mp (hM hmem)
  rw [hn, hbt] at this
  linarith [le_abs_self M, abs_nonneg ρ]

/-- A half-strip in a nondegenerate affine coordinate is unbounded. -/
theorem not_isBounded_halfStrip {ρ : ℝ} {c b : ℂ} (hb : b ≠ 0) :
    ¬IsBounded {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} := fun hE => by
  obtain ⟨M, hM⟩ := hE.subset_closedBall c
  let t := (|M| + 1) / ‖b‖ + |ρ| + 1
  have ht : ρ < t := by
    have : 0 ≤ (|M| + 1) / ‖b‖ := by positivity
    dsimp [t]
    linarith [le_abs_self ρ]
  have hbt : |M| + 1 ≤ ‖b‖ * t := by
    have := mul_div_cancel₀ (|M| + 1) (norm_ne_zero_iff.mpr hb)
    dsimp [t]
    nlinarith [norm_nonneg b, abs_nonneg ρ]
  let ζ : ℂ := t + Real.pi / 2 * Complex.I
  have hn : ‖b‖ * t ≤ ‖c + b * ζ - c‖ := by
    simp only [add_sub_cancel_left, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa [ζ] using re_le_norm ζ) (norm_nonneg b)
  have hmem : c + b * ζ ∈
      {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} := by
    simpa [mul_div_cancel_left₀ _ hb, ζ] using
      And.intro ht (And.intro (by linarith [Real.pi_pos] : 0 < Real.pi / 2)
        (by linarith [Real.pi_pos] : Real.pi / 2 < Real.pi))
  have := mem_closedBall_iff_norm.mp (hM hmem)
  linarith [le_abs_self M]

/-- The far part of the exterior of a closed half-strip is open. -/
theorem isOpen_halfStripExterior (ρ : ℝ) (c b : ℂ) :
    IsOpen {w : ℂ | ρ < ‖w - c‖ ∧
      (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} := by
  have hre : Continuous fun w : ℂ => ((w - c) / b).re := by fun_prop
  have him : Continuous fun w : ℂ => ((w - c) / b).im := by fun_prop
  have hnorm : Continuous fun w : ℂ => ‖w - c‖ := by fun_prop
  exact (isOpen_lt continuous_const hnorm).inter
    ((isOpen_lt hre continuous_const).union (isClosed_Icc.preimage him).isOpen_compl)

/-- The far part of the exterior of a half-strip in a nondegenerate affine coordinate is
unbounded. -/
theorem not_isBounded_halfStripExterior {ρ : ℝ} {c b : ℂ} (hb : b ≠ 0) :
    ¬IsBounded {w : ℂ | ρ < ‖w - c‖ ∧
      (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} := by
  -- A half-strip pointing in the opposite direction lies in the exterior.
  intro hE
  apply not_isBounded_inter_lt_norm_sub
    (not_isBounded_halfStrip (ρ := 0) (c := c) (neg_ne_zero.mpr hb)) c ρ
  refine hE.subset fun w hw => ⟨hw.2, Or.inl ?_⟩
  simpa only [div_neg, neg_re, neg_pos] using hw.1.1

/-- **Open far parts of the ends.**  For finitely many pairwise disjoint sector ends of positive
half-opening, half-strip ends or half-strip-exterior ends contained in `U` and covering it far out,
their far parts are open, unbounded, pairwise disjoint and preconnected at infinity inside `U`, and
still cover `U` far out. -/
theorem exists_far_ends {κ : Type*} [Finite κ] {α : κ → ℝ} {U : Set ℂ}
    {E : κ → Set ℂ} {c b : κ → ℂ} {ρ : κ → ℝ} {R : ℝ} (hb : ∀ k, b k ≠ 0)
    (hE : ∀ k, (0 < α k ∧
        E k = {w : ℂ | ρ k < ‖w - c k‖ ∧ |((w - c k) / b k).arg| < α k}) ∨
      E k = {w : ℂ | ρ k < ((w - c k) / b k).re ∧ ((w - c k) / b k).im ∈ Ioo 0 Real.pi} ∨
      E k = {w : ℂ | ρ k < ‖w - c k‖ ∧
        (((w - c k) / b k).re < 0 ∨ ((w - c k) / b k).im ∉ Icc 0 Real.pi)})
    (hEU : ∀ k, E k ⊆ U) (hUE : ∀ w ∈ U, R < ‖w‖ → ∃ k, w ∈ E k)
    (hEd : Pairwise (Disjoint on E)) :
    ∃ E' : κ → Set ℂ, ∃ R' : ℝ, (∀ k, IsOpen (E' k)) ∧ (∀ k, E' k ⊆ E k) ∧
      Pairwise (Disjoint on E') ∧ (∀ w ∈ U, R' < ‖w‖ → ∃ k, w ∈ E' k) ∧
      (∀ k, IsPreconnectedAtInfinityIn U (E' k)) ∧ ∀ k, ¬IsBounded (E' k) := by
  have := Fintype.ofFinite κ
  refine ⟨fun k => E k ∩ {w : ℂ | max (ρ k) 0 < ‖w - c k‖},
    max R (∑ k, (max (ρ k) 0 + ‖c k‖)),
    fun k => ?_,
    fun k => inter_subset_left,
    fun k l hkl => (hEd hkl).mono inter_subset_left inter_subset_left, fun w hw hRw => ?_,
    fun k => ?_, fun k => ?_⟩
  · dsimp only
    rcases hE k with ⟨-, hEk⟩ | hEk | hEk <;> rw [hEk]
    · -- the far part of the sector is the sector of radius `max (ρ k) 0`
      have hset :
          {w : ℂ | ρ k < ‖w - c k‖ ∧ |((w - c k) / b k).arg| < α k} ∩
            {w : ℂ | max (ρ k) 0 < ‖w - c k‖} =
          {w : ℂ | max (ρ k) 0 < ‖w - c k‖ ∧ |((w - c k) / b k).arg| < α k} := by
        ext w
        simp only [mem_inter_iff, mem_ofPred_eq, max_lt_iff]
        tauto
      rw [hset]
      exact isOpen_sector (le_max_right (ρ k) 0)
    · exact (isOpen_halfStrip (ρ k) (c k) (b k)).inter (isOpen_lt continuous_const (by fun_prop))
    · exact (isOpen_halfStripExterior (ρ k) (c k) (b k)).inter
        (isOpen_lt continuous_const (by fun_prop))
  · -- far from `0`, a point is far from every centre
    obtain ⟨k, hk⟩ := hUE w hw ((le_max_left _ _).trans_lt hRw)
    have hck : max (ρ k) 0 + ‖c k‖ ≤ ∑ l, (max (ρ l) 0 + ‖c l‖) :=
      Finset.single_le_sum (f := fun l => max (ρ l) 0 + ‖c l‖)
        (fun l _ => add_nonneg (le_max_right _ _) (norm_nonneg _)) (Finset.mem_univ k)
    refine ⟨k, hk, ?_⟩
    have := norm_sub_norm_le w (c k)
    have := le_max_right R (∑ l, (max (ρ l) 0 + ‖c l‖))
    exact (by linarith : max (ρ k) 0 < ‖w - c k‖)
  · rcases hE k with ⟨-, hEk⟩ | hEk | hEk
    · exact ((isPreconnectedAtInfinityIn_sector (ρ k) _ (hb k)).mono (hEk ▸ hEU k)).subset
        (hEk ▸ inter_subset_left)
    · exact ((isPreconnectedAtInfinityIn_halfStrip (ρ k) (hb k)).mono (hEk ▸ hEU k)).subset
        (hEk ▸ inter_subset_left)
    · exact ((isPreconnectedAtInfinityIn_halfStripExterior (ρ k) (hb k)).mono
        (hEk ▸ hEU k)).subset (hEk ▸ inter_subset_left)
  · dsimp only
    rcases hE k with ⟨hα, hEk⟩ | hEk | hEk <;> rw [hEk]
    · exact not_isBounded_inter_lt_norm_sub (not_isBounded_sector hα) _ _
    · exact not_isBounded_inter_lt_norm_sub (not_isBounded_halfStrip (hb k)) _ _
    · exact not_isBounded_inter_lt_norm_sub (not_isBounded_halfStripExterior (hb k)) _ _

end TauCeti
