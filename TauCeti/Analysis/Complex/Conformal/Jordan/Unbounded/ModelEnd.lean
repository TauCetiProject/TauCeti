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

## Main results

* `TauCeti.isPreconnectedAtInfinityIn_halfStrip`: a half-strip is preconnected at infinity.
* `TauCeti.isPreconnectedAtInfinityIn_sector`: the far part of a sector is preconnected at
  infinity.
* `TauCeti.isPreconnectedAtInfinityIn_halfStripExterior`: the far part of the exterior of a closed
  half-strip is preconnected at infinity.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Metric Set

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

end TauCeti
