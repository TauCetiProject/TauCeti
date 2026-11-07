/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Complex.Convex

/-!
# Affine bijections of horizontal strips

Positive real scalings and complex translations map horizontal strips bijectively
onto the strips whose endpoints undergo the corresponding real affine map. These
maps rescale logarithmic strip coordinates to arbitrary boundary heights.

A set far to the right that is confined to a strip, and whose preconnected pieces avoiding the
two boundary heights lie inside it or outside its closure, has the regions above and below the
strip outside its closure.
-/

public section

namespace TauCeti

open Complex Set

/-- A positive real scaling followed by a complex translation maps a horizontal strip
bijectively onto the strip with the transformed imaginary endpoints. -/
theorem bijOn_ofReal_mul_add_horizontalStrip {s : ℝ} (hs : 0 < s) (c : ℂ) (l h : ℝ) :
    BijOn (fun w : ℂ => (s : ℂ) * w + c)
      {w : ℂ | w.im ∈ Ioo l h} {w : ℂ | w.im ∈ Ioo (s * l + c.im) (s * h + c.im)} := by
  have him (w : ℂ) : ((s : ℂ) * w + c).im = s * w.im + c.im := by simp
  have himage := Set.image_affine_Ioo hs c.im l h
  refine ⟨fun w hw => ?_, fun w _ v _ hwv => ?_, fun v hv => ?_⟩
  · rw [mem_ofPred_eq, him, ← himage]
    exact mem_image_of_mem _ hw
  · exact mul_left_cancel₀ (ofReal_ne_zero.mpr hs.ne') (add_right_cancel hwv)
  · rw [← himage] at hv
    obtain ⟨y, hy, hyv⟩ := hv
    refine ⟨⟨(v.re - c.re) / s, y⟩, hy, ?_⟩
    apply Complex.ext
    · simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      rw [mul_div_cancel₀ _ hs.ne', sub_add_cancel]
    · simpa only [him] using hyv

/-- If the set `U` is confined to a strip of width `π + 2` far to the right, and preconnected sets
far to the right that avoid the two boundary heights lie wholly inside or wholly outside the
closure of `U`, then the regions below and above the strip are outside the closure of `U`. -/
theorem outer_regions_subset_compl_closure {U : Set ℂ} {c : ℂ} {R R₂ : ℝ} (hR : R₂ ≤ R)
    (hdichotomy : ∀ s : Set ℂ, IsPreconnected s →
      (∀ w ∈ s, R < w.re ∧ w.im ≠ c.im ∧ w.im ≠ c.im + Real.pi) → s ⊆ U ∨ s ⊆ (closure U)ᶜ)
    (hbounds : ∀ w ∈ U, R₂ < w.re → c.im - 1 < w.im ∧ w.im < c.im + Real.pi + 1) :
    {w : ℂ | R < w.re ∧ w.im < c.im} ⊆ (closure U)ᶜ ∧
      {w : ℂ | R < w.re ∧ c.im + Real.pi < w.im} ⊆ (closure U)ᶜ := by
  have hout (b : ℝ) (s : Set ℂ) (hs : IsPreconnected s)
      (havoid : ∀ w ∈ s, R < w.re ∧ w.im ≠ c.im ∧ w.im ≠ c.im + Real.pi)
      (hb : b < c.im - 1 ∨ c.im + Real.pi + 1 < b)
      (hmem : (R + 1 : ℂ) + (b : ℂ) * I ∈ s) : s ⊆ (closure U)ᶜ := by
    refine (hdichotomy s hs havoid).resolve_left fun h => ?_
    have hwR : R₂ < ((R + 1 : ℂ) + (b : ℂ) * I).re := by
      simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, one_re]
      exact hR.trans_lt (lt_add_one R)
    have h := hbounds _ (h hmem) hwR
    simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add, one_im] at h
    rcases hb with hb | hb <;> linarith
  refine ⟨?_, ?_⟩
  · apply hout (c.im - 2) _ ((convex_halfSpace_re_gt R).inter
      (convex_halfSpace_im_lt c.im)).isPreconnected
    · intro w hw
      exact ⟨hw.1, ne_of_lt hw.2,
        ne_of_lt (hw.2.trans (lt_add_of_pos_right _ Real.pi_pos))⟩
    · left; linarith
    · simp
  · apply hout (c.im + Real.pi + 2) _ ((convex_halfSpace_re_gt R).inter
      (convex_halfSpace_im_gt (c.im + Real.pi))).isPreconnected
    · intro w hw
      exact ⟨hw.1, ne_of_gt ((lt_add_of_pos_right _ Real.pi_pos).trans hw.2), ne_of_gt hw.2⟩
    · right; linarith
    · simp

end TauCeti
