/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Affine bijections of horizontal strips

Positive real scalings and complex translations map horizontal strips bijectively
onto the strips whose endpoints undergo the corresponding real affine map. These
maps rescale logarithmic strip coordinates to arbitrary boundary heights.
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

end TauCeti
