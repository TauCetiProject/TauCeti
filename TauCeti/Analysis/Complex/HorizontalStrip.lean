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
      {w : ℂ | w.im ∈ Ioo l h} {w : ℂ | w.im ∈ Ioo (s * l + c.im) (s * h + c.im)} :=
  ((Equiv.mulLeft₀ (s : ℂ) (ofReal_ne_zero.mpr hs.ne')).trans (Equiv.addRight c)).bijOn
    fun w => by simp [hs]

end TauCeti
