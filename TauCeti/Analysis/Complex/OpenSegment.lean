/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment

/-!
# The open segment from `0` to `1` in `ℂ`

Mathlib's `openSegment ℝ 0 1` in `ℂ` is the image of the open real interval `(0, 1)`. This file
records its description in coordinates: the real points strictly between `0` and `1`.

## Main results

* `TauCeti.Complex.mem_openSegment_zero_one`: `w ∈ openSegment ℝ 0 1` exactly when `w` is real
  with `0 < re w < 1`.
-/

public section

namespace TauCeti.Complex

/-- A point of `ℂ` lies on the open segment from `0` to `1` exactly when it is real and strictly
between `0` and `1`. -/
@[simp]
theorem mem_openSegment_zero_one {w : ℂ} :
    w ∈ openSegment ℝ (0 : ℂ) 1 ↔ w.im = 0 ∧ 0 < w.re ∧ w.re < 1 := by
  rw [openSegment_eq_image]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    simp [h0, h1]
  · rintro ⟨him, h0, h1⟩
    refine ⟨w.re, ⟨h0, h1⟩, _root_.Complex.ext ?_ ?_⟩ <;> simp [him]

end TauCeti.Complex
