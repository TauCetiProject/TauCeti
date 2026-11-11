/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment

/-!
# Open segments between real points of `ℂ`

The open segment of `ℂ` joining two real points is the image of the corresponding open segment
of `ℝ`. This file records its description in coordinates.

## Main results

* `Complex.mem_openSegment_ofReal`: `w ∈ openSegment ℝ (a : ℂ) b` exactly when `w` is real with
  `re w ∈ openSegment ℝ a b`.
* `Complex.mem_openSegment_zero_one`: `w ∈ openSegment ℝ 0 1` exactly when `w` is real
  with `0 < re w < 1`.
-/

public section

namespace Complex

/-- A point of `ℂ` lies on the open segment joining two real points exactly when it is real and
its real part lies on the open segment joining them in `ℝ`. -/
@[simp]
theorem mem_openSegment_ofReal {w : ℂ} {a b : ℝ} :
    w ∈ openSegment ℝ (a : ℂ) b ↔ w.im = 0 ∧ w.re ∈ openSegment ℝ a b := by
  simp only [openSegment, Set.mem_ofPred_eq, Complex.ext_iff]
  grind [add_re, add_im, real_smul, mul_re, mul_im, ofReal_re, ofReal_im, smul_eq_mul]

/-- A point of `ℂ` lies on the open segment from `0` to `1` exactly when it is real and strictly
between `0` and `1`. -/
@[simp]
theorem mem_openSegment_zero_one {w : ℂ} :
    w ∈ openSegment ℝ (0 : ℂ) 1 ↔ w.im = 0 ∧ 0 < w.re ∧ w.re < 1 := by
  simpa [openSegment_eq_Ioo] using mem_openSegment_ofReal (w := w) (a := 0) (b := 1)

end Complex
