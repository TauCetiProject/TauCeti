/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Differences of squared distances to real points

For two real points `c₁`, `c₂` of the complex plane, the difference of the two power functions
`|z - c|² - |C - c|²` is affine in the real part of `z` and vanishes when `z.re = C.re`
(`Complex.normSq_sub_ofReal_sub_normSq_sub_ofReal`): the radical axis of two circles centred on
the real line is the vertical line through their intersection points.

## Main results

* `Complex.normSq_sub_ofReal_sub_normSq_sub_ofReal`: the radical-line identity.
-/

public section

namespace Complex

/-- The "radical line" identity: for real centres `c₁` and `c₂`, the difference of the two power
functions `|z - c|² - |C - c|²` of `z` is affine in `z.re` and vanishes at `C.re`. -/
theorem normSq_sub_ofReal_sub_normSq_sub_ofReal {c₁ c₂ : ℝ} (C z : ℂ) :
    (Complex.normSq (z - c₁) - Complex.normSq (C - c₁)) -
        (Complex.normSq (z - c₂) - Complex.normSq (C - c₂)) =
      2 * (c₂ - c₁) * (z.re - C.re) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero]
  ring

end Complex
