/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A horizontal step, rotated

Rotating a horizontal step `x ≤ y` of the complex plane by `exp (-θ * I)` changes the height by
the step length times `sin (-θ)`.

## Main results

* `Complex.im_exp_neg_mul_sub_sub_eq_of_le`: the height of the rotated step.
-/

public section

open scoped ComplexOrder

namespace Complex

/-- **A horizontal step, rotated by `-θ`, has height `r * sin (-θ)`.**  If `x ≤ y` in the order on
`ℂ` (same imaginary part, real part not larger), then after multiplying by `exp (-θ * I)` the
difference of heights is the length `r = (y - x).re ≥ 0` times `sin (-θ)`. -/
lemma im_exp_neg_mul_sub_sub_eq_of_le (θ : ℝ) (w : ℂ) {x y : ℂ} (hxy : x ≤ y) :
    ∃ r, 0 ≤ r ∧ (Complex.exp (-θ * Complex.I) * (y - w)).im -
      (Complex.exp (-θ * Complex.I) * (x - w)).im = r * Real.sin (-θ) := by
  refine ⟨(y - x).re, sub_nonneg.mpr (Complex.le_def.mp hxy).1, ?_⟩
  have hu : (Complex.exp (-θ * Complex.I)).im = Real.sin (-θ) := by
    have h := Complex.exp_ofReal_mul_I_im (-θ)
    push_cast at h
    exact h
  rw [← Complex.sub_im, ← mul_sub, sub_sub_sub_cancel_right, Complex.mul_im, Complex.sub_im,
    (Complex.le_def.mp hxy).2, sub_self, mul_zero, zero_add, hu, mul_comm]

end Complex
