/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-!
# Normalizing two ordered-field points by an affine map

This file records that a positive affine map carries two ordered points in a linearly ordered
field to `0` and `1`.

## Main results

* `TauCeti.exists_affine_eq_zero_one` -- two ordered points admit a positive affine
  normalization.
-/

public section

noncomputable section

namespace TauCeti

/-- Two ordered points in a linearly ordered field can be normalized to `0` and `1` by a positive
affine change. -/
theorem exists_affine_eq_zero_one {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x y : K} (hxy : x < y) :
    ∃ c > 0, ∃ d, c * x + d = 0 ∧ c * y + d = 1 := by
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  refine ⟨(y - x)⁻¹, inv_pos.mpr (sub_pos.mpr hxy), -(y - x)⁻¹ * x, ?_, ?_⟩
  · rw [neg_mul, add_neg_cancel]
  · rw [neg_mul, ← sub_eq_add_neg, ← mul_sub, inv_mul_cancel₀ hne]

end TauCeti

end
