/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Normalizing two real points by an affine map

This file defines the unique positive affine normalization carrying two ordered real points to
`0` and `1` and records its elementary order properties.

## Main definitions

* `TauCeti.affineNormalize` -- the map carrying `x` to `0` and `y` to `1`.

## Main results

* `TauCeti.affineNormalize_left`, `TauCeti.affineNormalize_right` -- its endpoint values.
* `TauCeti.strictMono_affineNormalize` -- the normalization preserves strict order when `x < y`.
* `TauCeti.exists_affine_eq_zero_one` -- its expression as a positive affine change.
-/

public section

noncomputable section

namespace TauCeti

/-- The affine normalization that sends `x` to `0` and `y` to `1`. -/
def affineNormalize (x y z : ℝ) : ℝ := (z - x) / (y - x)

/-- The left endpoint is sent to `0`. -/
@[simp]
theorem affineNormalize_left (x y : ℝ) : affineNormalize x y x = 0 := by
  simp [affineNormalize]

/-- The right endpoint is sent to `1` when the endpoints are distinct. -/
@[simp]
theorem affineNormalize_right {x y : ℝ} (hxy : x ≠ y) : affineNormalize x y y = 1 := by
  rw [affineNormalize, div_self (sub_ne_zero.mpr hxy.symm)]

/-- The affine normalization of two ordered real points is strictly increasing. -/
theorem strictMono_affineNormalize {x y : ℝ} (hxy : x < y) :
    StrictMono (affineNormalize x y) := by
  intro s t hst
  exact div_lt_div_of_pos_right (sub_lt_sub_right hst x) (sub_pos.mpr hxy)

/-- Two ordered real points can be normalized to `0` and `1` by a positive affine change. -/
theorem exists_affine_eq_zero_one {x y : ℝ} (hxy : x < y) :
    ∃ c > 0, ∃ d, c * x + d = 0 ∧ c * y + d = 1 := by
  let c := (y - x)⁻¹
  refine ⟨c, inv_pos.mpr (sub_pos.mpr hxy), -c * x, by simp, ?_⟩
  calc
    c * y + -c * x = c * (y - x) := by rw [mul_sub, sub_eq_add_neg, neg_mul]
    _ = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr hxy.ne')

end TauCeti

end
