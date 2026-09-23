/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Normalizing two real points by an affine map

This file records that the inverse of Mathlib's `affineHomeomorph` gives a positive affine
normalization carrying two ordered real points to `0` and `1`.

## Main results

* `TauCeti.exists_affine_eq_zero_one` -- two ordered points admit a positive affine
  normalization.
-/

public section

noncomputable section

namespace TauCeti

/-- Two ordered real points can be normalized to `0` and `1` by a positive affine change. -/
theorem exists_affine_eq_zero_one {x y : ℝ} (hxy : x < y) :
    ∃ c > 0, ∃ d, c * x + d = 0 ∧ c * y + d = 1 := by
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.ne'
  let f := affineHomeomorph (y - x) x hne
  have hf (z : ℝ) : (y - x)⁻¹ * z + -(y - x)⁻¹ * x = f.symm z := by
    simp [f, affineHomeomorph_symm_apply, div_eq_mul_inv]
    ring
  have hx : f.symm x = 0 := by
    simp [f]
  have hy : f.symm y = 1 := by
    simpa [f, affineHomeomorph_apply] using f.symm_apply_apply (1 : ℝ)
  exact ⟨(y - x)⁻¹, inv_pos.mpr (sub_pos.mpr hxy), -(y - x)⁻¹ * x,
    (hf x).trans hx, (hf y).trans hy⟩

end TauCeti

end
