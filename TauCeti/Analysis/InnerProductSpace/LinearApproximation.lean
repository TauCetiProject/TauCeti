/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Inner products along a linear approximation

If a vector `y'` follows the linear expansion `y + A (z - x)` up to `ε * ‖z - x‖`, and `z` lies on
the segment `x + t • h`, then pairing with `h` gives `⟪h, y'⟫ = ⟪h, y⟫ + t * ⟪h, A h⟫` up to
`ε * ‖h‖ ^ 2`.

## Main results

* `TauCeti.abs_inner_sub_inner_sub_mul_le`: the bound on the pairing with `h`.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Along the segment `x + t • h`, a vector `y'` which follows the expansion
`y + A (z - x)` up to `ε * ‖z - x‖` satisfies `⟪h, y'⟫ = ⟪h, y⟫ + t * ⟪h, A h⟫` up to
`ε * ‖h‖ ^ 2`. -/
theorem abs_inner_sub_inner_sub_mul_le {z x y y' h : E} {A : E →ₗ[ℝ] E} {t ε : ℝ}
    (hε : 0 ≤ ε) (hz : z - x = t • h) (hzh : ‖z - x‖ ≤ ‖h‖)
    (hb : ‖y' - y - A (z - x)‖ ≤ ε * ‖z - x‖) :
    |⟪h, y'⟫_ℝ - ⟪h, y⟫_ℝ - t * ⟪h, A h⟫_ℝ| ≤ ε * ‖h‖ ^ 2 := by
  have : ⟪h, y'⟫_ℝ - ⟪h, y⟫_ℝ - t * ⟪h, A h⟫_ℝ = ⟪h, y' - y - A (z - x)⟫_ℝ := by
    rw [hz, map_smul, inner_sub_right, inner_sub_right, real_inner_smul_right]
  rw [this]
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖h‖ * ‖y' - y - A (z - x)‖ ≤ ‖h‖ * (ε * ‖h‖) :=
        mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hzh hε)) (norm_nonneg h)
    _ = ε * ‖h‖ ^ 2 := by ring

end TauCeti
