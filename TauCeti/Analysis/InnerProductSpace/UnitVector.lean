/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Coefficients against a unit vector

For a unit vector `ξ` in an inner product space over `ℝ` or `ℂ`, the coefficient `⟪ξ, x⟫` lies
within `‖x - ξ‖` of `1 = ⟪ξ, ξ⟫`. For instance, a matrix coefficient `g ↦ ⟪ξ, ρ g ξ⟫` of a unitary
representation is close to `1` wherever `ρ g` moves `ξ` little.

## Main results

* `TauCeti.norm_inner_sub_one_le`: `‖⟪ξ, x⟫ - 1‖ ≤ ‖x - ξ‖` for a unit vector `ξ`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a unit vector `ξ`, the coefficient `⟪ξ, x⟫` lies within `‖x - ξ‖` of `1`. -/
theorem norm_inner_sub_one_le {ξ : E} (hξ : ‖ξ‖ = 1) (x : E) : ‖⟪ξ, x⟫_𝕜 - 1‖ ≤ ‖x - ξ‖ := by
  rw [← inner_self_eq_one_of_norm_eq_one hξ, ← inner_sub_right]
  simpa [hξ] using norm_inner_le_norm (𝕜 := 𝕜) ξ (x - ξ)

end TauCeti
