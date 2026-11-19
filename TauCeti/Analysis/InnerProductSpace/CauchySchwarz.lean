/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Norm bounds from a quadratic lower bound by an inner product

In an inner product space over `𝕜 = ℝ` or `ℂ`, a bound `c ‖x‖² ≤ re ⟪g, x⟫` gives
`c ‖x‖ ≤ ‖g‖`: bound the right side by `‖g‖ ‖x‖` with the Cauchy–Schwarz inequality and cancel
one factor `‖x‖`. This is the last step of an energy estimate, where testing an equation against
the solution itself bounds `c ‖x‖²` by the pairing of `x` with the data `g`.

## Main declarations

* `TauCeti.mul_norm_le_norm_of_mul_norm_sq_le_re_inner`: the bound above.
-/

public section

namespace TauCeti

open RCLike
open scoped InnerProductSpace

variable {𝕜 F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Cauchy–Schwarz turns the bound `c ‖x‖² ≤ re ⟪g, x⟫` into `c ‖x‖ ≤ ‖g‖`. -/
theorem mul_norm_le_norm_of_mul_norm_sq_le_re_inner {c : ℝ} {g x : F}
    (h : c * ‖x‖ ^ 2 ≤ re ⟪g, x⟫_𝕜) : c * ‖x‖ ≤ ‖g‖ := by
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact norm_nonneg g
  · exact le_of_mul_le_mul_right (by nlinarith [re_inner_le_norm (𝕜 := 𝕜) g x]) hpos

end TauCeti
