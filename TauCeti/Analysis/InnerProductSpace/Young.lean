/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Young's inequality for inner products

In an inner product space over `𝕜 = ℝ` or `ℂ`, for every weight `ε > 0`,

`2 re ⟪x, y⟫ ≤ ε ‖x‖² + ε⁻¹ ‖y‖²`.

This is the inner-product form of Mathlib's weighted Young inequality `two_mul_le_add_mul_sq`,
obtained from it through the Cauchy-Schwarz inequality `re ⟪x, y⟫ ≤ ‖x‖ ‖y‖`. It is the form used
to absorb a cross term into a positive quadratic term, as in energy estimates for elliptic
equations with first-order terms.

## Main declarations

* `TauCeti.two_mul_re_inner_le_add_mul_norm_sq`: the weighted Young inequality above.
* `TauCeti.two_mul_re_inner_le_of_norm_le_mul_add_norm`: if `‖b‖ ≤ β (1 + ‖x‖)`, then
  `2 re ⟪x, b⟫ ≤ 3 β (1 + ‖x‖²)`, the cross-term bound for a vector field with linear growth.
-/

public section

namespace TauCeti

open RCLike
open scoped InnerProductSpace

variable {𝕜 F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Young's inequality for inner products**: for every weight `ε > 0`,
`2 re ⟪x, y⟫ ≤ ε ‖x‖² + ε⁻¹ ‖y‖²`. -/
theorem two_mul_re_inner_le_add_mul_norm_sq (x y : F) {ε : ℝ} (hε : 0 < ε) :
    2 * re ⟪x, y⟫_𝕜 ≤ ε * ‖x‖ ^ 2 + ε⁻¹ * ‖y‖ ^ 2 :=
  (mul_le_mul_of_nonneg_left (re_inner_le_norm x y) zero_le_two).trans <| by
    simpa only [mul_assoc] using two_mul_le_add_mul_sq hε

/-- **The cross term of a vector field with linear growth**: if `‖b‖ ≤ β (1 + ‖x‖)`, then
`2 re ⟪x, b⟫ ≤ 3 β (1 + ‖x‖²)`. This follows from the Cauchy-Schwarz inequality and the unweighted
Young inequality `2 ‖x‖ ≤ 1 + ‖x‖²`; it bounds the drift term of `1 + ‖x‖²` in Lyapunov and
barrier arguments. -/
theorem two_mul_re_inner_le_of_norm_le_mul_add_norm {x b : F} {β : ℝ}
    (hb : ‖b‖ ≤ β * (1 + ‖x‖)) : 2 * re ⟪x, b⟫_𝕜 ≤ 3 * β * (1 + ‖x‖ ^ 2) := by
  have hβ : 0 ≤ β := nonneg_of_mul_nonneg_left ((norm_nonneg b).trans hb) (by positivity)
  have h := (re_inner_le_norm (𝕜 := 𝕜) x b).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg x))
  nlinarith [mul_le_mul_of_nonneg_left (two_mul_le_add_sq ‖x‖ 1) hβ, mul_nonneg hβ (sq_nonneg ‖x‖)]

end TauCeti
