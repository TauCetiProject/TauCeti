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

end TauCeti
