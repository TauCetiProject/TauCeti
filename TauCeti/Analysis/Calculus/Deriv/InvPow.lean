/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Derivatives of inverse natural powers

Away from the origin, `y ↦ y⁻¹ ^ k` has derivative `-k x⁻¹ ^ (k + 1)` at `x`
(`TauCeti.hasDerivAt_inv_pow`). This is Mathlib's chain rule for `(y⁻¹) ^ k` with the derivative
written as a single inverse power, the form in which iterated derivatives of `t⁻¹ ^ k` stay in
the span of inverse powers.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- For `x ≠ 0`, the derivative of `y ↦ y⁻¹ ^ k` at `x` is `-k x⁻¹ ^ (k + 1)`. -/
theorem hasDerivAt_inv_pow (k : ℕ) {x : 𝕜} (hx : x ≠ 0) :
    HasDerivAt (fun y : 𝕜 => y⁻¹ ^ k) (-(k : 𝕜) * x⁻¹ ^ (k + 1)) x := by
  convert (hasDerivAt_inv hx).fun_pow k using 1
  rcases k with - | k
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [← inv_pow]
    ring

end TauCeti
