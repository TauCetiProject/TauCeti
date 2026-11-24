/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pairing a vector with its extremal vector

The extremal vector `‖x‖ ^ (r - 2) • x` of the `Lʳ` norm pairs with `x` to give `‖x‖ ^ r`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]

/-- For `r ≠ 0`, pairing a vector with its extremal vector `‖x‖ ^ (r - 2) • x` gives `‖x‖ ^ r`. -/
theorem inner_ofReal_rpow_sub_two_smul {V : Type*} [SeminormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] {r : ℝ} (hr : r ≠ 0) (x : V) :
    ⟪x, ((‖x‖ ^ (r - 2) : ℝ) : 𝕜) • x⟫_𝕜 = ((‖x‖ ^ r : ℝ) : 𝕜) := by
  -- This also holds when `‖x‖ = 0`: there both sides vanish, as `r ≠ 0`.
  have hpow : ‖x‖ ^ (r - 2) * ‖x‖ ^ 2 = ‖x‖ ^ r := by
    rw [← Real.rpow_two, ← Real.rpow_add' (norm_nonneg x) (by simpa using hr), sub_add_cancel]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, ← hpow, RCLike.ofReal_mul, RCLike.ofReal_pow]

end TauCeti
