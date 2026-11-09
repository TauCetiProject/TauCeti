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

/-- Pairing a vector with its extremal vector `‖x‖ ^ (r - 2) • x` gives `‖x‖ ^ r`. -/
theorem inner_ofReal_rpow_sub_two_smul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    {r : ℝ} (hr : r ≠ 0) (x : V) :
    ⟪x, ((‖x‖ ^ (r - 2) : ℝ) : 𝕜) • x⟫_𝕜 = ((‖x‖ ^ r : ℝ) : 𝕜) := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp [Real.zero_rpow hr]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.2 h0
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
    conv_rhs => rw [show r = (r - 2) + 2 by ring, Real.rpow_add hpos, Real.rpow_two]
    push_cast
    ring_nf

end TauCeti
