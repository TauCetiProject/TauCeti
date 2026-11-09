/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Rescaling a vector by a real root

For `a ≥ 0` and `q ≠ 0`, scaling a vector `v` in a normed space over `𝕜 = ℝ` or `ℂ` by the real
scalar `a ^ (1 / q)` multiplies `‖v‖ ^ q` by `a`. This is how weights are absorbed into the points
of a finite family when estimating `ℓᵖ` sums. The extremal vector `‖x‖ ^ (r - 2) • x` of the
`Lʳ` norm has norm at most `‖x‖ ^ (r - 1)`.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Scaling `v` by the real scalar `a ^ q⁻¹`, for `a ≥ 0` and `q ≠ 0`, multiplies `‖v‖ ^ q`
by `a`. -/
theorem norm_ofReal_rpow_inv_smul_rpow {a q : ℝ} (ha : 0 ≤ a) (hq : q ≠ 0) (v : E) :
    ‖((a ^ q⁻¹ : ℝ) : 𝕜) • v‖ ^ q = a * ‖v‖ ^ q := by
  rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg ha _),
    Real.mul_rpow (Real.rpow_nonneg ha _) (norm_nonneg _), Real.rpow_inv_rpow ha hq]

/-- The extremal vector `‖x‖ ^ (r - 2) • x` of the `Lʳ` norm has norm at most `‖x‖ ^ (r - 1)`. -/
theorem norm_ofReal_rpow_sub_two_smul_le {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (r : ℝ) (x : V) : ‖((‖x‖ ^ (r - 2) : ℝ) : 𝕜) • x‖ ≤ ‖x‖ ^ (r - 1) := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp [Real.rpow_nonneg]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.2 h0
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      show r - 1 = (r - 2) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]

end TauCeti
