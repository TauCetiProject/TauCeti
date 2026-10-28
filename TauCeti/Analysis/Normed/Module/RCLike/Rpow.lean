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
of a finite family when estimating `ℓᵖ` sums.
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

end TauCeti
