/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Iterated derivatives of a scalar function times a constant vector

The iterated derivatives of `y ↦ f y • v`, for a scalar function `f` and a fixed vector `v`, are
those of `f` composed with `t ↦ t • v` (Mathlib's `iteratedFDeriv_smul_const_apply`). This file
records the resulting norm bound `‖Dⁱ (f • v)‖ ≤ ‖Dⁱ f‖ ‖v‖`, which bounds the derivatives of a
vector field one coordinate at a time.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `i`-th derivative of a scalar function times a constant vector `v` is bounded by the
`i`-th derivative of the function times `‖v‖`. -/
theorem norm_iteratedFDeriv_smul_const_le {f : E → 𝕜} {i : ℕ} {x : E} (hf : ContDiffAt 𝕜 i f x)
    (v : F) : ‖iteratedFDeriv 𝕜 i (fun y ↦ f y • v) x‖ ≤ ‖iteratedFDeriv 𝕜 i f x‖ * ‖v‖ := by
  rw [iteratedFDeriv_smul_const_apply hf]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact (mul_le_of_le_one_left (norm_nonneg v) ContinuousLinearMap.norm_id_le)

end TauCeti
