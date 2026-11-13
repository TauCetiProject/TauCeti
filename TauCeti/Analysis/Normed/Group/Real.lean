/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Real

/-!
# Norms of real numbers

`Real.enorm_sq_eq_ofReal_sq` converts a squared extended norm into the nonnegative
real square embedded in `ℝ≥0∞`, for use in lower-integral energy identities.
`Filter.Eventually.norm_inv_le_inv` bounds the reciprocal of a real function that is eventually
bounded below by a positive constant.
-/

public section

open scoped ENNReal

namespace Real

/-- The squared extended norm of a real number is its square embedded in `ℝ≥0∞`. -/
theorem enorm_sq_eq_ofReal_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

end Real

namespace Filter.Eventually

/-- If `λ ≤ a` eventually along a filter, with `λ > 0`, then `‖a⁻¹‖ ≤ λ⁻¹` eventually. -/
theorem norm_inv_le_inv {α : Type*} {l : Filter α} {a : α → ℝ} {lam : ℝ}
    (ha : ∀ᶠ t in l, lam ≤ a t) (hlam : 0 < lam) : ∀ᶠ t in l, ‖(a t)⁻¹‖ ≤ lam⁻¹ :=
  ha.mono fun t ht => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hlam.trans_le ht)]
    exact inv_anti₀ hlam ht

end Filter.Eventually
