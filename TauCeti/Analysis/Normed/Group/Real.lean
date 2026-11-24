/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Basic.Sign.Defs

/-!
# Norms of real numbers

`Real.enorm_sq_eq_ofReal_sq` converts a squared extended norm into the nonnegative
real square embedded in `ℝ≥0∞`, for use in lower-integral energy identities, and
`Real.coe_nnNorm_sq` and `Real.nnNorm_sq` write a squared nonnegative norm as the square, in `ℝ`
and in `ℝ≥0`.
`SignType.norm_coe_le_one` bounds the norm of a coerced `SignType` by `1`.
`Filter.Eventually.norm_inv_le_inv` bounds the reciprocal of a real function that is eventually
bounded below by a positive constant.
-/

public section

open scoped ENNReal NNReal

namespace Real

/-- The squared extended norm of a real number is its square embedded in `ℝ≥0∞`. -/
theorem enorm_sq_eq_ofReal_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-- The squared nonnegative norm of a real number, cast to `ℝ`, is its square. -/
theorem coe_nnNorm_sq (x : ℝ) : ((‖x‖₊ ^ 2 : ℝ≥0) : ℝ) = x ^ 2 := by
  simp

/-- The squared nonnegative norm of a real number is its square, as an element of `ℝ≥0`. This is
the form in which `HasSubgaussianMGF.const_mul` scales a variance proxy. -/
theorem nnNorm_sq (x : ℝ) : ‖x‖₊ ^ 2 = ⟨x ^ 2, sq_nonneg x⟩ :=
  NNReal.eq (coe_nnNorm_sq x)

end Real

namespace SignType

/-- Coercing a `SignType` to `ℝ` has norm at most one. -/
theorem norm_coe_le_one (s : SignType) : ‖(s : ℝ)‖ ≤ 1 := by
  cases s <;> simp

end SignType

namespace Filter.Eventually

/-- If `λ ≤ a` eventually along a filter, with `λ > 0`, then `‖a⁻¹‖ ≤ λ⁻¹` eventually. -/
theorem norm_inv_le_inv {α : Type*} {l : Filter α} {a : α → ℝ} {lam : ℝ}
    (ha : ∀ᶠ t in l, lam ≤ a t) (hlam : 0 < lam) : ∀ᶠ t in l, ‖(a t)⁻¹‖ ≤ lam⁻¹ :=
  ha.mono fun t ht => by
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hlam.trans_le ht)]
    exact inv_anti₀ hlam ht

end Filter.Eventually
