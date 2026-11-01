/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Basic facts about positive operators

For a positive operator `T`, the off-diagonal entries are bounded by the diagonal ones,
`2 ‖⟪x, T y⟫‖ ≤ re ⟪T x, x⟫ + re ⟪T y, y⟫`
(`LinearMap.IsPositive.two_mul_norm_inner_le_add`, with the continuous version
`ContinuousLinearMap.IsPositive.two_mul_norm_inner_le_add`), by positivity of `T` at `x - z y`
for a scalar `z` of norm one.

For a positive operator `T` on a possibly infinite-dimensional Hilbert space, `1 + T` is
invertible (`ContinuousLinearMap.IsPositive.isUnit_one_add`), because
`re ⟪(1 + T) x, x⟫ ≥ ‖x‖²` bounds it below. This applies in particular to `T = X†X`, which makes
`(1 + X†X)⁻¹` available in formulas such as the orthogonal projection onto a graph subspace.
-/

public section

open scoped InnerProductSpace InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace LinearMap

/-- For a positive operator `T`, the off-diagonal entries are bounded by the diagonal ones:
`2 ‖⟪x, T y⟫‖ ≤ re ⟪T x, x⟫ + re ⟪T y, y⟫`. -/
theorem IsPositive.two_mul_norm_inner_le_add {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (x y : E) :
    2 * ‖⟪x, T y⟫_𝕜‖ ≤ RCLike.re ⟪T x, x⟫_𝕜 + RCLike.re ⟪T y, y⟫_𝕜 := by
  -- A scalar `z` of norm one rotating `⟪x, T y⟫` onto its norm.
  obtain ⟨z, hz, hzs⟩ : ∃ z : 𝕜, ‖z‖ = 1 ∧ z * ⟪x, T y⟫_𝕜 = ‖⟪x, T y⟫_𝕜‖ := by
    by_cases hs : ⟪x, T y⟫_𝕜 = 0
    · exact ⟨1, by simp, by simp [hs]⟩
    · refine ⟨‖⟪x, T y⟫_𝕜‖ / ⟪x, T y⟫_𝕜, ?_, div_mul_cancel₀ _ hs⟩
      rw [norm_div, RCLike.norm_ofReal, abs_norm, div_self (norm_ne_zero_iff.mpr hs)]
  have hzz : (starRingEnd 𝕜) z * z = 1 := by
    rw [RCLike.conj_mul, hz]
    simp
  -- Positivity of `T` at `x - z • y`.
  have e : ⟪T (x - z • y), x - z • y⟫_𝕜 =
      ⟪T x, x⟫_𝕜 - z * ⟪x, T y⟫_𝕜 - (starRingEnd 𝕜) (z * ⟪x, T y⟫_𝕜) + ⟪T y, y⟫_𝕜 := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, map_mul]
    rw [hT.isSymmetric x y, ← inner_conj_symm x (T y), RCLike.conj_conj]
    linear_combination ⟪T y, y⟫_𝕜 * hzz
  have h0 := hT.re_inner_nonneg_left (x - z • y)
  rw [e, hzs] at h0
  simp only [map_add, map_sub, RCLike.conj_re, RCLike.ofReal_re] at h0
  linarith

end LinearMap

namespace ContinuousLinearMap

/-- For a positive operator `T`, the off-diagonal entries are bounded by the diagonal ones:
`2 ‖⟪x, T y⟫‖ ≤ re ⟪T x, x⟫ + re ⟪T y, y⟫`. -/
theorem IsPositive.two_mul_norm_inner_le_add {T : E →L[𝕜] E} (hT : T.IsPositive) (x y : E) :
    2 * ‖⟪x, T y⟫_𝕜‖ ≤ RCLike.re ⟪T x, x⟫_𝕜 + RCLike.re ⟪T y, y⟫_𝕜 :=
  hT.toLinearMap.two_mul_norm_inner_le_add x y

variable [CompleteSpace E]

/-- On a complete space, `1 + T` is invertible for every positive operator `T`, since
`re ⟪(1 + T) x, x⟫ = ‖x‖² + re ⟪T x, x⟫ ≥ ‖x‖²`. For instance `1 + X†X` is invertible, by
`ContinuousLinearMap.isPositive_adjoint_comp_self`. -/
theorem IsPositive.isUnit_one_add {T : E →L[𝕜] E} (hT : T.IsPositive) : IsUnit (1 + T) := by
  refine isUnit_of_forall_le_norm_inner_map _ one_pos fun x => ?_
  rw [NNReal.coe_one, mul_one]
  calc ‖x‖ ^ 2 ≤ RCLike.re ⟪(1 + T) x, x⟫_𝕜 := by
        rw [add_apply, one_apply_eq_self, inner_add_left, map_add, inner_self_eq_norm_sq]
        exact le_add_of_nonneg_right (hT.re_inner_nonneg_left x)
    _ ≤ ‖⟪(1 + T) x, x⟫_𝕜‖ := RCLike.re_le_norm _

end ContinuousLinearMap
