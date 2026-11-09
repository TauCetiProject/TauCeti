/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap

/-!
# Conformal linear maps with a reciprocal conformal factor

Mathlib characterises a conformal linear map `L` between real inner product spaces by
`⟪L u, L v⟫ = c * ⟪u, v⟫` with `c > 0` (`isConformalMap_iff`). In conformal geometry the factor
often appears on the other side, as a *reciprocal* scale `ρ` with `ρ² ⟪L u, L v⟫ = ⟪u, v⟫`; this
is how Liouville's theorem (`TauCeti.Analysis.Calculus.Conformal.Liouville`) parametrises a
conformal map. This file connects the two forms.

## Main results

* `TauCeti.isConformalMap_of_sq_mul_inner`: a continuous linear map with
  `ρ² ⟪L u, L v⟫ = ⟪u, v⟫` and `ρ ≠ 0` is conformal, hence injective
  (`IsConformalMap.injective`).
* `TauCeti.eq_inv_norm_apply_of_sq_mul_inner`: a positive reciprocal scale is the reciprocal of
  the length of the image of any unit vector.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {L : E →L[ℝ] F} {ρ : ℝ}

/-- A continuous linear map which scales inner products by `ρ⁻²` for some `ρ ≠ 0`, written as
`ρ² ⟪L u, L v⟫ = ⟪u, v⟫`, is conformal. -/
theorem isConformalMap_of_sq_mul_inner (hρ : ∀ u v, ρ ^ 2 * ⟪L u, L v⟫ = ⟪u, v⟫) (hρ0 : ρ ≠ 0) :
    IsConformalMap L := by
  refine (isConformalMap_iff L).2 ⟨(ρ ^ 2)⁻¹, by positivity, fun u v ↦ ?_⟩
  rw [← hρ, inv_mul_cancel_left₀ (pow_ne_zero 2 hρ0)]

/-- If `ρ > 0` and `ρ² ⟪L u, L v⟫ = ⟪u, v⟫` for all `u` and `v`, then `ρ` is the reciprocal of
the length of the image of any unit vector. -/
theorem eq_inv_norm_apply_of_sq_mul_inner (hρ : ∀ u v, ρ ^ 2 * ⟪L u, L v⟫ = ⟪u, v⟫)
    (hρ0 : 0 < ρ) {e : E} (he : ‖e‖ = 1) : ρ = ‖L e‖⁻¹ := by
  have h := hρ e e
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he, one_pow, ← mul_pow] at h
  exact eq_inv_of_mul_eq_one_left
    ((pow_eq_one_iff_of_nonneg (mul_nonneg hρ0.le (norm_nonneg _)) two_ne_zero).1 h)

end TauCeti
