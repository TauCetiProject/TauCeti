/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Inner-product half-spaces

A translation orthogonal to the normal vector preserves a strict half-space. The ball of radius
`r` about a unit vector `x` lies in the half-space `{z | 1 - r ≤ ⟪x, z⟫}`. The projection
`z - (⟪z, ν⟫ / ‖ν‖²) ν` lands in the boundary hyperplane `{z | ⟪z, ν⟫ = 0}`.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

/-- Every translation parallel to the boundary of the half-space `{x | c < ⟪x, ν⟫}` maps it into
itself. -/
theorem mapsTo_add_smul_of_halfSpace {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : Set E} {ν τ : E} {c : ℝ}
    (hΩ : ∀ x, x ∈ s ↔ c < ⟪x, ν⟫_ℝ) (hτ : ⟪τ, ν⟫_ℝ = 0) (t : ℝ) :
    Set.MapsTo (· + t • τ) s s := fun x hx => by
  have hx' := (hΩ x).1 hx
  exact (hΩ _).2 (by simpa [inner_add_left, real_inner_smul_left, hτ] using hx')

/-- The inner product of a unit vector `x` with `z` is at least `1 - ‖z - x‖`. -/
theorem one_sub_norm_sub_le_inner {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : ‖x‖ = 1) (z : E) : 1 - ‖z - x‖ ≤ ⟪x, z⟫_ℝ := by
  have h := real_inner_le_norm x (x - z)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hx, norm_sub_rev] at h
  linarith

/-- The projection `z - (⟪z, ν⟫ / ‖ν‖²) ν` onto the hyperplane orthogonal to `ν` is orthogonal
to `ν`. It is the explicit form of `z - (ℝ ∙ ν).starProjection z`, by
`Submodule.starProjection_singleton`. -/
theorem real_inner_sub_div_norm_sq_smul_self_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (z ν : E) : ⟪z - (⟪z, ν⟫_ℝ / ‖ν‖ ^ 2) • ν, ν⟫_ℝ = 0 := by
  rcases eq_or_ne ν 0 with rfl | hν
  · simp
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ (pow_pos (norm_pos_iff.2 hν) 2).ne', sub_self]

end TauCeti
