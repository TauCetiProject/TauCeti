/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Reflection across the orthogonal complement of a line

These lemmas describe reflection across the hyperplane perpendicular to a vector in a real
inner product space. They supply the reflection identities used by the half-space Green kernel.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Reflection through the hyperplane perpendicular to a unit normal `v` has this explicit
formula. -/
theorem reflection_orthogonal_singleton_apply {v : F} (hv : ‖v‖ = 1) (x : F) :
    (ℝ ∙ v)ᗮ.reflection x = x - (2 * ⟪v, x⟫_ℝ) • v := by
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, neg_sub,
    hv, one_pow, div_one, two_smul, two_mul, add_smul]

/-- Reflection negates the component in the normal direction. -/
@[simp] theorem inner_reflection_orthogonal_singleton {v : F} (x : F) :
    ⟪v, (ℝ ∙ v)ᗮ.reflection x⟫_ℝ = -⟪v, x⟫_ℝ := by
  rw [← LinearIsometryEquiv.inner_map_map (ℝ ∙ v)ᗮ.reflection,
    Submodule.reflection_reflection,
    Submodule.reflection_orthogonalComplement_singleton_eq_neg, inner_neg_left]

/-- A point on the bounding hyperplane is fixed by reflection. -/
theorem reflection_orthogonal_singleton_eq_self_of_inner_eq_zero {v x : F}
    (hx : ⟪v, x⟫_ℝ = 0) : (ℝ ∙ v)ᗮ.reflection x = x := by
  exact Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx)

/-- Reflection moves across a distance to the image point. -/
theorem norm_sub_reflection_orthogonal_singleton (v x y : F) :
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ = ‖(ℝ ∙ v)ᗮ.reflection y - x‖ := by
  calc
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ =
        ‖(ℝ ∙ v)ᗮ.reflection (y - (ℝ ∙ v)ᗮ.reflection x)‖ :=
      (((ℝ ∙ v)ᗮ.reflection).norm_map _).symm
    _ = ‖(ℝ ∙ v)ᗮ.reflection y - x‖ := by simp [map_sub]

/-- At the boundary, the pole and its image are equidistant from the variable point. -/
theorem norm_sub_reflection_orthogonal_singleton_eq_of_inner_eq_zero {v : F}
    (x : F) {y : F} (hy : ⟪v, y⟫_ℝ = 0) :
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ = ‖y - x‖ := by
  rw [norm_sub_reflection_orthogonal_singleton,
    reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hy]

/-- A point whose normal component differs from the negated component of `x` is not its
reflection. -/
theorem ne_reflection_orthogonal_singleton_of_inner_ne_neg {v x y : F}
    (hinner : ⟪v, y⟫_ℝ ≠ -⟪v, x⟫_ℝ) :
    y ≠ (ℝ ∙ v)ᗮ.reflection x := by
  intro h
  rw [h, inner_reflection_orthogonal_singleton] at hinner
  exact hinner rfl

/-- The squared distance to the image pole exceeds the squared distance to the pole by
four times the product of the two signed distances to the boundary. -/
theorem norm_sub_reflection_orthogonal_singleton_sq {v : F} (hv : ‖v‖ = 1) (x y : F) :
    ‖y - (ℝ ∙ v)ᗮ.reflection x‖ ^ 2 =
      ‖y - x‖ ^ 2 + 4 * ⟪v, x⟫_ℝ * ⟪v, y⟫_ℝ := by
  have heq : y - (ℝ ∙ v)ᗮ.reflection x =
      (y - x) + (2 * ⟪v, x⟫_ℝ) • v := by
    rw [reflection_orthogonal_singleton_apply hv]
    abel
  rw [heq, norm_add_sq_real, inner_smul_right, inner_sub_left, norm_smul, hv]
  simp only [mul_one, Real.norm_eq_abs, sq_abs]
  rw [real_inner_comm y v, real_inner_comm x v]
  ring

/-- Both points in the positive half-space are closer to each other than to the image pole. -/
theorem norm_sub_lt_norm_sub_reflection_orthogonal_singleton {v x y : F} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) :
    ‖y - x‖ < ‖y - (ℝ ∙ v)ᗮ.reflection x‖ := by
  have hsq := norm_sub_reflection_orthogonal_singleton_sq hv x y
  nlinarith [norm_nonneg (y - x), norm_nonneg (y - (ℝ ∙ v)ᗮ.reflection x),
    mul_pos hx hy]

end TauCeti

end
