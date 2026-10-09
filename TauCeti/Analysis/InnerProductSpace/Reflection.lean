/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Reflection across the orthogonal complement of a line

These lemmas describe reflection across the hyperplane perpendicular to a vector in a real
inner product space. They supply the reflection identities used by the half-space Green kernel.

`TauCeti.reflection_apply_eq_toLp_zero_one` describes the reflection sending a unit vector of
`E × ℝ` to `(0, 1)`, using Mathlib's `Submodule.reflection_sub` and the product coordinates.

In dimension at least two, composing the reflections in the hyperplanes orthogonal to a nonzero
vector `v` and to a nonzero vector orthogonal to `v` gives a linear isometry of determinant `1`
sending `v` to `-v` (`TauCeti.exists_det_eq_one_apply_eq_neg`).
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

/-- In dimension at least two, a nonzero vector `v` is sent to `-v` by a linear isometry of
determinant `1`: the product of the reflections in the hyperplanes orthogonal to `v` and to a
nonzero vector orthogonal to `v`. -/
theorem exists_det_eq_one_apply_eq_neg [FiniteDimensional ℝ F] (hF : 2 ≤ Module.finrank ℝ F)
    {v : F} (hv : v ≠ 0) :
    ∃ r : F ≃ₗᵢ[ℝ] F, (LinearEquiv.det r.toLinearEquiv : ℝ) = 1 ∧ r v = -v := by
  have hdet (w : F) (hw : w ≠ 0) :
      (LinearEquiv.det (ℝ ∙ w)ᗮ.reflection.toLinearEquiv : ℝ) = -1 := by
    rw [Submodule.linearEquiv_det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton hw]
    simp
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (ℝ ∙ v)ᗮ) fun h ↦ by
    have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ v)
    rw [h, finrank_bot, finrank_span_singleton hv] at this
    omega
  refine ⟨(ℝ ∙ v)ᗮ.reflection.trans (ℝ ∙ w)ᗮ.reflection, ?_, ?_⟩
  · rw [LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.det_trans, Units.val_mul,
      hdet _ hw0, hdet _ hv]
    norm_num
  · rw [LinearIsometryEquiv.trans_apply, Submodule.reflection_orthogonalComplement_singleton_eq_neg,
      map_neg, reflection_orthogonal_singleton_eq_self_of_inner_eq_zero]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw
    rwa [real_inner_comm]

section ProdL2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a unit vector `u` of height less than `1`, the reflection in the hyperplane orthogonal to
`(0, 1) - (a, 0)`, with `a = (1 - u.snd)⁻¹ • u.fst`, sends `u` to the vertical vector `(0, 1)`:
the vector `(0, 1) - (a, 0)` is parallel to `(0, 1) - u`. -/
theorem reflection_apply_eq_toLp_zero_one {u : WithLp 2 (E × ℝ)} (hnorm : ‖u‖ = 1)
    (hs : u.snd < 1) :
    (ℝ ∙ (WithLp.toLp 2 ((0 : E), (1 : ℝ)) -
      WithLp.toLp 2 ((1 - u.snd)⁻¹ • u.fst, 0)))ᗮ.reflection u = WithLp.toLp 2 (0, 1) := by
  have hs1 : u.snd - 1 ≠ 0 := sub_ne_zero.2 hs.ne
  have hdir : WithLp.toLp 2 ((0 : E), (1 : ℝ)) - WithLp.toLp 2 ((1 - u.snd)⁻¹ • u.fst, 0) =
      (u.snd - 1)⁻¹ • (u - WithLp.toLp 2 (0, 1)) :=
    (WithLp.ext_iff 2).2 (Prod.ext (by simp [← neg_smul, ← inv_neg])
      (by simp [inv_mul_cancel₀ hs1]))
  have hspan : (ℝ ∙ (WithLp.toLp 2 ((0 : E), (1 : ℝ)) -
      WithLp.toLp 2 ((1 - u.snd)⁻¹ • u.fst, 0))) = ℝ ∙ (u - WithLp.toLp 2 (0, 1)) := by
    rw [hdir, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hs1))]
  simp only [hspan]
  exact Submodule.reflection_sub (by simp [hnorm])

end ProdL2

end TauCeti

end
