/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Reflections in inner product spaces

For a submodule `K` admitting an orthogonal projection, `Submodule.coe_reflection` expresses the
reflection across `K`, as a bounded operator, as `2 P_K - 1`, and a linear isometry mapping `K`
onto itself commutes with that reflection (`Submodule.reflection_apply_of_map_eq`).

The remaining lemmas describe reflection across the hyperplane perpendicular to a vector in a real
inner product space. They supply the reflection identities used by the half-space Green kernel,
and the splitting of the squared distance from a point of the hyperplane into the squared distance
to the foot of a point and its squared height (`TauCeti.norm_sub_sq_eq_of_inner_eq_zero`).

In dimension at least two, every vector `v` is sent to `-v` by a linear isometry of determinant
`1` (`TauCeti.exists_det_eq_one_apply_eq_neg`). For nonzero `v`, this is the composition of the
reflections in the hyperplanes orthogonal to `v` and to a nonzero vector orthogonal to `v`.

`LinearIsometry.exists_contDiff_path_reflection_orthogonal_range` gives a smooth path from the
identity to a half-turn in any distinguished complex plane, by composing two hyperplane
reflections. It supplies the sphere motion which interchanges the two halves of a connected sum.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The reflection across `K`, as a bounded operator, is `2 P_K - 1`. -/
theorem coe_reflection (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    (K.reflection : E →L[𝕜] E) = 2 • K.starProjection - 1 := by
  ext x
  simp [reflection_apply]

/-- A linear isometry equivalence mapping `K` onto itself commutes with the reflection across
`K`. -/
theorem reflection_apply_of_map_eq (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    {e : E ≃ₗᵢ[𝕜] E} (he : K.map (e.toLinearEquiv : E →ₗ[𝕜] E) = K) (x : E) :
    K.reflection (e x) = e (K.reflection x) := by
  have h := reflection_map_apply e K (e x)
  simp only [he, LinearIsometryEquiv.symm_apply_apply] at h
  exact h

/-- A linear isometry equivalence fixing `K` pointwise commutes with reflection across `K`. -/
theorem reflection_apply_of_eqOn (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    {e : E ≃ₗᵢ[𝕜] E} (he : Set.EqOn e id K) (x : E) :
    K.reflection (e x) = e (K.reflection x) := by
  refine reflection_apply_of_map_eq K ?_ x
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, he hw]
    exact hw
  · intro hv
    exact ⟨v, hv, he hv⟩

/-- A linear isometry equivalence fixing `K` pointwise commutes with reflection across `Kᗮ`. -/
theorem reflection_orthogonal_apply_of_eqOn (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    {e : E ≃ₗᵢ[𝕜] E} (he : Set.EqOn e id K) (x : E) :
    Kᗮ.reflection (e x) = e (Kᗮ.reflection x) := by
  rw [reflection_orthogonal_apply, reflection_apply_of_eqOn K he,
    reflection_orthogonal_apply, map_neg]

/-- Reflection across `Kᗮ` negates the inner product with any vector in `K`. -/
theorem inner_reflection_orthogonal_of_mem (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (x : E) {v : E} (hv : v ∈ K) :
    inner 𝕜 (Kᗮ.reflection x) v = -inner 𝕜 x v := by
  conv_lhs => rw [← neg_neg v,
    ← reflection_mem_subspace_orthogonal_precomplement_eq_neg hv, inner_neg_right,
    LinearIsometryEquiv.inner_map_map]

end Submodule

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

/-- For a point `y` of the hyperplane perpendicular to a unit vector `v`, the squared distance
from `y` to `x` splits into the squared distance from `y` to the foot `x - ⟪v, x⟫ v` of `x` and
the squared height of `x`. -/
theorem norm_sub_sq_eq_of_inner_eq_zero {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : ‖v‖ = 1) (x : E) {y : E} (hy : ⟪v, y⟫_ℝ = 0) :
    ‖y - x‖ ^ 2 = ‖y - (x - ⟪v, x⟫_ℝ • v)‖ ^ 2 + ⟪v, x⟫_ℝ ^ 2 := by
  have hy' : ⟪y, v⟫_ℝ = 0 := by rwa [real_inner_comm]
  simp only [norm_sub_sq_real, inner_sub_right, inner_smul_right, norm_smul, hv,
    mul_one, Real.norm_eq_abs, sq_abs, hy', mul_zero, sub_zero]
  rw [real_inner_comm x v]
  ring

/-- Both points in the positive half-space are closer to each other than to the image pole. -/
theorem norm_sub_lt_norm_sub_reflection_orthogonal_singleton {v x y : F} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) :
    ‖y - x‖ < ‖y - (ℝ ∙ v)ᗮ.reflection x‖ := by
  have hsq := norm_sub_reflection_orthogonal_singleton_sq hv x y
  nlinarith [norm_nonneg (y - x), norm_nonneg (y - (ℝ ∙ v)ᗮ.reflection x),
    mul_pos hx hy]

/-- In dimension at least two, every vector `v` is sent to `-v` by a linear isometry of
determinant `1`. For nonzero `v`, take the product of the reflections in the hyperplanes
orthogonal to `v` and to a nonzero vector orthogonal to `v`. -/
theorem exists_det_eq_one_apply_eq_neg (hF : 2 ≤ Module.finrank ℝ F) (v : F) :
    ∃ r : F ≃ₗᵢ[ℝ] F, (LinearEquiv.det r.toLinearEquiv : ℝ) = 1 ∧ r v = -v := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  by_cases hv : v = 0
  · exact ⟨LinearIsometryEquiv.refl ℝ F, by simp, by simp [hv]⟩
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

end TauCeti

end

noncomputable section

namespace LinearIsometry

open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ι : ℂ →ₗᵢ[ℝ] E)

/-- The path of normals in the distinguished plane used to factor a half-turn as two
hyperplane reflections. -/
private def turningNormal (t : ℝ) : E := ι (Circle.exp (Real.pi / 2 * t) : ℂ)

private theorem norm_turningNormal (t : ℝ) : ‖turningNormal ι t‖ = 1 := by
  rw [turningNormal, ι.norm_map]
  exact Circle.norm_coe _

private theorem turningNormal_zero : turningNormal ι 0 = ι 1 := by
  simp [turningNormal]

private theorem turningNormal_one : turningNormal ι 1 = ι Complex.I := by
  simp only [turningNormal, mul_one, Circle.coe_exp, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]

/-- The two-reflection rotation of the ambient space. -/
private def turningIsometry (t : ℝ) : E ≃ₗᵢ[ℝ] E :=
  (ℝ ∙ ι 1)ᗮ.reflection.trans (ℝ ∙ turningNormal ι t)ᗮ.reflection

private theorem turningIsometry_zero (x : E) : turningIsometry ι 0 x = x := by
  simp [turningIsometry, turningNormal_zero]

private theorem turningIsometry_one (x : E) :
    turningIsometry ι 1 x = (LinearMap.range ι.toLinearMap)ᗮ.reflection x := by
  let K := LinearMap.range ι.toLinearMap
  obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  obtain ⟨w, rfl⟩ := hy
  have hz1 : ⟪ι 1, z⟫ = 0 :=
    ((K.mem_orthogonal z).mp hz) _ (LinearMap.mem_range_self _ _)
  have hzi : ⟪ι Complex.I, z⟫ = 0 :=
    ((K.mem_orthogonal z).mp hz) _ (LinearMap.mem_range_self _ _)
  have hw : ι w = w.re • ι 1 + w.im • ι Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simp [Complex.real_smul]
  have h1 : ‖ι 1‖ = 1 := by simp
  have hi : ‖ι Complex.I‖ = 1 := by simp
  simp only [turningIsometry, LinearIsometryEquiv.trans_apply, turningNormal_one,
    LinearIsometry.coe_toLinearMap]
  rw [map_add, map_add, map_add,
    TauCeti.reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hz1,
    TauCeti.reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hzi,
    Submodule.reflection_mem_subspace_eq_self hz,
    Submodule.reflection_mem_subspace_orthogonal_precomplement_eq_neg
      (K := ι.range) (v := ι w) ⟨w, rfl⟩]
  rw [TauCeti.reflection_orthogonal_singleton_apply h1,
    TauCeti.reflection_orthogonal_singleton_apply hi, hw]
  simp [ι.inner_map_map, Complex.inner, inner_add_right, inner_smul_right, inner_sub_right]
  module

private theorem contDiff_turningIsometry :
    ContDiff ℝ ∞ (fun p : ℝ × E => turningIsometry ι p.1 p.2) := by
  have hu : ContDiff ℝ ∞ (fun p : ℝ × E => turningNormal ι p.1) := by
    exact ι.contDiff.comp
      ((Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_fst)).mul contDiff_const)))
  have hv : ContDiff ℝ ∞ (fun p : ℝ × E => (ℝ ∙ ι 1)ᗮ.reflection p.2) :=
    (ℝ ∙ ι 1)ᗮ.reflection.contDiff.comp contDiff_snd
  have hformula (p : ℝ × E) : turningIsometry ι p.1 p.2 =
      (ℝ ∙ ι 1)ᗮ.reflection p.2 -
        (2 * ⟪turningNormal ι p.1, (ℝ ∙ ι 1)ᗮ.reflection p.2⟫) •
          turningNormal ι p.1 := by
    exact TauCeti.reflection_orthogonal_singleton_apply (norm_turningNormal ι p.1) _
  simp_rw [hformula]
  exact hv.sub ((contDiff_const.mul (hu.inner ℝ hv)).smul hu)

/-- A half-turn in an isometrically embedded complex plane is connected to the identity by a
smooth family of linear isometries. The parameter runs over all real numbers; times zero and
one give the identity and reflection across the orthogonal complement of the plane.

This is the usual factorization of a rotation as two hyperplane reflections, with one normal
moving along a quarter of the unit circle. -/
theorem exists_contDiff_path_reflection_orthogonal_range :
    ∃ R : ℝ → E ≃ₗᵢ[ℝ] E, ContDiff ℝ ∞ (fun p : ℝ × E => R p.1 p.2) ∧
      (∀ x, R 0 x = x) ∧ ∀ x, R 1 x = ι.rangeᗮ.reflection x :=
  ⟨turningIsometry ι, contDiff_turningIsometry ι, turningIsometry_zero ι,
    turningIsometry_one ι⟩

end LinearIsometry
