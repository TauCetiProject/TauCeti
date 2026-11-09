/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5,
  OpenAI GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Reflections in inner product spaces

For a submodule `K` admitting an orthogonal projection, `Submodule.coe_reflection` expresses the
reflection across `K`, as a bounded operator, as `2 P_K - 1`, and a linear isometry mapping `K`
onto itself commutes with that reflection (`Submodule.reflection_apply_of_map_eq`). In Euclidean
space, the reflection in the axis spanned by a basis vector `eᵢ` keeps the `i`-th coordinate and
negates the others (`EuclideanSpace.reflection_singleton_single_apply`).

The remaining lemmas describe reflection across the hyperplane perpendicular to a vector in a real
inner product space. They supply the reflection identities used by the half-space Green kernel,
and the splitting of the squared distance from a point of the hyperplane into the squared distance
to the foot of a point and its squared height (`TauCeti.norm_sub_sq_eq_of_inner_eq_zero`). For a
linear isometry `ι : ℂ → F`, the reflection in the hyperplane perpendicular to `ι i` is complex
conjugation on the plane `ι ℂ` (`LinearIsometry.reflection_orthogonal_singleton_map_I`).

In dimension at least two, every vector `v` is sent to `-v` by a linear isometry of determinant
`1` (`TauCeti.exists_det_eq_one_apply_eq_neg`). For nonzero `v`, this is the composition of the
reflections in the hyperplanes orthogonal to `v` and to a nonzero vector orthogonal to `v`.
In every nonzero finite dimension, the reflection in the hyperplane orthogonal to a nonzero vector
is a linear isometry of determinant `-1` (`TauCeti.exists_det_eq_neg_one`), so of negative
determinant as a continuous linear map (`TauCeti.exists_det_neg`).

`LinearIsometry.exists_contDiff_path_reflection_orthogonal_range` gives a smooth path from the
identity to a half-turn in any distinguished complex plane, by composing two hyperplane
reflections. It supplies the sphere motion which interchanges the two halves of a connected sum.

In the same way, two unit vectors `a` and `b` with `a ≠ -b` are joined by a rotation in the plane
they span: reflecting in the hyperplane orthogonal to `a` and then in the one orthogonal to `a + b`
sends `a` to `b` and fixes every vector orthogonal to both. Moving the second normal from `a` to
`a + b` connects this rotation to the identity by an analytic path of linear isometries
(`TauCeti.exists_contDiff_path_apply_eq`).

Composing four such reflections rotates a whole `C^k` path `u` of unit vectors orthogonal to a
vector `v` back to its value `u s₀`, by a `C^k` family of linear isometries fixing `v`, as soon as
the orthogonal complement of `v` has dimension at least three
(`TauCeti.exists_contDiff_linearIsometryEquiv_apply_eq`). The rotations pass through an auxiliary
unit vector `p` orthogonal to `v` with `u s + p ≠ 0` for every `s`
(`TauCeti.exists_forall_add_ne_zero`), which exists because the cone `(s, r) ↦ -r • u s` is the
image of a plane and so misses a point of the orthogonal complement.

More generally, every linear isometry of determinant `1` of a finite-dimensional real inner product
space is the time-one map of an analytic path of linear isometries starting at the identity
(`LinearIsometryEquiv.exists_contDiff_path_of_det_eq_one`). By the Cartan–Dieudonné theorem
(`LinearIsometryEquiv.reflections_generate_dim`) such an isometry is a product of hyperplane
reflections, an even number of them nontrivial, since each hyperplane reflection has determinant
`-1` (`TauCeti.linearEquiv_det_reflection_orthogonal_singleton`). The product of the reflections in
the hyperplanes orthogonal to unit vectors `a` and `b` is joined to the identity by moving the
normal of the reflection applied second from `a` to `b` along the segment between them, which
avoids `0` unless `b = -a`; the remaining reflections are absorbed by conjugation.
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

namespace EuclideanSpace

/-- The reflection of Euclidean space in the coordinate axis spanned by the basis vector `eᵢ`
keeps the `i`-th coordinate and negates all the others. -/
@[simp]
theorem reflection_singleton_single_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (w : EuclideanSpace ℝ ι) (j : ι) :
    (ℝ ∙ EuclideanSpace.single i (1 : ℝ)).reflection w j = if j = i then w j else -w j := by
  rw [Submodule.reflection_singleton_apply]
  by_cases h : j = i
  · subst h
    simp [EuclideanSpace.inner_single_left]
    ring
  · simp [EuclideanSpace.inner_single_left, h]

end EuclideanSpace

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

/-- Reflection through the hyperplane perpendicular to an arbitrary normal `u` has this explicit
formula; for `u = 0` both sides are `x`. -/
theorem reflection_orthogonal_singleton_apply_div_norm_sq (u x : F) :
    (ℝ ∙ u)ᗮ.reflection x = x - (2 * (⟪u, x⟫_ℝ / ‖u‖ ^ 2)) • u := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id_eq, two_smul, neg_sub, two_mul, add_smul]

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

/-- For a linear isometry `ι : ℂ → F`, the reflection in the hyperplane perpendicular to `ι i`
acts on the plane `ι ℂ` by complex conjugation. -/
theorem _root_.LinearIsometry.reflection_orthogonal_singleton_map_I (ι : ℂ →ₗᵢ[ℝ] F) (w : ℂ) :
    (ℝ ∙ ι Complex.I)ᗮ.reflection (ι w) = ι ((starRingEnd ℂ) w) := by
  rw [reflection_orthogonal_singleton_apply (by simp), ι.inner_map_map, ← ι.map_smul, ← map_sub]
  congr 1
  apply Complex.ext <;> simp [Complex.inner]
  ring

/-- Both points in the positive half-space are closer to each other than to the image pole. -/
theorem norm_sub_lt_norm_sub_reflection_orthogonal_singleton {v x y : F} (hv : ‖v‖ = 1)
    (hx : 0 < ⟪v, x⟫_ℝ) (hy : 0 < ⟪v, y⟫_ℝ) :
    ‖y - x‖ < ‖y - (ℝ ∙ v)ᗮ.reflection x‖ := by
  have hsq := norm_sub_reflection_orthogonal_singleton_sq hv x y
  nlinarith [norm_nonneg (y - x), norm_nonneg (y - (ℝ ∙ v)ᗮ.reflection x),
    mul_pos hx hy]

/-- Reflection in the hyperplane orthogonal to a nonzero vector has determinant `-1`. -/
theorem linearEquiv_det_reflection_orthogonal_singleton [FiniteDimensional ℝ F] {v : F}
    (hv : v ≠ 0) : (LinearEquiv.det (ℝ ∙ v)ᗮ.reflection.toLinearEquiv : ℝ) = -1 := by
  rw [Submodule.linearEquiv_det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton hv]
  simp

/-- In dimension at least two, every vector `v` is sent to `-v` by a linear isometry of
determinant `1`. For nonzero `v`, take the product of the reflections in the hyperplanes
orthogonal to `v` and to a nonzero vector orthogonal to `v`. -/
theorem exists_det_eq_one_apply_eq_neg (hF : 2 ≤ Module.finrank ℝ F) (v : F) :
    ∃ r : F ≃ₗᵢ[ℝ] F, (LinearEquiv.det r.toLinearEquiv : ℝ) = 1 ∧ r v = -v := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos (by omega)
  by_cases hv : v = 0
  · exact ⟨LinearIsometryEquiv.refl ℝ F, by simp, by simp [hv]⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := (ℝ ∙ v)ᗮ) fun h ↦ by
    have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ v)
    rw [h, finrank_bot, finrank_span_singleton hv] at this
    omega
  refine ⟨(ℝ ∙ v)ᗮ.reflection.trans (ℝ ∙ w)ᗮ.reflection, ?_, ?_⟩
  · rw [LinearIsometryEquiv.toLinearEquiv_trans, LinearEquiv.det_trans, Units.val_mul,
      linearEquiv_det_reflection_orthogonal_singleton hw0,
      linearEquiv_det_reflection_orthogonal_singleton hv]
    norm_num
  · rw [LinearIsometryEquiv.trans_apply, Submodule.reflection_orthogonalComplement_singleton_eq_neg,
      map_neg, reflection_orthogonal_singleton_eq_self_of_inner_eq_zero]
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hw
    rwa [real_inner_comm]

/-- A nontrivial finite-dimensional real inner product space has a linear isometry of
determinant `-1`: the reflection in the hyperplane orthogonal to a nonzero vector. -/
theorem exists_det_eq_neg_one [Nontrivial F] [FiniteDimensional ℝ F] :
    ∃ r : F ≃ₗᵢ[ℝ] F, (LinearEquiv.det r.toLinearEquiv : ℝ) = -1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  refine ⟨(ℝ ∙ v)ᗮ.reflection, ?_⟩
  rw [Submodule.linearEquiv_det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton hv]
  simp

/-- A nontrivial finite-dimensional real inner product space has a linear isometry whose
underlying continuous linear map has negative determinant, the form taken by the
orientation-reversal lemmas for linear automorphisms. -/
theorem exists_det_neg [Nontrivial F] [FiniteDimensional ℝ F] :
    ∃ r : F ≃ₗᵢ[ℝ] F, LinearMap.det (r.toContinuousLinearEquiv : F →ₗ[ℝ] F) < 0 := by
  obtain ⟨r, hr⟩ := exists_det_eq_neg_one (F := F)
  refine ⟨r, ?_⟩
  rw [← LinearEquiv.coe_det]
  exact hr.trans_lt (by norm_num)

end TauCeti

end

noncomputable section

namespace LinearIsometry

open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (ι : ℂ →ₗᵢ[ℝ] E)

/-- Reflection across the orthogonal complement of the range negates every vector in the
isometrically embedded complex plane. -/
@[simp]
theorem reflection_orthogonal_range_apply (w : ℂ) : ι.rangeᗮ.reflection (ι w) = -ι w :=
  Submodule.reflection_mem_subspace_orthogonal_precomplement_eq_neg
    (K := ι.range) (LinearMap.mem_range_self _ w)

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

/-- The two-reflection rotation of the ambient space. This is the usual factorization of a rotation
as two hyperplane reflections, with one normal moving along a quarter of the unit circle. -/
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
  have h1i : ⟪ι 1, ι Complex.I⟫ = 0 := by simp [ι.inner_map_map, Complex.inner]
  have hi1 : ⟪ι Complex.I, ι 1⟫ = 0 := by rw [real_inner_comm, h1i]
  simp only [turningIsometry, LinearIsometryEquiv.trans_apply, turningNormal_one,
    LinearIsometry.coe_toLinearMap]
  rw [map_add, map_add, map_add,
    TauCeti.reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hz1,
    TauCeti.reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hzi,
    Submodule.reflection_mem_subspace_eq_self hz, ι.reflection_orthogonal_range_apply, hw]
  simp only [map_add, map_smul, map_neg, Submodule.reflection_orthogonalComplement_singleton_eq_neg,
    TauCeti.reflection_orthogonal_singleton_eq_self_of_inner_eq_zero h1i,
    TauCeti.reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hi1]
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
one give the identity and reflection across the orthogonal complement of the plane. -/
theorem exists_contDiff_path_reflection_orthogonal_range :
    ∃ R : ℝ → E ≃ₗᵢ[ℝ] E, ContDiff ℝ ∞ (fun p : ℝ × E => R p.1 p.2) ∧
      (∀ x, R 0 x = x) ∧ ∀ x, R 1 x = ι.rangeᗮ.reflection x :=
  ⟨turningIsometry ι, contDiff_turningIsometry ι, turningIsometry_zero ι,
    turningIsometry_one ι⟩

end LinearIsometry

namespace TauCeti

open scoped RealInnerProductSpace ContDiff

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Reflecting in the hyperplane orthogonal to `a + b`, for vectors `a` and `b` of the same norm,
sends `-a` to `b`. This is `Submodule.reflection_sub` for `-a` and `b`. -/
theorem reflection_orthogonal_singleton_add_apply_neg {a b : F} (h : ‖a‖ = ‖b‖) :
    (ℝ ∙ (a + b))ᗮ.reflection (-a) = b := by
  have hspan : (ℝ ∙ (-a - b)) = ℝ ∙ (a + b) := by
    rw [← neg_add', ← Set.neg_singleton, Submodule.span_neg]
  have h' := Submodule.reflection_sub (v := -a) (w := b) (by rw [norm_neg, h])
  simpa only [hspan] using h'

/-- Reflection in the hyperplane orthogonal to a nonvanishing `C^k` normal `c p`, applied to a
`C^k` vector `y p`, depends `C^k` on the parameter `p`. -/
theorem contDiff_reflection_orthogonal_singleton_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {k : ℕ∞ω} {c y : X → F} (hc : ContDiff ℝ k c) (hy : ContDiff ℝ k y)
    (hc₀ : ∀ p, c p ≠ 0) :
    ContDiff ℝ k fun p => (ℝ ∙ c p)ᗮ.reflection (y p) := by
  have h : (fun p => (ℝ ∙ c p)ᗮ.reflection (y p)) = fun p =>
      y p - (2 * (⟪c p, y p⟫ / ‖c p‖ ^ 2)) • c p :=
    funext fun p => reflection_orthogonal_singleton_apply_div_norm_sq _ _
  rw [h]
  exact hy.sub ((contDiff_const.mul ((hc.inner ℝ hy).div ((contDiff_norm_sq ℝ).comp hc)
    fun p => pow_ne_zero 2 (norm_ne_zero_iff.2 (hc₀ p)))).smul hc)

/-- Reflecting in the hyperplane orthogonal to `a` and then in the hyperplane orthogonal to a
nonvanishing analytic normal `c t` is analytic jointly in the time and the vector. -/
private theorem contDiff_reflection_trans_reflection {a : F} {c : ℝ → F} (hc : ContDiff ℝ ω c)
    (hc₀ : ∀ t, c t ≠ 0) :
    ContDiff ℝ ω fun p : ℝ × F => ((ℝ ∙ a)ᗮ.reflection.trans (ℝ ∙ c p.1)ᗮ.reflection) p.2 :=
  contDiff_reflection_orthogonal_singleton_apply (hc.comp contDiff_fst)
    ((ℝ ∙ a)ᗮ.reflection.toContinuousLinearEquiv.contDiff.comp contDiff_snd) fun p => hc₀ p.1

/-- The rotation from `a` toward `b` at time `t`: the reflection in the hyperplane orthogonal to
`a`, followed by the reflection in the hyperplane orthogonal to `a + t² b`. -/
private def pairRotation (a b : F) (t : ℝ) : F ≃ₗᵢ[ℝ] F :=
  (ℝ ∙ a)ᗮ.reflection.trans (ℝ ∙ (a + t ^ 2 • b))ᗮ.reflection

/-- **Rotating one unit vector to another.** Two unit vectors `a` and `b` with `a ≠ -b` are
joined by an analytic path of linear isometries, starting at the identity, whose time-one map
sends `a` to `b` and fixes every vector orthogonal to both `a` and `b`. -/
theorem exists_contDiff_path_apply_eq {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ -b) :
    ∃ R : ℝ → F ≃ₗᵢ[ℝ] F, ContDiff ℝ ω (fun p : ℝ × F => R p.1 p.2) ∧ (∀ x, R 0 x = x) ∧
      R 1 a = b ∧ ∀ x, ⟪a, x⟫ = 0 → ⟪b, x⟫ = 0 → R 1 x = x := by
  -- The moving normal `a + t² b` never vanishes, since `‖a‖ = ‖b‖` and `a ≠ -b`.
  have hu (t : ℝ) : a + t ^ 2 • b ≠ 0 := by
    refine fun h => hab ?_
    have h₁ : a = -(t ^ 2 • b) := eq_neg_of_add_eq_zero_left h
    have hs : t ^ 2 = 1 := by
      have := congrArg norm h₁
      rwa [norm_neg, norm_smul, ha, hb, mul_one, Real.norm_of_nonneg (sq_nonneg t), eq_comm]
        at this
    rw [h₁, hs, one_smul]
  refine ⟨pairRotation a b, ?_, fun x => ?_, ?_, fun x hax hbx => ?_⟩
  · exact contDiff_reflection_trans_reflection (c := fun t => a + t ^ 2 • b)
      (contDiff_const.add ((contDiff_id.pow 2).smul contDiff_const)) hu
  · simp [pairRotation]
  · rw [pairRotation, LinearIsometryEquiv.trans_apply,
      Submodule.reflection_orthogonalComplement_singleton_eq_neg]
    simpa only [one_pow, one_smul] using
      reflection_orthogonal_singleton_add_apply_neg (ha.trans hb.symm)
  · rw [pairRotation, LinearIsometryEquiv.trans_apply,
      reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hax,
      reflection_orthogonal_singleton_eq_self_of_inner_eq_zero]
    rw [inner_add_left, inner_smul_left, hax, hbx]
    simp

/-- A differentiable path `u` of unit vectors orthogonal to `v`, in a space where the orthogonal
complement of `v` has dimension at least three, avoids the antipode of some unit vector `p`
orthogonal to `v`: `u s + p ≠ 0` for every `s`. The cone `(s, r) ↦ -r • u s` over the antipodal
path is the image of a plane, so it misses a point of the orthogonal complement. -/
theorem exists_forall_add_ne_zero {v : F}
    (hF : 2 < Module.finrank ℝ (ℝ ∙ v)ᗮ) {u : ℝ → F} (hu : Differentiable ℝ u)
    (hv : ∀ s, ⟪u s, v⟫ = 0) :
    ∃ p : F, ‖p‖ = 1 ∧ ⟪p, v⟫ = 0 ∧ ∀ s, u s + p ≠ 0 := by
  set K := (ℝ ∙ v)ᗮ
  let g : ℝ × ℝ → K := fun q => q.2 • K.orthogonalProjectionOnto (-u q.1)
  have hP : Differentiable ℝ fun q : ℝ × ℝ => K.orthogonalProjectionOnto (-u q.1) :=
    K.orthogonalProjectionOnto.differentiable.comp (hu.comp differentiable_fst).neg
  have hg : Differentiable ℝ g := differentiable_snd.smul hP
  obtain ⟨q, hq⟩ := (hg.dense_compl_range_of_finrank_lt_finrank (by
    rw [Module.finrank_prod, Module.finrank_self]
    omega)).nonempty
  have hmem (s : ℝ) : -u s ∈ K :=
    K.neg_mem (Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by
      rw [real_inner_comm]; exact hv s))
  have hq0 : (q : F) ≠ 0 := by
    intro h
    exact hq ⟨(0, 0), Subtype.ext (by simp [g, h])⟩
  refine ⟨‖(q : F)‖⁻¹ • (q : F), norm_smul_inv_norm hq0, ?_, fun s hs => hq ⟨(s, ‖(q : F)‖), ?_⟩⟩
  · rw [real_inner_smul_left, real_inner_comm,
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 q.2, mul_zero]
  · -- From `u s + ‖q‖⁻¹ • q = 0`, the point `q` is `‖q‖ • (-u s)`.
    have hqs : (q : F) = ‖(q : F)‖ • -u s := by
      rw [← eq_neg_of_add_eq_zero_right hs, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.2 hq0), one_smul]
    refine Subtype.ext ?_
    simp only [g, Submodule.coe_smul,
      K.orthogonalProjectionOnto_mem_subspace_eq_self ⟨-u s, hmem s⟩]
    exact hqs.symm

/-- **Rotating a path of unit vectors back to its base value.** Let `u` be a `C^k` path, `k ≠ 0`,
of unit vectors orthogonal to `v`, in a real inner product space where the orthogonal complement
of `v` has dimension at least three. Then a `C^k` family `Q` of linear isometries, each fixing
`v`, carries `u s` to `u s₀` for every `s`, and `Q s` is the identity whenever `u s = u s₀`.

`Q s` composes four hyperplane reflections: a rotation in the plane of `u s` and an auxiliary unit
vector `p` (`TauCeti.exists_forall_add_ne_zero`), sending `u s` to `p`, followed by the inverse of
the rotation sending `u s₀` to `p`. -/
theorem exists_contDiff_linearIsometryEquiv_apply_eq {k : ℕ∞ω}
    (hk : k ≠ 0) {v : F} (hF : 2 < Module.finrank ℝ (ℝ ∙ v)ᗮ) {u : ℝ → F}
    (hu : ContDiff ℝ k u) (hu₁ : ∀ s, ‖u s‖ = 1) (hv : ∀ s, ⟪u s, v⟫ = 0) (s₀ : ℝ) :
    ∃ Q : ℝ → F ≃ₗᵢ[ℝ] F, ContDiff ℝ k (fun p : ℝ × F => Q p.1 p.2) ∧ (∀ s, Q s v = v) ∧
      (∀ s, Q s (u s) = u s₀) ∧ ∀ s, u s = u s₀ → ∀ x, Q s x = x := by
  obtain ⟨p, hp₁, hpv, hup⟩ := exists_forall_add_ne_zero hF (hu.differentiable hk) hv
  have hu₀ (s : ℝ) : u s ≠ 0 := fun h => by simpa [h] using hu₁ s
  let ρ : F → F ≃ₗᵢ[ℝ] F := fun c => (ℝ ∙ c)ᗮ.reflection
  refine ⟨fun s => ((ρ (u s)).trans (ρ (u s + p))).trans ((ρ (u s₀ + p)).trans (ρ (u s₀))),
    ?_, fun s => ?_, fun s => ?_, fun s hs x => ?_⟩
  · have h₁ := contDiff_reflection_orthogonal_singleton_apply (hu.comp contDiff_fst) contDiff_snd
      fun q : ℝ × F => hu₀ q.1
    have h₂ := contDiff_reflection_orthogonal_singleton_apply
      ((hu.comp contDiff_fst).add contDiff_const) h₁ fun q : ℝ × F => hup q.1
    have h₃ := contDiff_reflection_orthogonal_singleton_apply contDiff_const h₂ fun _ => hup s₀
    exact contDiff_reflection_orthogonal_singleton_apply contDiff_const h₃ fun _ => hu₀ s₀
  · have hfix {c : F} (hc : ⟪c, v⟫ = 0) : ρ c v = v :=
      reflection_orthogonal_singleton_eq_self_of_inner_eq_zero hc
    have hadd (s' : ℝ) : ⟪u s' + p, v⟫ = 0 := by rw [inner_add_left, hv, hpv, add_zero]
    simp only [LinearIsometryEquiv.trans_apply, hfix (hv s), hfix (hadd s), hfix (hadd s₀),
      hfix (hv s₀)]
  · simp only [LinearIsometryEquiv.trans_apply, ρ,
      Submodule.reflection_orthogonalComplement_singleton_eq_neg,
      reflection_orthogonal_singleton_add_apply_neg ((hu₁ s).trans hp₁.symm)]
    have h₃ := reflection_orthogonal_singleton_add_apply_neg (hp₁.trans (hu₁ s₀).symm)
    rw [add_comm p, map_neg] at h₃
    rw [neg_eq_iff_eq_neg.1 h₃, map_neg,
      Submodule.reflection_orthogonalComplement_singleton_eq_neg, neg_neg]
  · simp only [LinearIsometryEquiv.trans_apply, hs, ρ, Submodule.reflection_reflection]

end TauCeti

namespace LinearIsometryEquiv

open scoped RealInnerProductSpace ContDiff

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `e` is the time-one map of an analytic path of linear isometries starting at the identity. -/
private def IsJoinedToOne (e : F ≃ₗᵢ[ℝ] F) : Prop :=
  ∃ R : ℝ → F ≃ₗᵢ[ℝ] F, ContDiff ℝ ω (fun p : ℝ × F => R p.1 p.2) ∧ (∀ x, R 0 x = x) ∧
    ∀ x, R 1 x = e x

/-- The determinant of a product of linear isometries is the product of their determinants. -/
private theorem det_toLinearEquiv_mul (e f : F ≃ₗᵢ[ℝ] F) :
    (LinearEquiv.det (e * f).toLinearEquiv : ℝ) =
      LinearEquiv.det e.toLinearEquiv * LinearEquiv.det f.toLinearEquiv := by
  simp [mul_def]

/-- The identity is joined to itself by the constant path. -/
private theorem isJoinedToOne_one : IsJoinedToOne (1 : F ≃ₗᵢ[ℝ] F) :=
  ⟨fun _ => 1, by simpa using contDiff_snd, fun _ => rfl, fun _ => rfl⟩

/-- Paths from the identity multiply pointwise. -/
private theorem IsJoinedToOne.mul {e f : F ≃ₗᵢ[ℝ] F} (he : IsJoinedToOne e)
    (hf : IsJoinedToOne f) : IsJoinedToOne (e * f) := by
  obtain ⟨R, hR, hR₀, hR₁⟩ := he
  obtain ⟨S, hS, hS₀, hS₁⟩ := hf
  refine ⟨fun t => R t * S t, ?_, fun x => ?_, fun x => ?_⟩
  · simp only [coe_mul, Function.comp_apply]
    exact hR.comp (contDiff_fst.prodMk hS)
  · simp [hR₀, hS₀]
  · simp [hR₁, hS₁]

/-- A path from the identity can be conjugated by any linear isometry. -/
private theorem IsJoinedToOne.conj {e : F ≃ₗᵢ[ℝ] F} (he : IsJoinedToOne e) (g : F ≃ₗᵢ[ℝ] F) :
    IsJoinedToOne (g * e * g⁻¹) := by
  obtain ⟨R, hR, hR₀, hR₁⟩ := he
  refine ⟨fun t => g * R t * g⁻¹, ?_, fun x => ?_, fun x => ?_⟩
  · simp only [coe_mul, coe_inv, Function.comp_apply]
    exact g.toContinuousLinearEquiv.contDiff.comp
      (hR.comp (contDiff_fst.prodMk (g.symm.toContinuousLinearEquiv.contDiff.comp contDiff_snd)))
  · simp [hR₀]
  · simp [hR₁]

/-- The product of the reflections in the hyperplanes orthogonal to two unit vectors `a` and `b`
is joined to the identity, by moving the normal of the second reflection from `a` to `b` along the
segment between them. That segment avoids `0` unless `b = -a`, when the product is the
identity. -/
private theorem isJoinedToOne_reflection_mul_reflection_of_norm_eq_one {a b : F} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) : IsJoinedToOne ((ℝ ∙ b)ᗮ.reflection * (ℝ ∙ a)ᗮ.reflection) := by
  by_cases hab : b = -a
  · have hspan : (ℝ ∙ b) = ℝ ∙ a := by
      rw [hab, ← neg_one_smul ℝ a, Submodule.span_singleton_smul_eq isUnit_one.neg]
    simp only [hspan, Submodule.reflection_mul_reflection]
    exact isJoinedToOne_one
  set c : ℝ → F := fun t => (1 - t) • a + t • b
  have hc (t : ℝ) : c t ≠ 0 := by
    intro h
    -- Then `t • b = (t - 1) • a`, so `|t| = |t - 1|`, which forces `t = 1 / 2` and `b = -a`.
    have h' : t • b = (t - 1) • a := by
      simp only [c] at h
      linear_combination (norm := module) h
    have hn := congrArg norm h'
    rw [norm_smul, norm_smul, ha, hb, Real.norm_eq_abs, Real.norm_eq_abs] at hn
    have ht : t = 1 / 2 := by
      rcases abs_eq_abs.mp (by simpa using hn) with h | h <;> linarith
    subst ht
    exact hab (by linear_combination (norm := module) (2 : ℝ) • h')
  refine ⟨fun t => (ℝ ∙ a)ᗮ.reflection.trans (ℝ ∙ c t)ᗮ.reflection, ?_, fun x => ?_, fun x => ?_⟩
  · exact TauCeti.contDiff_reflection_trans_reflection (c := c)
      (((contDiff_const.sub contDiff_id).smul contDiff_const).add (contDiff_id.smul contDiff_const))
      hc
  · simp [c]
  · simp [c]

/-- The product of the reflections in the hyperplanes orthogonal to two nonzero vectors is joined
to the identity. -/
private theorem isJoinedToOne_reflection_mul_reflection {u w : F} (hu : u ≠ 0) (hw : w ≠ 0) :
    IsJoinedToOne ((ℝ ∙ u)ᗮ.reflection * (ℝ ∙ w)ᗮ.reflection) := by
  -- Both reflections only depend on the lines spanned by `u` and `w`, so normalize them.
  have hspan {v : F} (hv : v ≠ 0) : ∃ a, ‖a‖ = 1 ∧ (ℝ ∙ v) = ℝ ∙ a :=
    ⟨‖v‖⁻¹ • v, norm_smul_inv_norm hv,
      (Submodule.span_singleton_smul_eq (inv_ne_zero (norm_ne_zero_iff.2 hv)).isUnit v).symm⟩
  obtain ⟨a, ha, hua⟩ := hspan hu
  obtain ⟨b, hb, hwb⟩ := hspan hw
  simp only [hua, hwb]
  exact isJoinedToOne_reflection_mul_reflection_of_norm_eq_one hb ha

/-- A product of hyperplane reflections of determinant `1` is joined to the identity, and one of
determinant `-1` is joined to the identity after multiplying by any further hyperplane
reflection. -/
private theorem isJoinedToOne_list_prod [FiniteDimensional ℝ F] (l : List F) :
    ((LinearEquiv.det (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod.toLinearEquiv : ℝ) = 1 →
        IsJoinedToOne (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod) ∧
      ((LinearEquiv.det (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod.toLinearEquiv : ℝ) = -1 →
        ∀ a : F, a ≠ 0 →
          IsJoinedToOne ((l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod * (ℝ ∙ a)ᗮ.reflection)) := by
  induction l with
  | nil =>
    refine ⟨fun _ => isJoinedToOne_one, fun h => ?_⟩
    simp [one_def] at h
    linarith
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons]
    set φ := (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod
    set g := (ℝ ∙ v)ᗮ.reflection
    by_cases hv : v = 0
    · have hg : g = 1 := by
        ext x
        simp only [g]
        rw [TauCeti.reflection_orthogonal_singleton_apply_div_norm_sq, hv]
        simp
      simpa [hg] using ih
    have hdet : (LinearEquiv.det (g * φ).toLinearEquiv : ℝ) =
        -LinearEquiv.det φ.toLinearEquiv := by
      rw [det_toLinearEquiv_mul, TauCeti.linearEquiv_det_reflection_orthogonal_singleton hv,
        neg_one_mul]
    rw [hdet]
    refine ⟨fun h => ?_, fun h a ha => ?_⟩
    · -- `g * φ` is the conjugate of `φ * g` by `g`.
      have := (ih.2 (by linarith) v hv).conj g
      rwa [show g * (φ * g) * g⁻¹ = g * φ by group] at this
    · -- `g * φ * r_a` is the conjugate of `φ` by `g`, times `g * r_a`.
      have := ((ih.1 (by linarith)).conj g).mul (isJoinedToOne_reflection_mul_reflection hv ha)
      rwa [show g * φ * g⁻¹ * (g * (ℝ ∙ a)ᗮ.reflection) = g * φ * (ℝ ∙ a)ᗮ.reflection by group]
        at this

/-- **Linear isometries of determinant `1` are joined to the identity.** A linear isometry of a
finite-dimensional real inner product space of determinant `1` is the time-one map of an analytic
path of linear isometries starting at the identity. -/
theorem exists_contDiff_path_of_det_eq_one [FiniteDimensional ℝ F] (e : F ≃ₗᵢ[ℝ] F)
    (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = 1) :
    ∃ R : ℝ → F ≃ₗᵢ[ℝ] F, ContDiff ℝ ω (fun p : ℝ × F => R p.1 p.2) ∧ (∀ x, R 0 x = x) ∧
      ∀ x, R 1 x = e x := by
  obtain ⟨l, -, rfl⟩ := e.reflections_generate_dim
  exact (isJoinedToOne_list_prod l).1 he

end LinearIsometryEquiv

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace reflection, viewed as a bounded operator, squares to the identity. -/
@[simp] theorem reflection_mul_self (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (U.reflection : E →L[𝕜] E) * (U.reflection : E →L[𝕜] E) = 1 := by
  ext x
  simpa only [mul_apply_eq_comp, one_apply_eq_self, LinearIsometryEquiv.coe_coe''] using
    U.reflection_reflection x

/-- A subspace reflection is self-adjoint as a bounded operator. -/
theorem isSelfAdjoint_reflection [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint (U.reflection : E →L[𝕜] E) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', LinearIsometryEquiv.adjoint_eq_symm,
    reflection_symm]

/-- A subspace reflection is a unitary bounded operator. -/
theorem reflection_mem_unitary [CompleteSpace E]
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (U.reflection : E →L[𝕜] E) ∈ unitary (E →L[𝕜] E) := by
  simpa only [Unitary.coe_symm_linearIsometryEquiv_apply] using
    (Unitary.linearIsometryEquiv.symm U.reflection).property

/-- Full off-diagonality is anticommutation with the source reflection.

Adapted from `reflection_anticommutes_of_maps_orthogonal` in
`DavisKahan/InfiniteDimensional/TanTwoTheta/QuarterAcuteFormGap.lean`, Kitware DKPS
(Jon Crall, OpenAI GPT-5.6 Thinking and Claude Opus 5; Apache-2.0). -/
theorem reflection_mul_eq_neg_mul_of_maps_orthogonal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] (H : E →L[𝕜] E)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ)
    (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U) :
    (U.reflection : E →L[𝕜] E) * H = -(H * (U.reflection : E →L[𝕜] E)) := by
  apply ContinuousLinearMap.ext
  intro x
  let p : E := U.starProjection x
  let m : E := x - U.starProjection x
  have hp : p ∈ U := U.starProjection_apply_mem x
  have hm : m ∈ Uᗮ := U.sub_starProjection_mem_orthogonal x
  have hxpm : x = p + m := by
    simpa only [p, m, starProjection_orthogonal_val] using
      (U.starProjection_add_starProjection_orthogonal x).symm
  have hHp : H p ∈ Uᗮ := hHU p hp
  have hHm : H m ∈ U := hHUperp m hm
  have hJp : (U.reflection : E →L[𝕜] E) p = p := by
    simpa only [LinearIsometryEquiv.coe_coe''] using U.reflection_mem_subspace_eq_self hp
  have hJm : (U.reflection : E →L[𝕜] E) m = -m := by
    simpa only [LinearIsometryEquiv.coe_coe''] using
      U.reflection_mem_subspace_orthogonalComplement_eq_neg hm
  have hJHp : (U.reflection : E →L[𝕜] E) (H p) = -H p := by
    simpa only [LinearIsometryEquiv.coe_coe''] using
      U.reflection_mem_subspace_orthogonalComplement_eq_neg hHp
  have hJHm : (U.reflection : E →L[𝕜] E) (H m) = H m := by
    simpa only [LinearIsometryEquiv.coe_coe''] using U.reflection_mem_subspace_eq_self hHm
  simp only [mul_apply_eq_comp, neg_apply]
  calc
    (U.reflection : E →L[𝕜] E) (H x) = (U.reflection : E →L[𝕜] E) (H p + H m) := by
      rw [hxpm, map_add]
    _ = (U.reflection : E →L[𝕜] E) (H p) + (U.reflection : E →L[𝕜] E) (H m) := map_add _ _ _
    _ = -(H p) + H m := by rw [hJHp, hJHm]
    _ = -(H (p - m)) := by
      have hmap : H (p - m) = H p - H m := map_sub H p m
      rw [hmap]
      abel
    _ = -(H ((U.reflection : E →L[𝕜] E) x)) := by
      have hJx : (U.reflection : E →L[𝕜] E) x = p - m := by
        rw [hxpm, map_add, hJp, hJm]
        module
      rw [hJx]

/-- The symmetric product of two subspace reflections is
`R_V R_U + R_U R_V = 2 I - 4 (P_U - P_V)²`.

Extracted from the reflection-product calculation in
`DavisKahan/InfiniteDimensional/TanTwoTheta/QuarterAcuteFormGap.lean`, Kitware DKPS
(Jon Crall, OpenAI GPT-5.6 Thinking and Claude Opus 5; Apache-2.0). -/
theorem reflection_mul_add_mul_reflection
    (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (V.reflection : E →L[𝕜] E) * (U.reflection : E →L[𝕜] E) +
        (U.reflection : E →L[𝕜] E) * (V.reflection : E →L[𝕜] E) =
      (2 : 𝕜) • (1 : E →L[𝕜] E) -
        (4 : 𝕜) • ((U.starProjection - V.starProjection) *
          (U.starProjection - V.starProjection)) := by
  simp only [coe_reflection, show (4 : 𝕜) = 2 + 2 by norm_num, add_smul, two_smul]
  noncomm_ring [U.isIdempotentElem_starProjection.eq, V.isIdempotentElem_starProjection.eq]

end Submodule
