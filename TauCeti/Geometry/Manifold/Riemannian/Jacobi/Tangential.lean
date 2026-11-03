/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.ConstantSpeed
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# Tangential and normal Jacobi fields

Along a geodesic `γ` the velocity field `γ'` is parallel and `R(γ', γ')γ' = 0`, so every field
`(α + β t) γ'(t)` is a Jacobi field. These are the *tangential* Jacobi fields. Conversely, the
component of an arbitrary Jacobi field `J` along the geodesic is affine in the parameter: from
`D²J = -R(J, γ')γ'` and the skew-symmetry of `⟨R(J, γ')·, ·⟩` the function `⟨DJ, γ'⟩` is
constant, hence

`⟨J(t), γ'(t)⟩ = ⟨J(a), γ'(a)⟩ + (t - a) ⟨DJ(a), γ'(a)⟩`

on every preconnected parameter set. Since a geodesic has constant speed, the orthogonal
projection of `J` onto the line spanned by `γ'` is therefore a tangential Jacobi field, and the
remaining component `J - proj J` is a Jacobi field orthogonal to `γ'`. This splits the Jacobi
fields along a geodesic into tangential fields, which only reparametrize the geodesic, and normal
fields, which carry its geometry.

For a constant geodesic the velocity vanishes, every tangential field is zero and the splitting
is trivial; the statements below need no nonconstancy hypothesis. A Jacobi field is normal
everywhere exactly when it and its covariant derivative are orthogonal to `γ'` at one parameter.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.isJacobiFieldOn_affine_smul_curveVelocityWithin`: the fields
  `(α + β t) γ'(t)` are Jacobi fields.
* `TauCeti.Manifold.IsJacobiFieldOn.inner_alongCurveWithin_curveVelocityWithin_eq`: `⟨DJ, γ'⟩` is
  constant along the geodesic.
* `TauCeti.Manifold.IsJacobiFieldOn.inner_curveVelocityWithin_eq`: `⟨J, γ'⟩` is affine in the
  parameter.
* `TauCeti.Manifold.IsJacobiFieldOn.forall_inner_curveVelocityWithin_eq_zero_iff`: a Jacobi field is
  normal everywhere if and only if `J` and `DJ` are normal at one parameter.
* `TauCeti.Manifold.IsJacobiFieldOn.starProjection_singleton_eq`: the orthogonal projection of a
  Jacobi field onto the velocity line is `(α + β t) γ'(t)` with explicit coefficients.
* `TauCeti.Manifold.IsJacobiFieldOn.isJacobiFieldOn_starProjection_singleton` and
  `TauCeti.Manifold.IsJacobiFieldOn.isJacobiFieldOn_sub_starProjection_singleton`: the tangential
  and normal components of a Jacobi field are Jacobi fields.
* `TauCeti.Manifold.IsJacobiFieldOn.exists_eq_affine_smul_add`: every Jacobi field is a tangential
  Jacobi field `(α + β t) γ'(t)` plus a Jacobi field orthogonal to `γ'`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10 (tangential and normal Jacobi fields, Proposition 10.7 and Corollary 10.8).
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Chapter 5, Proposition 3.6.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a t : ℝ}

/-- **Tangential Jacobi fields.** Along a geodesic, the velocity scaled by an affine function
`α + β t` of the parameter is a Jacobi field. -/
theorem IsGeodesicCurveOn.isJacobiFieldOn_affine_smul_curveVelocityWithin [I.Boundaryless]
    (h : IsGeodesicCurveOn I γ s) (α β : ℝ) :
    IsJacobiFieldOn I γ (fun r ↦ (α + β * r) • curveVelocityWithin I γ s r) s := by
  have hf : ContDiff ℝ 2 fun r : ℝ ↦ α + β * r := by fun_prop
  have hfirst : ∀ r ∈ s, alongCurveWithin (leviCivitaConnection I M) γ
      (fun r ↦ (α + β * r) • curveVelocityWithin I γ s r) s r =
        β • curveVelocityWithin I γ s r := by
    intro r hr
    have hderiv : HasDerivAt (fun r : ℝ ↦ α + β * r) β r := by
      simpa using ((hasDerivAt_id r).const_mul β).const_add α
    rw [h.alongCurveWithin_smul_curveVelocityWithin hr
        hderiv.differentiableAt.differentiableWithinAt,
      hderiv.hasDerivWithinAt.derivWithin (h.uniqueDiffOn r hr)]
  have hlift : curveVelocityLiftWithin I γ s =
      fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ s r) :=
    funext (curveVelocityLiftWithin_apply γ s)
  refine ⟨h, ?_, fun r hr ↦ ?_⟩
  · have hv : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2 (curveVelocityLiftWithin I γ s) s :=
      h.contMDiffOn_curveVelocityLiftWithin_infty.of_le (by simp)
    rw [hlift] at hv
    exact hf.contMDiff.contMDiffOn.smul_totalSpace hv
  · rw [alongCurveWithin_congr _ γ _
        (Filter.mem_of_superset self_mem_nhdsWithin (hfirst ·)) (hfirst r hr),
      alongCurveWithin_const_smul, ← accelerationWithin_def, h.accelerationWithin_eq_zero r hr]
    simp [curvatureTensor_self]

/-- The derivative of `⟨DJ, γ'⟩` vanishes: `D²J = -R(J, γ')γ'` is orthogonal to `γ'` and `γ'` is
parallel. -/
private theorem IsJacobiFieldOn.hasDerivWithinAt_inner_alongCurveWithin_curveVelocityWithin
    (hJ : IsJacobiFieldOn I γ J s) (ht : t ∈ s) :
    HasDerivWithinAt (fun r ↦ inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s r)
      (curveVelocityWithin I γ s r)) 0 s t := by
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hγ := hJ.isGeodesicCurveOn
  have hprod := hm.hasDerivWithinAt_inner_alongCurveWithin (hJ.uniqueDiffOn t ht)
    (hγ.mdifferentiableOn t ht) (hJ.differentiableWithinAt_sectionCoord_alongCurveWithin ht)
    (differentiableWithinAt_sectionCoord_curveVelocityWithin γ hγ.uniqueDiffOn hγ.contMDiffOn ht
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  refine hprod.congr_deriv ?_
  have hskew := hm.inner_curvatureTensor_eq_neg (γ t) (J t) (curveVelocityWithin I γ s t)
    (curveVelocityWithin I γ s t) (curveVelocityWithin I γ s t)
  rw [real_inner_comm (curveVelocityWithin I γ s t)] at hskew
  rw [hJ.alongCurveWithin_alongCurveWithin_eq ht, ← accelerationWithin_def,
    hγ.accelerationWithin_eq_zero t ht, inner_neg_left, inner_zero_right,
    real_inner_comm (curveVelocityWithin I γ s t)]
  linarith

/-- The derivative of `⟨J, γ'⟩` is `⟨DJ, γ'⟩`, since `γ'` is parallel. -/
private theorem IsJacobiFieldOn.hasDerivWithinAt_inner_curveVelocityWithin
    (hJ : IsJacobiFieldOn I γ J s) (ht : t ∈ s) :
    HasDerivWithinAt (fun r ↦ inner ℝ (J r) (curveVelocityWithin I γ s r))
      (inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s t)
        (curveVelocityWithin I γ s t)) s t := by
  have hm := isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hγ := hJ.isGeodesicCurveOn
  have hprod := hm.hasDerivWithinAt_inner_alongCurveWithin (hJ.uniqueDiffOn t ht)
    (hγ.mdifferentiableOn t ht) (hJ.differentiableWithinAt_sectionCoord ht)
    (differentiableWithinAt_sectionCoord_curveVelocityWithin γ hγ.uniqueDiffOn hγ.contMDiffOn ht
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  refine hprod.congr_deriv ?_
  rw [← accelerationWithin_def, hγ.accelerationWithin_eq_zero t ht, inner_zero_right, add_zero]

/-- The inner product of the covariant derivative of a Jacobi field with the velocity of its
geodesic is constant on a preconnected parameter set. -/
theorem IsJacobiFieldOn.inner_alongCurveWithin_curveVelocityWithin_eq
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) {b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s a) (curveVelocityWithin I γ s a) =
      inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s b)
        (curveVelocityWithin I γ s b) := by
  have h := (Real.convex_iff_isPreconnected.2 hs).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr ↦ hJ.hasDerivWithinAt_inner_alongCurveWithin_curveVelocityWithin hr)
    (C := 0) (fun _ _ ↦ by simp) hb ha
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  exact h

/-- **The tangential component of a Jacobi field is affine.** On a preconnected parameter set,
`⟨J(t), γ'(t)⟩ = ⟨J(a), γ'(a)⟩ + (t - a) ⟨DJ(a), γ'(a)⟩`. -/
theorem IsJacobiFieldOn.inner_curveVelocityWithin_eq
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) (ha : a ∈ s) (ht : t ∈ s) :
    inner ℝ (J t) (curveVelocityWithin I γ s t) =
      inner ℝ (J a) (curveVelocityWithin I γ s a) +
        (t - a) * inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s a)
          (curveVelocityWithin I γ s a) := by
  set c := inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s a)
    (curveVelocityWithin I γ s a)
  have hderiv : ∀ r ∈ s, HasDerivWithinAt
      (fun r ↦ inner ℝ (J r) (curveVelocityWithin I γ s r) - (r - a) * c) 0 s r := by
    intro r hr
    have h₁ := hJ.hasDerivWithinAt_inner_curveVelocityWithin hr
    rw [hJ.inner_alongCurveWithin_curveVelocityWithin_eq hs hr ha] at h₁
    exact (h₁.sub (((hasDerivAt_id' r).sub_const a).mul_const c).hasDerivWithinAt).congr_deriv
      (by simp [c])
  have h := (Real.convex_iff_isPreconnected.2 hs).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv (C := 0) (fun _ _ ↦ by simp) ha ht
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, sub_self, zero_mul, sub_zero] at h
  linarith

/-- **Normal Jacobi fields.** A Jacobi field on a preconnected parameter set is orthogonal to the
velocity of its geodesic everywhere if and only if the field and its covariant derivative are
orthogonal to the velocity at one parameter. -/
theorem IsJacobiFieldOn.forall_inner_curveVelocityWithin_eq_zero_iff
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) (ha : a ∈ s) :
    (∀ t ∈ s, inner ℝ (J t) (curveVelocityWithin I γ s t) = 0) ↔
      inner ℝ (J a) (curveVelocityWithin I γ s a) = 0 ∧
        inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s a)
          (curveVelocityWithin I γ s a) = 0 := by
  refine ⟨fun h ↦ ⟨h a ha, ?_⟩, fun ⟨h₀, h₁⟩ t ht ↦ by
    rw [hJ.inner_curveVelocityWithin_eq hs ha ht, h₀, h₁, mul_zero, add_zero]⟩
  have hzero : HasDerivWithinAt (fun r ↦ inner ℝ (J r) (curveVelocityWithin I γ s r)) 0 s a :=
    (hasDerivWithinAt_const a s (0 : ℝ)).congr_of_mem (fun r hr ↦ h r hr) ha
  exact (hJ.uniqueDiffOn a ha).eq_deriv _ (hJ.hasDerivWithinAt_inner_curveVelocityWithin ha) hzero

/-- The orthogonal projection of a Jacobi field onto the line spanned by the velocity is the
tangential field with the affine coefficient
`(⟨J(a), γ'(a)⟩ + (t - a) ⟨DJ(a), γ'(a)⟩) / ‖γ'(a)‖²`, on a preconnected parameter set. -/
theorem IsJacobiFieldOn.starProjection_singleton_eq
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) (ha : a ∈ s) (ht : t ∈ s) :
    (ℝ ∙ curveVelocityWithin I γ s t).starProjection (J t) =
      ((inner ℝ (J a) (curveVelocityWithin I γ s a) +
          (t - a) * inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s a)
            (curveVelocityWithin I γ s a)) /
        ‖curveVelocityWithin I γ s a‖ ^ 2) • curveVelocityWithin I γ s t := by
  rw [Submodule.starProjection_singleton, real_inner_comm,
    hJ.inner_curveVelocityWithin_eq hs ha ht,
    hJ.isGeodesicCurveOn.norm_curveVelocityWithin_eq hs ht ha, RCLike.ofReal_real_eq_id, id_eq]

/-- The tangential component of a Jacobi field, its orthogonal projection onto the line spanned by
the velocity, is a Jacobi field on a preconnected parameter set. -/
theorem IsJacobiFieldOn.isJacobiFieldOn_starProjection_singleton [I.Boundaryless]
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) :
    IsJacobiFieldOn I γ
      (fun r ↦ (ℝ ∙ curveVelocityWithin I γ s r).starProjection (J r)) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact (isJacobiFieldOn_zero hJ.isGeodesicCurveOn).congr (by simp)
  set c₀ := inner ℝ (J a) (curveVelocityWithin I γ s a)
  set c₁ := inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s a)
    (curveVelocityWithin I γ s a)
  set n := ‖curveVelocityWithin I γ s a‖ ^ 2
  refine (hJ.isGeodesicCurveOn.isJacobiFieldOn_affine_smul_curveVelocityWithin
    ((c₀ - a * c₁) / n) (c₁ / n)).congr fun r hr ↦ ?_
  rw [hJ.starProjection_singleton_eq hs ha hr]
  congr 1
  ring

/-- The normal component of a Jacobi field, the field minus its orthogonal projection onto the
line spanned by the velocity, is a Jacobi field on a preconnected parameter set. It is orthogonal
to the velocity by `Submodule.sub_starProjection_mem_orthogonal`. -/
theorem IsJacobiFieldOn.isJacobiFieldOn_sub_starProjection_singleton [I.Boundaryless]
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) :
    IsJacobiFieldOn I γ
      (fun r ↦ J r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (J r)) s :=
  (hJ.add ((hJ.isJacobiFieldOn_starProjection_singleton hs).const_smul (-1))).congr fun r _ ↦ by
    simp [sub_eq_add_neg]

/-- **Splitting of Jacobi fields.** On a preconnected parameter set, every Jacobi field is the sum
of a tangential Jacobi field `(α + β t) γ'(t)` and a Jacobi field orthogonal to the velocity. -/
theorem IsJacobiFieldOn.exists_eq_affine_smul_add [I.Boundaryless]
    (hJ : IsJacobiFieldOn I γ J s) (hs : IsPreconnected s) :
    ∃ α β : ℝ, ∃ N : ∀ t, TangentSpace I (γ t), IsJacobiFieldOn I γ N s ∧
      (∀ t ∈ s, inner ℝ (N t) (curveVelocityWithin I γ s t) = 0) ∧
      ∀ t ∈ s, J t = (α + β * t) • curveVelocityWithin I γ s t + N t := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, 0, J, hJ, by simp, by simp⟩
  set c₀ := inner ℝ (J a) (curveVelocityWithin I γ s a)
  set c₁ := inner ℝ (alongCurveWithin (leviCivitaConnection I M) γ J s a)
    (curveVelocityWithin I γ s a)
  set n := ‖curveVelocityWithin I γ s a‖ ^ 2
  refine ⟨(c₀ - a * c₁) / n, c₁ / n, _, hJ.isJacobiFieldOn_sub_starProjection_singleton hs,
    fun t _ ↦ Submodule.starProjection_inner_eq_zero _ _ (Submodule.mem_span_singleton_self _),
    fun t ht ↦ ?_⟩
  rw [hJ.starProjection_singleton_eq hs ha ht]
  have : (c₀ - a * c₁) / n + c₁ / n * t = (c₀ + (t - a) * c₁) / n := by ring
  rw [this, add_sub_cancel]

end TauCeti.Manifold
