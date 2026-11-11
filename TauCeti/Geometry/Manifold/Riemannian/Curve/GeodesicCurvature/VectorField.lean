/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal

/-!
# The geodesic curvature of the integral curves of a vector field

On an oriented Riemannian surface, let `X` be a vector field and `J` the rotation by `+π/2` in the
oriented tangent planes. The function

`κ_X = ⟪∇_X X, J X⟫ / ‖X‖³`

is the signed geodesic curvature, relative to the oriented unit normal, of the curves which run
along `X` in its direction: if the velocity of a curve `γ` is `a • X ∘ γ` near `t`, with `a` a
positive function differentiable at `t`, then the geodesic curvature of `γ` at `t` is
`κ_X (γ t)`. Indeed `D_t γ' = a' X + a² ∇_X X`, the first term is orthogonal to `J X`, and the
factors `a²` and `a³` coming from the acceleration, the normal and the speed cancel. The speed of
the curve is thus irrelevant, and `κ_X` only depends on `X` up to multiplication by positive
functions.

This computes the geodesic curvature of a family of curves tangent to a vector field, such as the
parallel arcs of a normal strip, from the field alone.

## Main definitions and results

* `TauCeti.Manifold.fieldGeodesicCurvature`: the function `κ_X = ⟪∇_X X, J X⟫ / ‖X‖³`.
* `TauCeti.Manifold.geodesicCurvature_eq_fieldGeodesicCurvature`: a curve whose velocity is a
  positive multiple of `X` near `t` has geodesic curvature `κ_X (γ t)` at `t`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 9.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The **geodesic curvature of a vector field** `X` on an oriented surface,
`κ_X = ⟪∇_X X, J X⟫ / ‖X‖³`, where `∇` is the Levi-Civita connection and `J` the rotation by
`+π/2`. It is the geodesic curvature, relative to the oriented unit normal, of the curves whose
velocity is a positive multiple of `X`; see
`TauCeti.Manifold.geodesicCurvature_eq_fieldGeodesicCurvature`. -/
def fieldGeodesicCurvature (o : Orientation I M (Fin 2)) (X : Π x : M, TangentSpace I x)
    (x : M) : ℝ :=
  letI := o.fact_finrank_tangentSpace x
  ⟪leviCivitaConnection I M X x (X x), (o.orientationAt x).rightAngleRotation (X x)⟫_ℝ /
    ‖X x‖ ^ 3

/-- The defining formula for `fieldGeodesicCurvature`. -/
theorem fieldGeodesicCurvature_def (o : Orientation I M (Fin 2))
    (X : Π x : M, TangentSpace I x) (x : M) :
    fieldGeodesicCurvature o X x =
      (letI := o.fact_finrank_tangentSpace x
      ⟪leviCivitaConnection I M X x (X x), (o.orientationAt x).rightAngleRotation (X x)⟫_ℝ /
        ‖X x‖ ^ 3) :=
  (rfl)

/-- **The geodesic curvature of a curve along a vector field.** If near `t` the velocity of a
curve `γ` is `a • X ∘ γ`, where `X` is a vector field differentiable at `γ t` and nonzero there
and `a` is a function differentiable at `t` with `a t > 0`, then the geodesic curvature of `γ`
at `t` relative to its oriented unit normal is `κ_X (γ t)`. -/
theorem geodesicCurvature_eq_fieldGeodesicCurvature (o : Orientation I M (Fin 2))
    {X : Π x : M, TangentSpace I x} {γ : ℝ → M} {a : ℝ → ℝ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) (hX : MDiffAt (T% X) (γ t))
    (ha : DifferentiableAt ℝ a t) (hapos : 0 < a t) (hXne : X (γ t) ≠ 0)
    (hvel : (fun r ↦ curveVelocity I γ r) =ᶠ[𝓝 t] fun r ↦ a r • X (γ r)) :
    geodesicCurvature γ (orientedUnitNormal o γ) t = fieldGeodesicCurvature o X (γ t) := by
  let := o.fact_finrank_tangentSpace (γ t)
  have hcoord : DifferentiableAt ℝ (sectionCoord (F := E) γ (fun r ↦ X (γ r)) (γ t)) t :=
    differentiableAt_sectionCoord γ (fun r ↦ X (γ r)) (hX.comp t hγ)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
  have hv : curveVelocity I γ t = a t • X (γ t) := hvel.self_of_nhds
  have hacc : acceleration (leviCivitaConnection I M) γ t =
      deriv a t • X (γ t) + a t • leviCivitaConnection I M X (γ t) (a t • X (γ t)) := by
    rw [acceleration_def, alongCurve_congr _ γ (fun r ↦ curveVelocity I γ r) hvel,
      alongCurve_smul _ γ (fun r ↦ X (γ r)) a ha hcoord,
      alongCurve_pullback _ γ X (hasMFDerivAt_curveVelocity hγ) hX, hv]
  have horth : ⟪X (γ t), (o.orientationAt (γ t)).rightAngleRotation (X (γ t))⟫_ℝ = 0 := by
    rw [real_inner_comm, (o.orientationAt (γ t)).inner_rightAngleRotation_self]
  rw [geodesicCurvature_def, orientedUnitNormal_apply, NormedSpace.normalize, map_smul, hacc, hv,
    fieldGeodesicCurvature_def, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hapos, map_smul]
  simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, horth, mul_zero,
    zero_add]
  field_simp [hapos.ne', norm_ne_zero_iff.mpr hXne]

end TauCeti.Manifold
