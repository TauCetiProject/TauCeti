/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal
import TauCeti.Geometry.Manifold.Riemannian.ArcLength
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity

/-!
# Signed geodesic curvature on oriented surfaces

The oriented area of the velocity and acceleration divided by the cubed speed gives signed
geodesic curvature relative to the oriented unit normal. This expression yields continuity at
regular `C²` parameters and allows comparison of curves agreeing near a parameter. Periodic
curves have periodic signed geodesic curvature without any regularity assumption.

## Main results

* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal`: the volume-form expression.
* `Filter.EventuallyEq.geodesicCurvature_orientedUnitNormal_eq`: invariance under germ equality.
* `Function.Periodic.geodesicCurvature_orientedUnitNormal`: periodicity of the curvature.
* `TauCeti.Manifold.continuousAt_geodesicCurvature_orientedUnitNormal` and
  `TauCeti.Manifold.continuous_geodesicCurvature_orientedUnitNormal`: continuity for regular
  `C²` curves, locally and globally.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 9.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ}

variable (o : Orientation I M (Fin 2))

/-- **The geodesic curvature relative to the oriented unit normal** is the oriented area of the
velocity and the covariant acceleration divided by the cubed speed,
`k_g = vol(γ', D_t γ') / ‖γ'‖³`. -/
theorem geodesicCurvature_orientedUnitNormal (γ : ℝ → M) (t : ℝ) :
    geodesicCurvature γ (orientedUnitNormal o γ) t =
      riemannianVolumeForm o (γ t) ![curveVelocity I γ t,
        acceleration (leviCivitaConnection I M) γ t] / ‖curveVelocity I γ t‖ ^ 3 := by
  let := o.fact_finrank_tangentSpace (γ t)
  rw [geodesicCurvature_def, orientedUnitNormal_apply, NormedSpace.normalize, map_smul,
    real_inner_smul_right, real_inner_comm,
    (o.orientationAt (γ t)).inner_rightAngleRotation_left, riemannianVolumeForm_apply,
    ← (o.orientationAt (γ t)).areaForm_to_volumeForm]
  ring

/-- Curves agreeing near a parameter have the same geodesic curvature relative to the oriented
unit normal there. -/
theorem _root_.Filter.EventuallyEq.geodesicCurvature_orientedUnitNormal_eq
    {η : ℝ → M} (h : γ =ᶠ[𝓝 t] η) (o : Orientation I M (Fin 2)) :
    geodesicCurvature γ (orientedUnitNormal o γ) t =
      geodesicCurvature η (orientedUnitNormal o η) t := by
  rw [geodesicCurvature_orientedUnitNormal, geodesicCurvature_orientedUnitNormal,
    h.self_of_nhds, h.curveVelocity_eq, h.acceleration_eq]

/-- The geodesic curvature of a periodic curve relative to its oriented unit normal is
periodic, with the same period. No regularity is assumed. -/
theorem _root_.Function.Periodic.geodesicCurvature_orientedUnitNormal
    {a : ℝ} (hper : Function.Periodic γ a) :
    Function.Periodic (geodesicCurvature γ (orientedUnitNormal o γ)) a := by
  intro t
  have hacc := acceleration_comp_add_const (leviCivitaConnection I M) γ a t
  rw [hper.funext] at hacc
  rw [TauCeti.Manifold.geodesicCurvature_orientedUnitNormal,
    TauCeti.Manifold.geodesicCurvature_orientedUnitNormal, hper t,
    hper.curveVelocity_add (I := I), ← hacc]

/-- If a curve is `C²` at a parameter with nonzero velocity, its geodesic curvature relative to
the oriented unit normal is continuous there. -/
theorem continuousAt_geodesicCurvature_orientedUnitNormal (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hne : curveVelocity I γ t ≠ 0) :
    ContinuousAt (geodesicCurvature γ (orientedUnitNormal o γ)) t := by
  have hV : ContMDiffAt 𝓘(ℝ) I.tangent 0
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocity I γ r)) t := by
    rw [← funext (curveVelocityLift_apply (I := I) γ)]
    exact hγ.contMDiffAt_curveVelocityLift (by norm_num)
  have hA := contMDiffAt_acceleration_leviCivitaConnection (n := 0) (m := 2) (k := 1)
    (by norm_num) (by norm_num) hγ
  -- Normalize the regularity indices required by the volume-form evaluation API.
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  have : ContMDiffVectorBundle (0 + 1) E (TangentSpace I : M → Type _) I := by
    simpa using (inferInstance : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I)
  have hvol := ((isSmoothForm_riemannianVolumeForm (n := 0) o).contMDiff (γ t)).comp t
    (hγ.of_le (by norm_num))
  have heval := hvol.continuousAlternatingMap_bundle_apply
    (v := fun i r ↦ ![curveVelocity I γ r, acceleration (leviCivitaConnection I M) γ r] i)
    (fun i ↦ by
      fin_cases i
      · exact hV
      · exact hA)
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 1) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  have hnorm := (hγ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).continuousAt_norm_curveVelocity
  exact ((contMDiffAt_totalSpace_iff.mp heval).2.continuousAt.div (hnorm.pow 3)
    (pow_ne_zero 3 (norm_ne_zero_iff.mpr hne))).congr
    (Eventually.of_forall fun r ↦ (geodesicCurvature_orientedUnitNormal o γ r).symm)

/-- The geodesic curvature of a regular `C²` curve relative to its oriented unit normal is
continuous. -/
theorem continuous_geodesicCurvature_orientedUnitNormal (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    (hne : ∀ t, curveVelocity I γ t ≠ 0) :
    Continuous (geodesicCurvature γ (orientedUnitNormal o γ)) :=
  continuous_iff_continuousAt.mpr fun t ↦
    continuousAt_geodesicCurvature_orientedUnitNormal o hγ.contMDiffAt (hne t)

end TauCeti.Manifold
