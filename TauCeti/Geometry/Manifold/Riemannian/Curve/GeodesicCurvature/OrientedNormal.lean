/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature
public import TauCeti.Geometry.Manifold.Riemannian.Curve.OrientedNormal
import TauCeti.Geometry.Manifold.Riemannian.Curve.GeodesicCurvature.Reparametrization
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Signed geodesic curvature on oriented surfaces

The oriented area of the velocity and acceleration divided by the cubed speed gives signed
geodesic curvature relative to the oriented unit normal. This expression yields `C^n` regularity
at regular `C^(n+2)` parameters, in particular continuity at regular `C²` parameters, and allows
comparison of curves agreeing near a parameter. Periodic
curves have periodic signed geodesic curvature without any regularity assumption.

## Main results

* `TauCeti.Manifold.geodesicCurvature_orientedUnitNormal`: the volume-form expression.
* `Filter.EventuallyEq.geodesicCurvature_orientedUnitNormal_eq`: invariance under germ equality.
* `Function.Periodic.geodesicCurvature_orientedUnitNormal`: periodicity of the curvature.
* `TauCeti.Manifold.contDiffAt_geodesicCurvature_orientedUnitNormal` and
  `TauCeti.Manifold.contDiff_geodesicCurvature_orientedUnitNormal`: `C^n` regularity for regular
  `C^(n+2)` curves with the corresponding manifold and metric regularity.
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
  exact h.geodesicCurvature_eq (h.orientedUnitNormal_eq o)

/-- The geodesic curvature of a periodic curve relative to its oriented unit normal is
periodic, with the same period. No regularity is assumed. -/
theorem _root_.Function.Periodic.geodesicCurvature_orientedUnitNormal
    {a : ℝ} (hper : Function.Periodic γ a) :
    Function.Periodic (geodesicCurvature γ (orientedUnitNormal o γ)) a :=
  hper.geodesicCurvature (hper.orientedUnitNormal o)

/-- On a `C^m` manifold with a `C^k` metric, the geodesic curvature of a regular
`C^(n+2)` curve relative to its oriented unit normal is `C^n` at the tested parameter, provided
`n + 2 ≤ m` and `n + 1 ≤ k`. -/
theorem contDiffAt_geodesicCurvature_orientedUnitNormal {n m k : ℕ∞ω}
    [IsManifold I m M]
    [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]
    (hm : n + 2 ≤ m) (hk : n + 1 ≤ k)
    (hγ : ContMDiffAt 𝓘(ℝ) I (n + 2) γ t) (hne : curveVelocity I γ t ≠ 0) :
    ContDiffAt ℝ n (geodesicCurvature γ (orientedUnitNormal o γ)) t := by
  have : IsManifold I (n + 1) M :=
    IsManifold.of_le (n := m) ((by gcongr; norm_num : n + 1 ≤ n + 2).trans hm)
  have : IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := k) (le_self_add.trans hk)
  have hV : ContMDiffAt 𝓘(ℝ) I.tangent n
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocity I γ r)) t := by
    rw [← funext (curveVelocityLift_apply (I := I) γ)]
    exact hγ.contMDiffAt_curveVelocityLift (by gcongr; norm_num)
  have hA := contMDiffAt_acceleration_leviCivitaConnection hm hk hγ
  have hvol := ((isSmoothForm_riemannianVolumeForm (n := n) o).contMDiff (γ t)).comp t
    (hγ.of_le (by simp))
  have heval := hvol.continuousAlternatingMap_bundle_apply
    (v := fun i r ↦ ![curveVelocity I γ r, acceleration (leviCivitaConnection I M) γ r] i)
    (fun i ↦ by
      fin_cases i
      · exact hV
      · exact hA)
  have hnorm : ContDiffAt ℝ n (fun r ↦ ‖curveVelocity I γ r‖) t := by
    have hinner : ContDiffAt ℝ n
        (fun r ↦ ⟪curveVelocity I γ r, curveVelocity I γ r⟫_ℝ) t := by
      rw [← contMDiffAt_iff_contDiffAt]
      exact ContMDiffAt.inner_bundle (IB := I) (E := TangentSpace I) (F := E) hV hV
    simpa only [norm_eq_sqrt_real_inner] using hinner.sqrt (inner_self_ne_zero.mpr hne)
  exact ((contMDiffAt_iff_contDiffAt.mp (Bundle.Trivial.contMDiffAt_mk_iff.mp heval).2).div
    (hnorm.pow 3) (pow_ne_zero 3 (norm_ne_zero_iff.mpr hne))).congr_of_eventuallyEq
    (Eventually.of_forall fun r ↦ geodesicCurvature_orientedUnitNormal o γ r)

/-- On a `C^m` manifold with a `C^k` metric, the geodesic curvature of a regular
`C^(n+2)` curve relative to its oriented unit normal is `C^n` when `n + 2 ≤ m` and `n + 1 ≤ k`. -/
theorem contDiff_geodesicCurvature_orientedUnitNormal {n m k : ℕ∞ω}
    [IsManifold I m M]
    [IsContMDiffRiemannianBundle I k E (fun x : M ↦ TangentSpace I x)]
    (hm : n + 2 ≤ m) (hk : n + 1 ≤ k)
    (hγ : ContMDiff 𝓘(ℝ) I (n + 2) γ) (hne : ∀ t, curveVelocity I γ t ≠ 0) :
    ContDiff ℝ n (geodesicCurvature γ (orientedUnitNormal o γ)) :=
  contDiff_iff_contDiffAt.mpr fun t ↦
    contDiffAt_geodesicCurvature_orientedUnitNormal o hm hk hγ.contMDiffAt (hne t)

/-- If a curve is `C²` at a parameter with nonzero velocity, its geodesic curvature relative to
the oriented unit normal is continuous there. -/
theorem continuousAt_geodesicCurvature_orientedUnitNormal (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hne : curveVelocity I γ t ≠ 0) :
    ContinuousAt (geodesicCurvature γ (orientedUnitNormal o γ)) t :=
  (contDiffAt_geodesicCurvature_orientedUnitNormal o (n := 0) (m := 2) (k := 1)
    (by norm_num) (by norm_num) hγ hne).continuousAt

/-- The geodesic curvature of a regular `C²` curve relative to its oriented unit normal is
continuous. -/
theorem continuous_geodesicCurvature_orientedUnitNormal (hγ : ContMDiff 𝓘(ℝ) I 2 γ)
    (hne : ∀ t, curveVelocity I γ t ≠ 0) :
    Continuous (geodesicCurvature γ (orientedUnitNormal o γ)) :=
  (contDiff_geodesicCurvature_orientedUnitNormal o (n := 0) (m := 2) (k := 1)
    (by norm_num) (by norm_num) hγ hne).continuous

end TauCeti.Manifold
