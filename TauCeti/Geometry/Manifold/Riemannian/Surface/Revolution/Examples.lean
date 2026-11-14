/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Surface.Revolution.Geodesic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Cylindrical geodesics and planar polar coordinates

Affine curves in the angular and height coordinates of the unit cylinder are native
geodesics for its induced metric. Planar polar coordinates give a contrasting nonconstant
metric with nonzero Christoffel symbols.
-/

public noncomputable section

open Bundle Manifold TopologicalSpace
open scoped ContDiff

namespace TauCeti.SurfaceOfRevolution.Examples

open TauCeti.Manifold

local notation "P" => ℝ × ℝ
local notation "IP" => 𝓘(ℝ, P)
local notation "U" => (⊤ : Opens P)

/-- The smooth metric induced by the standard unit-cylinder parametrization. -/
def cylinderMetric : ContMDiffRiemannianMetric IP ∞ P (fun p : U ↦ TangentSpace IP p) :=
  riemannianMetric (f := fun _ ↦ 1) (g := id) U (fun _ ↦ contDiffAt_const)
    (fun _ ↦ contDiffAt_id) (fun _ ↦ one_ne_zero)
    (fun p ↦ by simp [profileSpeedSq_def])

/-- The first fundamental form of the cylinder is the metric of its unrolled plane. -/
theorem cylinderMetric_inner (p : U) (w z : TangentSpace IP p) :
    cylinderMetric.inner p w z = metric (fun _ ↦ 1) id p.val
      (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p w))
      (NormedSpace.fromTangentSpace p.val (tangentSpaceOpenEquiv (I := IP) p z)) := by
  exact riemannianMetric_inner U _ _ _ _ p w z

/-- A line in the angular-height covering plane of the unit cylinder. -/
def cylinderCurve (a b t : ℝ) : U := ⟨(a * t, b * t), Set.mem_univ _⟩

/-- Helices, vertical generators and horizontal parallels on the cylinder are geodesics
for the actual induced metric. -/
theorem isGeodesicCurve_cylinderCurve (a b : ℝ) :
    letI : RiemannianBundle (fun p : U ↦ TangentSpace IP p) :=
      ⟨cylinderMetric.toRiemannianMetric⟩
    IsGeodesicCurve IP (cylinderCurve a b) := by
  let : RiemannianBundle (fun p : U ↦ TangentSpace IP p) :=
    ⟨cylinderMetric.toRiemannianMetric⟩
  have hc : deriv (fun r ↦ (cylinderCurve a b r).val) = fun _ ↦ (a, b) := by
    funext t
    simpa [cylinderCurve] using (((hasDerivAt_id t).const_mul a).prodMk
      ((hasDerivAt_id t).const_mul b)).deriv
  rw [← isGeodesicCurveOn_univ]
  apply (SurfaceOfRevolution.isGeodesicCurveOn_iff cylinderMetric_inner
    (fun _ ↦ contDiffAt_const) (fun _ ↦ contDiffAt_id)
    (fun _ ↦ one_ne_zero) (fun p ↦ by simp [profileSpeedSq_def]) isOpen_univ).mpr
  constructor
  · have hC : ContMDiff 𝓘(ℝ) IP ∞ (cylinderCurve a b) := by
      rw [← ContMDiff.subtypeVal_comp_iff U]
      apply ContDiff.contMDiff
      simp only [Function.comp_def, cylinderCurve]
      fun_prop
    exact (hC.of_le (by norm_num)).contMDiffOn
  · intro t _
    dsimp only
    simp [hc, profileSpeedSq_def]

/-- The Christoffel map in planar polar coordinates has the usual nonzero radial and angular
terms, unlike the constant-coefficient cylindrical case. -/
theorem christoffelSecondKind_polar {p : P} (hr : p.2 ≠ 0) (w z : P) :
    christoffelSecondKind (metric id (fun _ ↦ 0)) p w z =
      ((w.1 * z.2 + w.2 * z.1) / p.2, -p.2 * w.1 * z.1) := by
  have hf : DifferentiableAt ℝ (deriv (id : ℝ → ℝ)) p.2 := by
    simp only [deriv_id']
    fun_prop
  have hg : DifferentiableAt ℝ (deriv (fun _ : ℝ ↦ (0 : ℝ))) p.2 := by
    simp only [deriv_const']
    fun_prop
  rw [christoffelSecondKind_metric differentiableAt_id hf hg hr
    (by simp [profileSpeedSq_def])]
  simp [profileSpeedSq_def]
  field_simp

end TauCeti.SurfaceOfRevolution.Examples
