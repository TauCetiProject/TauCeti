/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.MeasureTheory.Group.Circle

import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.Geometry.Manifold.Instances.AddCircle.Circle
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.OneDimensional
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The round metric on the unit circle

The complex unit circle is the unit sphere in the real inner-product space `ℂ`. This file names
its induced round metric and records its ambient-coordinate inner product formula.

The construction reuses `TauCeti.sphereRoundMetric`; the circle is definitionally the unit sphere
of `ℂ`, so no second metric or auxiliary identification is introduced.

`Circle.norm_curveVelocity_exp` shows that the angular parametrization has unit speed.
The periodic change of variables `Diffeomorph.map_withDensity_enorm_curveVelocity_addCircle`
then identifies the Riemannian volume with arclength (`Circle.riemannianVolume_eq_circleArcLength`).
Consequently `Circle.riemannianVolume_univ` gives total mass `2 * π`.
-/

public section

open Bundle
open scoped Manifold

local instance circleFinrankFact : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
  ⟨by norm_num [Complex.finrank_real_complex]⟩

namespace TauCeti

/-- The sphere chart structure made available through Circle's opaque type abbreviation. -/
noncomputable local instance circleChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Submonoid.unitSphere ℂ) :=
  instChartedSpaceEuclideanSpaceRealFinOfNatNatCircle

/-- The Riemannian bundle carrying the induced round metric on the complex unit circle. -/
@[instance_reducible]
noncomputable def roundMetricCircle :
    RiemannianBundle (fun x : Circle ↦ TangentSpace (𝓡 1) x) :=
  ⟨(sphereRoundMetric (E := ℂ) (n := 1)).toRiemannianMetric⟩

end TauCeti

namespace Circle

/-- The round metric pairs circle tangent vectors by the ambient complex inner product of their
manifold derivatives under the inclusion into `ℂ`. -/
@[simp]
theorem roundMetricCircle_inner (x : Circle) (v w : TangentSpace (𝓡 1) x) :
    let _ := TauCeti.roundMetricCircle
    inner ℝ v w =
      inner ℝ (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) x v)
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) x w) := by
  let _ : RiemannianBundle (fun x : Circle ↦ TangentSpace (𝓡 1) x) := TauCeti.roundMetricCircle
  rw [← mvfderiv_apply_eq_mfderiv_apply, ← mvfderiv_apply_eq_mfderiv_apply]
  exact TauCeti.inner_tangentSpace_sphere (E := ℂ) (n := 1) x v w

section Volume

open MeasureTheory Set TauCeti
open scoped InnerProductSpace Real

attribute [local instance] TauCeti.roundMetricCircle

-- Use the sphere's continuous metric with the named round metric on `Circle`.
local instance : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
    (fun z : Circle ↦ TangentSpace (𝓡 1) z) :=
  (inferInstance : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
    (fun z : Metric.sphere (0 : ℂ) 1 ↦ TangentSpace (𝓡 1) z))

/-- The angular parametrization of the round circle has unit speed. -/
@[simp]
theorem norm_curveVelocity_exp (t : ℝ) :
    ‖TauCeti.Manifold.curveVelocity (𝓡 1) Circle.exp t‖ = 1 := by
  have hι : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) (Circle.exp t) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have hγ := (contMDiff_circleExp (m := 1)).mdifferentiable one_ne_zero t
  have hv := (TauCeti.Manifold.hasDerivAt_comp_curve hι
    (TauCeti.Manifold.hasMFDerivAt_curveVelocity hγ)).unique (hasDerivAt_coe_circleExp t)
  have hnorm : ‖TauCeti.Manifold.curveVelocity (𝓡 1) Circle.exp t‖ =
      ‖mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) (Circle.exp t)
        (TauCeti.Manifold.curveVelocity (𝓡 1) Circle.exp t)‖ :=
    norm_tangentSpace_sphere (E := ℂ) (n := 1) (Circle.exp t) _
  rw [hnorm, hv]
  have h : ‖Complex.I * (Circle.exp t : ℂ)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, Circle.norm_coe, mul_one]
  exact h

/-- The Riemannian volume measure of the round circle is its unnormalized arclength measure. -/
theorem riemannianVolume_eq_circleArcLength : riemannianVolume (𝓡 1) Circle = circleArcLength := by
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  let e := AddCircle.diffeomorphCircle (2 * π) 1
  have he : (fun t : ℝ ↦ e t) = Circle.exp := by
    funext t
    rw [AddCircle.diffeomorphCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul]
  have hspeed : (fun t ↦ ‖TauCeti.Manifold.curveVelocity (𝓡 1) Circle.exp t‖ₑ) = 1 := by
    funext t
    rw [← ofReal_norm, norm_curveVelocity_exp, ENNReal.ofReal_one, Pi.one_apply]
  have hvol := e.map_withDensity_enorm_curveVelocity_addCircle one_ne_zero 0
  have hmap := congrArg (fun γ : ℝ → Circle ↦ Measure.map γ
    ((volume.restrict (Ioc 0 (0 + 2 * π))).withDensity
      fun t ↦ ‖TauCeti.Manifold.curveVelocity (𝓡 1) γ t‖ₑ)) he
  rw [hmap, hspeed, withDensity_one, zero_add] at hvol
  have hmk : AddCircle.homeomorphCircle' ∘ ((↑) : ℝ → AddCircle (2 * π)) = Circle.exp :=
    funext AddCircle.homeomorphCircle'_apply_mk
  have hquot := AddCircle.measurePreserving_mk (2 * π) 0
  -- Express arclength as the same pushforward from the period interval.
  rw [circleArcLength_def, ← hquot.map_eq, Measure.map_map
    AddCircle.homeomorphCircle'.continuous.measurable hquot.measurable, hmk, zero_add]
  exact hvol.symm

/-- The Riemannian volume measure of the round unit circle has total mass `2 * π`. -/
@[simp]
theorem riemannianVolume_univ : riemannianVolume (𝓡 1) Circle univ = ENNReal.ofReal (2 * π) := by
  rw [riemannianVolume_eq_circleArcLength, circleArcLength_univ]

end Volume

end Circle
