/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Geometry.Manifold.Riemannian.Sphere
public import TauCeti.Geometry.Manifold.VectorField.Regularity
public import TauCeti.Geometry.Sphere.Circle

/-!
# The round metric on the unit circle

The complex unit circle is the unit sphere in the real inner-product space `ℂ`.  This file names
its induced round metric and records the ambient-coordinate formula used by the circle's later
Riemannian volume and Laplace--Beltrami calculations.

The construction reuses `TauCeti.sphereRoundMetric`; the circle is definitionally the unit sphere
of `ℂ`, so no second metric or auxiliary identification is introduced.
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

end Circle
