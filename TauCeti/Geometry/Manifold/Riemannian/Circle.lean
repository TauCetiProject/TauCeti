/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The round metric on the unit circle

The complex unit circle is the unit sphere in the real inner-product space `ℂ`.  This file names
its induced round metric, records the ambient-coordinate formula used by the circle's later
Riemannian volume and Laplace--Beltrami calculations, and packages the tautological diffeomorphism
and Riemannian isometry between `Metric.sphere (0 : ℂ) 1` and `Circle`.

The construction reuses `TauCeti.sphereRoundMetric`; the circle is definitionally the unit sphere
of `ℂ`, so no second metric or auxiliary identification is introduced.

## Main definitions and results

* `TauCeti.roundMetricCircle`: the induced round metric on `Circle`.
* `Circle.roundMetricCircle_inner`: ambient-coordinate formula for the inner product.
* `TauCeti.sphereComplexToCircleDiffeomorph` and `TauCeti.sphereComplexToCircleIsometry`: the
  tautological diffeomorphism and Riemannian isometry `Metric.sphere (0 : ℂ) 1 ≃ Circle`.
-/

public section

open Bundle Manifold Metric
open scoped ContDiff Manifold

local instance circleFinrankFact : Fact (Module.finrank ℝ ℂ = 1 + 1) :=
  ⟨by norm_num [Complex.finrank_real_complex]⟩

namespace Circle

/-- The sphere chart structure made available through Circle's opaque type abbreviation. -/
noncomputable local instance circleChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Submonoid.unitSphere ℂ) :=
  instChartedSpaceEuclideanSpaceRealFinOfNatNatCircle

end Circle

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

namespace TauCeti

/-- The tautological diffeomorphism between the unit sphere in `ℂ` and `Circle`. -/
noncomputable def sphereComplexToCircleDiffeomorph :
    Diffeomorph (𝓡 1) (𝓡 1) (sphere (0 : ℂ) 1) Circle ∞ where
  toEquiv :=
    { toFun := fun z ↦ z
      invFun := fun z ↦ z
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  contMDiff_toFun := contMDiff_id
  contMDiff_invFun := contMDiff_id

/-- Applying `sphereComplexToCircleDiffeomorph` preserves the underlying complex number. -/
@[simp]
theorem coe_sphereComplexToCircleDiffeomorph_apply (z : sphere (0 : ℂ) 1) :
    (sphereComplexToCircleDiffeomorph z : ℂ) = z :=
  (rfl)

/-- Applying the inverse of `sphereComplexToCircleDiffeomorph` preserves the underlying complex
number. -/
@[simp]
theorem coe_sphereComplexToCircleDiffeomorph_symm_apply (z : Circle) :
    (sphereComplexToCircleDiffeomorph.symm z : ℂ) = z :=
  (rfl)

/-- The tautological Riemannian isometry between the unit sphere in `ℂ` and `Circle` equipped with
`TauCeti.roundMetricCircle`. -/
noncomputable def sphereComplexToCircleIsometry :
    letI := TauCeti.roundMetricCircle
    RiemannianIsometry (𝓡 1) (𝓡 1) (sphere (0 : ℂ) 1) Circle :=
  letI := TauCeti.roundMetricCircle
  { toDiffeomorph := sphereComplexToCircleDiffeomorph
    inner_mfderiv' := fun x v w ↦ by
      have hι : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ))
          (sphereComplexToCircleDiffeomorph x) :=
        (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1) x).mdifferentiableAt one_ne_zero
      have hφ : MDifferentiableAt (𝓡 1) (𝓡 1) sphereComplexToCircleDiffeomorph x :=
        sphereComplexToCircleDiffeomorph.contMDiff.mdifferentiable (by simp) x
      have hval : (fun z : Circle ↦ (z : ℂ)) ∘ sphereComplexToCircleDiffeomorph =
          (Subtype.val : sphere (0 : ℂ) 1 → ℂ) :=
        funext coe_sphereComplexToCircleDiffeomorph_apply
      rw [Circle.roundMetricCircle_inner, ← mvfderiv_apply_eq_mfderiv_apply,
        ← mvfderiv_apply_eq_mfderiv_apply, ← mvfderiv_comp_apply x hι hφ,
        ← mvfderiv_comp_apply x hι hφ, hval]
      exact (inner_tangentSpace_sphere x v w).symm }

/-- The underlying diffeomorphism of `sphereComplexToCircleIsometry` is
`sphereComplexToCircleDiffeomorph`. -/
@[simp]
theorem toDiffeomorph_sphereComplexToCircleIsometry :
    letI := TauCeti.roundMetricCircle
    sphereComplexToCircleIsometry.toDiffeomorph = sphereComplexToCircleDiffeomorph :=
  (rfl)

/-- As a function, `sphereComplexToCircleIsometry` is `sphereComplexToCircleDiffeomorph`. -/
@[simp]
theorem coe_sphereComplexToCircleIsometry :
    letI := TauCeti.roundMetricCircle
    ⇑sphereComplexToCircleIsometry = sphereComplexToCircleDiffeomorph :=
  (rfl)

end TauCeti
