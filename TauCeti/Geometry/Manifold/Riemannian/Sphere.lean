/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Induced

/-!
# The round metric on the unit sphere

The unit sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1` is an analytic manifold
modelled on `ℝⁿ` (Mathlib's stereographic atlas), and its inclusion into `E` is an analytic
immersion. The *round metric* is the Riemannian metric induced by this immersion: the inner
product of two tangent vectors is the inner product in `E` of their images under the differential
of the inclusion. This file installs it as the `RiemannianBundle` instance on the tangent bundle of
the sphere, together with its analyticity.

With `E = EuclideanSpace ℝ (Fin 4)` this is the round three-sphere `S³`, the spherical one of
Thurston's eight model geometries.

## Main definitions

* `TauCeti.sphereRoundMetric`: the analytic round metric on the unit sphere.
* `TauCeti.instRiemannianBundleSphere`, `TauCeti.instIsContMDiffRiemannianBundleSphere` and
  `TauCeti.instIsContinuousRiemannianBundleSphere`: the corresponding instances.

## Main statements

* `TauCeti.inner_tangentSpace_sphere`: the round inner product of two tangent vectors is the inner
  product of their images in `E`.
* `TauCeti.norm_tangentSpace_sphere`: the round norm of a tangent vector is the norm of its image
  in `E`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the round metric as an induced metric).
-/

public section

open Bundle Metric Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The round metric on the unit sphere of `E`: the analytic Riemannian metric induced by the
inclusion of the sphere into `E`. -/
def sphereRoundMetric :
    ContMDiffRiemannianMetric (𝓡 n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  inducedRiemannianMetric (n := ω) ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere
    injective_mvfderiv_subtypeVal_sphere

/-- The round metric evaluates the inner product of `E` on the images of tangent vectors under the
differential of the inclusion. -/
@[simp]
theorem sphereRoundMetric_inner (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    (sphereRoundMetric (E := E)).inner x v w =
      inner ℝ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w) :=
  inducedRiemannianMetric_inner _ _ _ x v w

/-- The unit sphere is a Riemannian manifold for its round metric. -/
instance instRiemannianBundleSphere :
    RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  ⟨(sphereRoundMetric (E := E)).toRiemannianMetric⟩

/-- The round metric is analytic. -/
instance instIsContMDiffRiemannianBundleSphere :
    IsContMDiffRiemannianBundle (𝓡 n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  Bundle.instIsContMDiffRiemannianBundle (sphereRoundMetric (E := E))

/-- The round metric is continuous. -/
instance instIsContinuousRiemannianBundleSphere :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  Bundle.instIsContinuousRiemannianBundle
    (sphereRoundMetric (E := E)).toContinuousRiemannianMetric

/-- The round inner product of two tangent vectors to the sphere is the inner product in `E` of
their images under the differential of the inclusion. -/
@[simp]
theorem inner_tangentSpace_sphere (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    inner ℝ v w =
      inner ℝ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w) :=
  sphereRoundMetric_inner x v w

/-- The round norm of a tangent vector to the sphere is the norm in `E` of its image under the
differential of the inclusion. -/
@[simp]
theorem norm_tangentSpace_sphere (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ‖v‖ = ‖mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_tangentSpace_sphere]

end TauCeti
