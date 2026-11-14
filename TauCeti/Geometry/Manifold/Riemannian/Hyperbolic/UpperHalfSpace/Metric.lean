/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.Completeness
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic

/-!
# The Riemannian distance and complete hyperbolic metric on upper half-space

Equip `UpperHalfSpace E` with its Riemannian metric space structure
`TauCeti.MetricSpace.ofRiemannianMetric`, whose topology is definitionally the manifold topology
and whose distance is the infimum of lengths of `C¹` curves in the hyperbolic metric
`(‖dx‖² + dt²) / t²`. In finite dimension this metric space is complete, and packaging the metric
with completeness and its constant-curvature tensor yields a `TauCeti.HyperbolicMetric` witness for
hyperbolic space in every positive dimension.

## Main definitions and instances

* `TauCeti.UpperHalfSpace.instMetricSpace`: the Riemannian `MetricSpace` on `UpperHalfSpace E`.
* `TauCeti.UpperHalfSpace.instIsRiemannianManifold`: `IsRiemannianManifold` for `UpperHalfSpace E`.
* `TauCeti.UpperHalfSpace.instCompleteSpace`: metric completeness when `E` is finite-dimensional.
* `TauCeti.UpperHalfSpace.hyperbolicMetric`: bundled `HyperbolicMetric` on `UpperHalfSpace E`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3
  (hyperbolic space in the upper-half-space model).
-/

public section

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "P" => WithLp 2 (E × ℝ)
local notation "J" => 𝓘(ℝ, P)

/-- The Riemannian metric space structure on `UpperHalfSpace E` induced by the hyperbolic metric
`(‖dx‖² + dt²) / t²`. Its underlying topology is definitionally the manifold topology. -/
instance instMetricSpace : MetricSpace (UpperHalfSpace E) :=
  MetricSpace.ofRiemannianMetric J (UpperHalfSpace E)

/-- Equipped with its Riemannian distance, `UpperHalfSpace E` satisfies `IsRiemannianManifold`:
its extended distance is the infimum of hyperbolic lengths of `C¹` curves. -/
instance instIsRiemannianManifold : IsRiemannianManifold J (UpperHalfSpace E) :=
  ⟨fun _ _ ↦ rfl⟩

/-- The extended distance on `UpperHalfSpace E` is its Riemannian extended distance. -/
theorem edist_eq_riemannianEDist (x y : UpperHalfSpace E) :
    edist x y = Manifold.riemannianEDist J x y :=
  (rfl)

/-- The distance on `UpperHalfSpace E` is the real value of its Riemannian extended distance. -/
theorem dist_eq_toReal_riemannianEDist (x y : UpperHalfSpace E) :
    dist x y = (Manifold.riemannianEDist J x y).toReal :=
  IsRiemannianManifold.dist_eq_toReal_riemannianEDist J x y

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- In finite dimension, `UpperHalfSpace E` with its Riemannian distance is complete. -/
instance instCompleteSpace : CompleteSpace (UpperHalfSpace E) :=
  completeSpace_of_riemannianMetric

/-- The standard complete metric of constant curvature `-1` on upper half-space. -/
def hyperbolicMetric : HyperbolicMetric (I := J) (M := UpperHalfSpace E) where
  metric := { riemannianMetric with contMDiff := riemannianMetric.contMDiff.of_le le_top }
  complete := completeSpace_of_riemannianMetric
  curvature := by
    rw [ContMDiffRiemannianMetric.isConstantCurvatureTensor_iff]
    exact curvatureTensor_eq

/-- Forgetting completeness and curvature recovers the standard upper-half-space metric. -/
@[simp] theorem hyperbolicMetric_toRiemannianMetric :
    (hyperbolicMetric (E := E)).metric.toRiemannianMetric = riemannianMetric.toRiemannianMetric :=
  (rfl)

/-- Upper half-space with its standard manifold structure admits a complete hyperbolic metric. -/
theorem isHyperbolic : IsHyperbolic (I := J) (M := UpperHalfSpace E) :=
  TauCeti.isHyperbolic_iff.mpr ⟨hyperbolicMetric⟩

end FiniteDimensional

end TauCeti.UpperHalfSpace
