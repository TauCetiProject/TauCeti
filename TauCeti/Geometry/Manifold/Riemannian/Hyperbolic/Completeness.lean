/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Homogeneous
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace

/-!
# Completeness of the upper-half-space metric

The upper-half-space model carries a transitive action by Riemannian isometries. The general
homogeneous-manifold completeness theorem therefore supplies the metric completeness required by
the `complete` field of `TauCeti.HyperbolicMetric`. This file records that consequence for every
finite-dimensional real inner-product space, leaving the constant-curvature calculation to the
model-specific hyperbolic development.

## Main result

* `TauCeti.UpperHalfSpace.completeSpace_of_riemannianMetric`: the Riemannian distance of the
  upper-half-space metric is complete.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 3.
* P. Scott, *The geometries of 3-manifolds*, Proposition 3.4.15.
-/

public section

open scoped Manifold

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Riemannian distance of the upper-half-space metric is complete in finite dimension.

The explicit uniform-space argument in the conclusion matches the metric used by
`TauCeti.HyperbolicMetric.complete`. -/
theorem completeSpace_of_riemannianMetric [FiniteDimensional ℝ E] :
    @CompleteSpace (UpperHalfSpace E)
      ((MetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (E × ℝ))
          (UpperHalfSpace E)).toPseudoMetricSpace.toUniformSpace) := by
  -- Completeness follows from transitivity of the full Riemannian-isometry group and the
  -- finite-dimensional homogeneous-manifold theorem.
  exact @completeSpace_of_isPretransitive_isom_of_finiteDimensional (WithLp 2 (E × ℝ)) _ _ _ _
    (𝓘(ℝ, WithLp 2 (E × ℝ))) (UpperHalfSpace E)
    (EMetricSpace.ofRiemannianMetric 𝓘(ℝ, WithLp 2 (E × ℝ)) (UpperHalfSpace E)).toPseudoEMetricSpace
    _ _ _ _ _

end TauCeti.UpperHalfSpace
