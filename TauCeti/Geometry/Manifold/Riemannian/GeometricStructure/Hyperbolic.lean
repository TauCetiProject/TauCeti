/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.GeometricStructure.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Curvature
public import TauCeti.Geometry.Manifold.Riemannian.SMulGroupoid.Curvature

/-!
# Closed hyperbolic geometric manifolds are hyperbolic

A space with a geometric structure modelled on hyperbolic space `ℍ³`
(`TauCeti.HasGeometricStructure` for `TauCeti.ModelGeometry.hyperbolic`) is a quotient `ℍ³ / Γ`
by a free, properly discontinuous group of isometries. Hyperbolic volume, Mostow rigidity and the
statements built on them instead ask for a complete Riemannian metric of constant curvature `-1`
(`TauCeti.IsHyperbolic`). This file connects the two: the metric of `ℍ³`, read through the
`(Isom ℍ³, ℍ³)`-atlas of the quotient, has constant curvature `-1`
(`TauCeti.isConstantCurvatureTensor_contMDiffChartRiemannianMetric`), and it is complete when the
quotient is compact.

## Main results

* `TauCeti.HasGeometricStructure.exists_isHyperbolic`: a compact connected space with a hyperbolic
  geometric structure is a smooth manifold carrying a hyperbolic metric.

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton University Press,
  1997, Sections 3.4 and 3.8.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

/-- **Closed hyperbolic geometric manifolds are hyperbolic.** A compact connected space with a
geometric structure modelled on hyperbolic space has a smooth structure, modelled on the charts of
`ℍ³`, for which it carries a complete Riemannian metric of constant curvature `-1`. -/
theorem HasGeometricStructure.exists_isHyperbolic {M : Type*} [TopologicalSpace M]
    [CompactSpace M] [T3Space M] [PreconnectedSpace M]
    (h : HasGeometricStructure M .hyperbolic) :
    ∃ (_ : ChartedSpace ModelGeometry.hyperbolic.ChartSpace M)
      (_ : IsManifold ModelGeometry.hyperbolic.model ∞ M),
      IsHyperbolic (I := ModelGeometry.hyperbolic.model) (M := M) := by
  obtain ⟨_, _⟩ := h.exists_hasGroupoid
  exact ⟨ChartedSpace.comp _ ModelGeometry.hyperbolic.Space M,
    isManifold_of_hasGroupoid_smulGroupoid ModelGeometry.hyperbolic.model ∞
      (Isom ModelGeometry.hyperbolic.model ModelGeometry.hyperbolic.Space) M,
    isHyperbolic_of_hasGroupoid_smulGroupoid (I := ModelGeometry.hyperbolic.model)
      fun x w u v ↦ UpperHalfSpace.curvatureTensor_eq x w u v⟩

end TauCeti
