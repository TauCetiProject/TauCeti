/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Topology.MetricSpace.Homogeneous

/-!
# Completeness of homogeneous Riemannian manifolds

If the Riemannian isometry group acts transitively on a locally compact Riemannian manifold,
its Riemannian distance is complete. In particular this applies to finite-dimensional
homogeneous Riemannian manifolds, including the homogeneous models of three-dimensional
geometries. The conclusion concerns the Riemannian distance, rather than an arbitrary metric
compatible with the manifold topology.

The argument uses the distance-preserving action and completeness of homogeneous locally
compact pseudoemetric spaces. It also applies when different components are at infinite
distance and does not require a boundaryless model.

## References

* W. Thurston, *Three-Dimensional Geometry and Topology*, Vol. 1, Proposition 3.4.15.
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), Sections 4–5.
-/

public section

open Bundle Manifold
open scoped Manifold

namespace TauCeti

section Ambient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]
  [MulAction.IsPretransitive (Isom I M) M]

include I

variable (M) in
/-- A homogeneous Riemannian manifold whose topology is weakly locally compact is complete
for its Riemannian extended distance. -/
theorem completeSpace_of_isPretransitive_isom [WeaklyLocallyCompactSpace M] :
    CompleteSpace M := by
  let : IsIsometricSMul (Isom I M) M :=
    ⟨fun Φ ↦ IsometryClass.isometry Φ⟩
  exact completeSpace_of_isIsometricSMul_of_isPretransitive (G := Isom I M) (X := M)

variable (M) in
/-- Every finite-dimensional homogeneous Riemannian manifold is complete for its Riemannian
extended distance. -/
theorem completeSpace_of_isPretransitive_isom_of_finiteDimensional [FiniteDimensional ℝ E] :
    CompleteSpace M := by
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  exact completeSpace_of_isPretransitive_isom (I := I) M

end Ambient

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [T3Space M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [MulAction.IsPretransitive (Isom I M) M]

/-- The extended metric constructed from a finite-dimensional homogeneous Riemannian
manifold is complete. This installs the Riemannian distance on a manifold that initially
carries only a topology. -/
theorem completeSpace_ofRiemannianMetric_of_isPretransitive_isom :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    CompleteSpace M := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  exact completeSpace_of_isPretransitive_isom_of_finiteDimensional (I := I) M

end Intrinsic

end TauCeti
