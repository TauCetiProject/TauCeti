/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.AlgebraicTopology.FundamentalGroup.Incompressible

/-!
# Closed surfaces and Haken embeddings

This file packages the manifold hypotheses used for the Haken condition in dimension three.
`IsClosedConnectedSurface` records a compact, connected, boundaryless 2-manifold, while
`IsClosedConnectedThreeManifold` records the analogous hypotheses in dimension three.  The
relation `IsHakenSurfaceEmbedding` then combines both conditions with Tau Ceti's
dimension-independent `IsIncompressible` predicate.  The later Haken predicate can use this
relation for a chosen surface embedding without repeating either manifold package.

The product-slice witness is the basic example: a continuous retraction onto the first factor
makes the inclusion of a surface as a slice incompressible.  This is the standard elementary
example used when introducing Haken manifolds; the definitions follow Hatcher, *Notes on Basic
3-Manifold Topology*, Sections 1.1--1.2, and Jaco, *Lectures on Three-Manifold Topology*,
Chapter II.

## Main definitions

* `TauCeti.IsClosedConnectedSurface`: a compact, connected, Hausdorff, second-countable,
  boundaryless 2-manifold.
* `TauCeti.IsClosedConnectedThreeManifold`: the analogous 3-manifold predicate.
* `TauCeti.IsHakenSurfaceEmbedding`: a closed connected surface embedded incompressibly in a closed
  connected 3-manifold.

## Main results

* `TauCeti.isHakenSurfaceEmbedding_iff` exposes the three defining conditions.
* `TauCeti.isHakenSurfaceEmbedding_of_leftInverse` and
  `TauCeti.isHakenSurfaceEmbedding_prodMk` provide reusable incompressible-surface witnesses.
-/

public section

open Set

open scoped Manifold ContDiff

namespace TauCeti

/-! ### Closed manifold predicates -/

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-- A **closed connected surface** is a compact, connected, Hausdorff, second-countable,
boundaryless smooth 2-manifold.

The dimension is pinned by the Euclidean 2-space model. The separation and countability clauses
are explicit because Mathlib's `IsManifold` records only local compatibility with the model. -/
def IsClosedConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] : Prop :=
  T2Space S ∧ SecondCountableTopology S ∧ IsManifold (𝓡 2) ∞ S ∧
    BoundarylessManifold (𝓡 2) S ∧ IsCompact (univ : Set S) ∧ IsConnected (univ : Set S)

/-- A **closed connected 3-manifold** is a compact, connected, Hausdorff, second-countable,
boundaryless smooth 3-manifold. -/
def IsClosedConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  T2Space M ∧ SecondCountableTopology M ∧ IsManifold (𝓡 3) ∞ M ∧
    BoundarylessManifold (𝓡 3) M ∧ IsCompact (univ : Set M) ∧ IsConnected (univ : Set M)

@[simp]
theorem isClosedConnectedSurface_iff
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] :
    IsClosedConnectedSurface S ↔
      T2Space S ∧ SecondCountableTopology S ∧ IsManifold (𝓡 2) ∞ S ∧
        BoundarylessManifold (𝓡 2) S ∧ IsCompact (univ : Set S) ∧ IsConnected (univ : Set S) :=
  Iff.rfl

@[simp]
theorem isClosedConnectedThreeManifold_iff
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsClosedConnectedThreeManifold M ↔
      T2Space M ∧ SecondCountableTopology M ∧ IsManifold (𝓡 3) ∞ M ∧
        BoundarylessManifold (𝓡 3) M ∧ IsCompact (univ : Set M) ∧ IsConnected (univ : Set M) :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, countability, and boundaryless typeclasses
supply the closed-connected-surface predicate. -/
theorem isClosedConnectedSurface_of_classes
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    [T2Space S] [SecondCountableTopology S] [BoundarylessManifold (𝓡 2) S]
    [CompactSpace S] [ConnectedSpace S] : IsClosedConnectedSurface S :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, isCompact_univ, isConnected_univ⟩

/-- The usual compactness, connectedness, separation, countability, and boundaryless typeclasses
supply the closed-connected-3-manifold predicate. -/
theorem isClosedConnectedThreeManifold_of_classes
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [BoundarylessManifold (𝓡 3) M]
    [CompactSpace M] [ConnectedSpace M] : IsClosedConnectedThreeManifold M :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, isCompact_univ, isConnected_univ⟩

/-! ### Incompressible surface embeddings -/

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- A **Haken embedding** exhibits a closed connected surface as an incompressible surface in a
closed connected 3-manifold. Keeping the map as data lets later statements name the particular
surface rather than hiding it behind an existential. -/
def IsHakenSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsClosedConnectedSurface S ∧ IsClosedConnectedThreeManifold M ∧ IsIncompressible f

/-- The defining closed-surface, closed-ambient, and incompressibility conditions of
`IsHakenSurfaceEmbedding`. -/
@[simp]
theorem isHakenSurfaceEmbedding_iff {f : C(S, M)} :
    IsHakenSurfaceEmbedding f ↔ IsClosedConnectedSurface S ∧
      IsClosedConnectedThreeManifold M ∧ IsIncompressible f :=
  Iff.rfl

/-- A continuous left inverse gives a Haken embedding of a closed surface. -/
theorem isHakenSurfaceEmbedding_of_leftInverse {f : C(S, M)} {r : C(M, S)}
    (hS : IsClosedConnectedSurface S) (hM : IsClosedConnectedThreeManifold M)
    (h : r.comp f = ContinuousMap.id S) :
    IsHakenSurfaceEmbedding f :=
  ⟨hS, hM, isIncompressible_of_leftInverse h⟩

/-- A product-slice inclusion is Haken whenever its source and ambient product carry the required
closed manifold structures. -/
theorem isHakenSurfaceEmbedding_prodMk {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) (S × Y)]
    (hS : IsClosedConnectedSurface S) (hM : IsClosedConnectedThreeManifold (S × Y)) (y₀ : Y) :
    IsHakenSurfaceEmbedding (ContinuousMap.prodMk (ContinuousMap.id S)
      (ContinuousMap.const S y₀)) :=
  ⟨hS, hM, isIncompressible_prodMk y₀⟩

end TauCeti
