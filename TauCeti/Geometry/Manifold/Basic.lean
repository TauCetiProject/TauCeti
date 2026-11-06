/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Compact and closed manifold predicates

This file packages the dimension-independent topological hypotheses used by manifold constructions.
The chart structure is supplied by a `ChartedSpace` instance over the Euclidean half-space
(boundary allowed) or the Euclidean space (boundaryless) model. Every charted space is a
topological manifold (Mathlib's instance `IsManifold I 0 M`), so the predicates record only the
separation, countability, compactness, and connectedness conditions, as the typeclasses
`T2Space`, `SecondCountableTopology`, `CompactSpace`, and `ConnectedSpace`. The file also provides
the standard surface and three-manifold specializations used by geometric-topology APIs.
-/

public section

namespace TauCeti

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-- A compact, connected `n`-manifold, allowing a nonempty boundary, in the standard Euclidean
half-space model. -/
def IsCompactConnectedManifold (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ CompactSpace X ∧ ConnectedSpace X

/-- The defining separation, countability, compactness, and connectedness conditions for
`IsCompactConnectedManifold`. -/
@[simp]
theorem isCompactConnectedManifold_iff (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X] :
    IsCompactConnectedManifold n X ↔
      T2Space X ∧ SecondCountableTopology X ∧ CompactSpace X ∧ ConnectedSpace X :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
`IsCompactConnectedManifold n X`. -/
theorem isCompactConnectedManifold (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X] :
    IsCompactConnectedManifold n X :=
  ⟨‹_›, ‹_›, ‹_›, ‹_›⟩

/-- A compact, connected, Hausdorff, second-countable, boundaryless topological `n`-manifold. -/
def IsClosedConnectedManifold (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ CompactSpace X ∧ ConnectedSpace X

/-- The defining separation, countability, compactness, and connectedness conditions for
`IsClosedConnectedManifold`. -/
@[simp]
theorem isClosedConnectedManifold_iff (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] :
    IsClosedConnectedManifold n X ↔
      T2Space X ∧ SecondCountableTopology X ∧ CompactSpace X ∧ ConnectedSpace X :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
`IsClosedConnectedManifold n X`. -/
theorem isClosedConnectedManifold (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X] :
    IsClosedConnectedManifold n X :=
  ⟨‹_›, ‹_›, ‹_›, ‹_›⟩

/-- A compact connected surface, allowing a nonempty boundary, in the standard Euclidean
half-space model. -/
def IsCompactConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] : Prop :=
  IsCompactConnectedManifold 2 S

/-- A compact connected 3-manifold, allowing a nonempty boundary, in the standard Euclidean
half-space model. -/
def IsCompactConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] : Prop :=
  IsCompactConnectedManifold 3 M

/-- The defining conditions for a compact connected surface. -/
@[simp]
theorem isCompactConnectedSurface_iff
    [ChartedSpace (EuclideanHalfSpace 2) S] :
    IsCompactConnectedSurface S ↔
      T2Space S ∧ SecondCountableTopology S ∧ CompactSpace S ∧ ConnectedSpace S :=
  isCompactConnectedManifold_iff 2 S

/-- The defining conditions for a compact connected 3-manifold. -/
@[simp]
theorem isCompactConnectedThreeManifold_iff
    [ChartedSpace (EuclideanHalfSpace 3) M] :
    IsCompactConnectedThreeManifold M ↔
      T2Space M ∧ SecondCountableTopology M ∧ CompactSpace M ∧ ConnectedSpace M :=
  isCompactConnectedManifold_iff 3 M

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
the compact-connected-surface predicate. -/
theorem isCompactConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S] :
    IsCompactConnectedSurface S :=
  isCompactConnectedManifold 2 S

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
the compact-connected-3-manifold predicate. -/
theorem isCompactConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] :
    IsCompactConnectedThreeManifold M :=
  isCompactConnectedManifold 3 M

/-- A **closed connected surface** is a compact, connected, Hausdorff, second-countable,
boundaryless topological 2-manifold. The dimension is pinned by the Euclidean 2-space model. -/
def IsClosedConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] : Prop :=
  IsClosedConnectedManifold 2 S

/-- A **closed connected 3-manifold** is a compact, connected, Hausdorff, second-countable,
boundaryless topological 3-manifold. -/
def IsClosedConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  IsClosedConnectedManifold 3 M

/-- The defining separation, countability, compactness, and connectedness conditions for a closed
connected surface. -/
@[simp]
theorem isClosedConnectedSurface_iff
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] :
    IsClosedConnectedSurface S ↔
      T2Space S ∧ SecondCountableTopology S ∧ CompactSpace S ∧ ConnectedSpace S :=
  isClosedConnectedManifold_iff 2 S

/-- The defining separation, countability, compactness, and connectedness conditions for a closed
connected 3-manifold. -/
@[simp]
theorem isClosedConnectedThreeManifold_iff
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsClosedConnectedThreeManifold M ↔
      T2Space M ∧ SecondCountableTopology M ∧ CompactSpace M ∧ ConnectedSpace M :=
  isClosedConnectedManifold_iff 3 M

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
the closed-connected-surface predicate. -/
theorem isClosedConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S] :
    IsClosedConnectedSurface S :=
  isClosedConnectedManifold 2 S

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
the closed-connected-3-manifold predicate. -/
theorem isClosedConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] :
    IsClosedConnectedThreeManifold M :=
  isClosedConnectedManifold 3 M

end TauCeti
