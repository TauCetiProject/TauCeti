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
The Euclidean self-model is boundaryless, so `IsClosedConnectedManifold` records only the
separation, countability, topological-manifold, compactness, and connectedness conditions. It also
provides the standard surface and three-manifold specializations used by geometric-topology APIs.
-/

public section

open Set

open scoped Manifold ContDiff

namespace TauCeti

universe u

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-- A compact, connected `n`-manifold, allowing a nonempty boundary, in the standard Euclidean
half-space model. -/
def IsCompactConnectedManifold (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ IsManifold (𝓡∂ n) 0 X ∧
    IsCompact (univ : Set X) ∧ IsConnected (univ : Set X)

/-- The defining separation, countability, manifold, compactness, and connectedness conditions for
`IsCompactConnectedManifold`. -/
@[simp]
theorem isCompactConnectedManifold_iff (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X] :
    IsCompactConnectedManifold n X ↔
      T2Space X ∧ SecondCountableTopology X ∧ IsManifold (𝓡∂ n) 0 X ∧
        IsCompact (univ : Set X) ∧ IsConnected (univ : Set X) :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, and countability typeclasses, together
with the `IsManifold (𝓡∂ n) 0 X` hypothesis, supply `IsCompactConnectedManifold n X`. -/
theorem isCompactConnectedManifold (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X] [IsManifold (𝓡∂ n) 0 X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X] :
    IsCompactConnectedManifold n X :=
  ⟨inferInstance, inferInstance, inferInstance, isCompact_univ, isConnected_univ⟩

/-- A compact, connected, Hausdorff, second-countable, boundaryless topological `n`-manifold. -/
def IsClosedConnectedManifold (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ IsManifold (𝓡 n) 0 X ∧
    IsCompact (univ : Set X) ∧ IsConnected (univ : Set X)

/-- The defining separation, countability, manifold, compactness, and connectedness conditions for
`IsClosedConnectedManifold`. -/
@[simp]
theorem isClosedConnectedManifold_iff (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] :
    IsClosedConnectedManifold n X ↔
      T2Space X ∧ SecondCountableTopology X ∧ IsManifold (𝓡 n) 0 X ∧
        IsCompact (univ : Set X) ∧ IsConnected (univ : Set X) :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, and countability typeclasses, together
with the `IsManifold (𝓡 n) 0 X` hypothesis, supply `IsClosedConnectedManifold n X`. -/
theorem isClosedConnectedManifold (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) 0 X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X] :
    IsClosedConnectedManifold n X :=
  ⟨inferInstance, inferInstance, inferInstance, isCompact_univ, isConnected_univ⟩

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
      T2Space S ∧ SecondCountableTopology S ∧ IsManifold (𝓡∂ 2) 0 S ∧
        IsCompact (univ : Set S) ∧ IsConnected (univ : Set S) :=
  isCompactConnectedManifold_iff 2 S

/-- The defining conditions for a compact connected 3-manifold. -/
@[simp]
theorem isCompactConnectedThreeManifold_iff
    [ChartedSpace (EuclideanHalfSpace 3) M] :
    IsCompactConnectedThreeManifold M ↔
      T2Space M ∧ SecondCountableTopology M ∧ IsManifold (𝓡∂ 3) 0 M ∧
        IsCompact (univ : Set M) ∧ IsConnected (univ : Set M) :=
  isCompactConnectedManifold_iff 3 M

/-- The usual compactness, connectedness, separation, and countability typeclasses, together
with the `IsManifold (𝓡∂ 2) 0 S` hypothesis, supply the compact-connected-surface predicate. -/
theorem isCompactConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold (𝓡∂ 2) 0 S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S] :
    IsCompactConnectedSurface S :=
  isCompactConnectedManifold 2 S

/-- The usual compactness, connectedness, separation, and countability typeclasses, together
with the `IsManifold (𝓡∂ 3) 0 M` hypothesis, supply the compact-connected-3-manifold predicate. -/
theorem isCompactConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) 0 M]
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

/-- The defining manifold, separation, compactness, and connectedness conditions for a closed
connected surface. -/
@[simp]
theorem isClosedConnectedSurface_iff
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] :
    IsClosedConnectedSurface S ↔
      T2Space S ∧ SecondCountableTopology S ∧ IsManifold (𝓡 2) 0 S ∧
        IsCompact (univ : Set S) ∧ IsConnected (univ : Set S) :=
  isClosedConnectedManifold_iff 2 S

/-- The defining manifold, separation, compactness, and connectedness conditions for a closed
connected 3-manifold. -/
@[simp]
theorem isClosedConnectedThreeManifold_iff
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsClosedConnectedThreeManifold M ↔
      T2Space M ∧ SecondCountableTopology M ∧ IsManifold (𝓡 3) 0 M ∧
        IsCompact (univ : Set M) ∧ IsConnected (univ : Set M) :=
  isClosedConnectedManifold_iff 3 M

/-- The usual compactness, connectedness, separation, and countability typeclasses, together
with the `IsManifold (𝓡 2) 0 S` hypothesis, supply the closed-connected-surface predicate. -/
theorem isClosedConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) 0 S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S] :
    IsClosedConnectedSurface S :=
  isClosedConnectedManifold 2 S

/-- The usual compactness, connectedness, separation, and countability typeclasses, together
with the `IsManifold (𝓡 3) 0 M` hypothesis, supply the closed-connected-3-manifold predicate. -/
theorem isClosedConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) 0 M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] :
    IsClosedConnectedThreeManifold M :=
  isClosedConnectedManifold 3 M

end TauCeti
