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
separation, countability, topological-manifold, compactness, and connectedness conditions.
-/

public section

open Set

open scoped Manifold ContDiff

namespace TauCeti

universe u

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

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
`IsCompactConnectedManifold n X`. -/
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

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
`IsClosedConnectedManifold n X`. -/
theorem isClosedConnectedManifold (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) 0 X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X] :
    IsClosedConnectedManifold n X :=
  ⟨inferInstance, inferInstance, inferInstance, isCompact_univ, isConnected_univ⟩

end TauCeti
