/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.Maps.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.Incompressible
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Compact surfaces and Haken embeddings

This file packages the manifold hypotheses used for the Haken condition in dimension three.
`IsCompactConnectedSurface` and `IsCompactConnectedThreeManifold` are boundary-aware predicates,
using Mathlib's Euclidean half-space models.  The relation `IsHakenSurfaceEmbedding` combines
these with a closed embedding, boundary preservation, relative local flatness, a bicollar, and Tau
Ceti's dimension-independent `IsIncompressible` predicate.  The closed specialization
`IsClosedHakenSurfaceEmbedding` additionally records local flatness and a global bicollar.

The product-slice witness is the basic example: a continuous retraction onto the first factor
makes the inclusion of a surface as a slice incompressible.  This is the standard elementary
example used when introducing Haken manifolds; the definitions follow Hatcher, *Notes on Basic
3-Manifold Topology*, Sections 1.1--1.2, and Jaco, *Lectures on Three-Manifold Topology*,
Chapter II.

## Main definitions

* `TauCeti.IsCompactConnectedSurface`: a compact, connected, Hausdorff, second-countable
  2-manifold, possibly with boundary.
* `TauCeti.IsCompactConnectedThreeManifold`: the analogous 3-manifold predicate.
* `TauCeti.IsClosedIncompressibleSurfaceEmbedding`: a closed connected surface embedded
  incompressibly in a closed connected 3-manifold.
* `TauCeti.IsHakenSurfaceEmbedding`: a proper, incompressible, non-spherical witness for
  Haken-ness, allowing boundary.
* `TauCeti.IsClosedHakenSurfaceEmbedding`: the closed, bicollared specialization.

## Main results

* `TauCeti.isClosedIncompressibleSurfaceEmbedding_iff` exposes the three defining conditions.
* `TauCeti.isClosedIncompressibleSurfaceEmbedding_of_leftInverse` and
  `TauCeti.isClosedIncompressibleSurfaceEmbedding_prodMk` provide reusable incompressible-surface
  witnesses.
* `TauCeti.isHakenSurfaceEmbedding_iff` exposes the additional Haken-witness conditions.
-/

public section

open Set Topology

open scoped Manifold ContDiff

namespace TauCeti

/-! ### Compact connected manifold predicates -/

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-- A compact connected surface, allowing a nonempty boundary, in the standard Euclidean
half-space model. -/
def IsCompactConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] : Prop :=
  T2Space S ∧ SecondCountableTopology S ∧ IsManifold (𝓡∂ 2) ∞ S ∧
    IsCompact (univ : Set S) ∧ IsConnected (univ : Set S)

/-- A compact connected 3-manifold, allowing a nonempty boundary, in the standard Euclidean
half-space model. -/
def IsCompactConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] : Prop :=
  T2Space M ∧ SecondCountableTopology M ∧ IsManifold (𝓡∂ 3) ∞ M ∧
    IsCompact (univ : Set M) ∧ IsConnected (univ : Set M)

@[simp]
theorem isCompactConnectedSurface_iff
    [ChartedSpace (EuclideanHalfSpace 2) S] :
    IsCompactConnectedSurface S ↔
      T2Space S ∧ SecondCountableTopology S ∧ IsManifold (𝓡∂ 2) ∞ S ∧
        IsCompact (univ : Set S) ∧ IsConnected (univ : Set S) :=
  Iff.rfl

@[simp]
theorem isCompactConnectedThreeManifold_iff
    [ChartedSpace (EuclideanHalfSpace 3) M] :
    IsCompactConnectedThreeManifold M ↔
      T2Space M ∧ SecondCountableTopology M ∧ IsManifold (𝓡∂ 3) ∞ M ∧
        IsCompact (univ : Set M) ∧ IsConnected (univ : Set M) :=
  Iff.rfl

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

/-! ### Boundary-aware Haken witnesses -/

section BoundaryAware

variable [ChartedSpace (EuclideanHalfSpace 2) S]
  [ChartedSpace (EuclideanHalfSpace 3) M]

/-- A **Haken surface embedding** allows the standard properly embedded, boundary-bearing witness.
It is a closed embedding, preserves the manifold boundary exactly, and is locally flat and
bicollared in the relative model `EuclideanHalfSpace 2 × ℝ`. Thus interior points cannot land on
the ambient boundary, boundary points cannot land in the interior, and the surface has two sides
even where it meets the boundary. It is also incompressible with nontrivial fundamental group. -/
def IsHakenSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsCompactConnectedSurface S ∧ IsCompactConnectedThreeManifold M ∧
    IsClosedEmbedding f ∧ f ⁻¹' (𝓡∂ 3).boundary M = (𝓡∂ 2).boundary S ∧
      IsLocallyFlat (EuclideanHalfSpace 2) ℝ f ∧ IsBicollared f ∧
        IsIncompressible f ∧ ∃ s : S, Nontrivial (FundamentalGroup S s)

/-- The defining compact, proper, boundary-preserving, locally flat, bicollared, incompressible,
and non-spherical conditions of `IsHakenSurfaceEmbedding`. -/
@[simp]
theorem isHakenSurfaceEmbedding_iff {f : C(S, M)} :
    IsHakenSurfaceEmbedding f ↔
      IsCompactConnectedSurface S ∧ IsCompactConnectedThreeManifold M ∧
        IsClosedEmbedding f ∧ f ⁻¹' (𝓡∂ 3).boundary M = (𝓡∂ 2).boundary S ∧
          IsLocallyFlat (EuclideanHalfSpace 2) ℝ f ∧ IsBicollared f ∧
            IsIncompressible f ∧ ∃ s : S, Nontrivial (FundamentalGroup S s) :=
  Iff.rfl

end BoundaryAware

/-! ### Closed incompressible surface embeddings -/

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- A **closed incompressible surface embedding** exhibits a closed connected surface as an
incompressible surface in a closed connected 3-manifold. Keeping the map as data lets later
statements name the particular surface rather than hiding it behind an existential. This is not
the Haken predicate: Haken-ness is a separate property of a 3-manifold asserting the existence of
an appropriate incompressible surface. -/
def IsClosedIncompressibleSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsClosedConnectedSurface S ∧ IsClosedConnectedThreeManifold M ∧ IsIncompressible f

/-- The defining closed-surface, closed-ambient, and incompressibility conditions of
`IsClosedIncompressibleSurfaceEmbedding`. -/
@[simp]
theorem isClosedIncompressibleSurfaceEmbedding_iff {f : C(S, M)} :
    IsClosedIncompressibleSurfaceEmbedding f ↔ IsClosedConnectedSurface S ∧
      IsClosedConnectedThreeManifold M ∧ IsIncompressible f :=
  Iff.rfl

/-- A continuous left inverse gives a closed incompressible surface embedding. -/
theorem isClosedIncompressibleSurfaceEmbedding_of_leftInverse {f : C(S, M)} {r : C(M, S)}
    (hS : IsClosedConnectedSurface S) (hM : IsClosedConnectedThreeManifold M)
    (h : r.comp f = ContinuousMap.id S) :
    IsClosedIncompressibleSurfaceEmbedding f :=
  ⟨hS, hM, isIncompressible_of_leftInverse h⟩

/-- A product-slice inclusion is a closed incompressible surface embedding whenever its source and
ambient product carry the required closed manifold structures. -/
theorem isClosedIncompressibleSurfaceEmbedding_prodMk {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) (S × Y)]
    (hS : IsClosedConnectedSurface S) (hM : IsClosedConnectedThreeManifold (S × Y)) (y₀ : Y) :
    IsClosedIncompressibleSurfaceEmbedding (ContinuousMap.prodMk (ContinuousMap.id S)
      (ContinuousMap.const S y₀)) :=
  ⟨hS, hM, isIncompressible_prodMk y₀⟩

/-- A **closed Haken surface embedding** is a closed incompressible embedding with the geometric
conditions needed for the usual Haken witness: it is locally flat in codimension one, globally
bicollared (hence two-sided), and its source has a nontrivial fundamental group, excluding the
spherical case.  The separate `IsClosedIncompressibleSurfaceEmbedding` package intentionally
remains the dimension-independent topological core; a Haken predicate may existentially quantify
this stronger relation without admitting wild, one-sided, or spherical surfaces. -/
def IsClosedHakenSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsClosedIncompressibleSurfaceEmbedding f ∧
    IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f ∧ IsBicollared f ∧
      ∃ s : S, Nontrivial (FundamentalGroup S s)

/-- The defining conditions of `IsClosedHakenSurfaceEmbedding`. -/
@[simp]
theorem isClosedHakenSurfaceEmbedding_iff {f : C(S, M)} :
    IsClosedHakenSurfaceEmbedding f ↔
      IsClosedIncompressibleSurfaceEmbedding f ∧
        IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f ∧ IsBicollared f ∧
          ∃ s : S, Nontrivial (FundamentalGroup S s) :=
  Iff.rfl

end TauCeti
