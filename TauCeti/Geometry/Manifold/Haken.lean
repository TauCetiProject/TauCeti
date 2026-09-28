/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.AlgebraicTopology.FundamentalGroup.Incompressible
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Compact surfaces and Haken embeddings

This file packages the manifold hypotheses used for the Haken condition in dimension three.
`IsCompactConnectedSurface` and `IsCompactConnectedThreeManifold` are boundary-aware
specializations of the dimension-independent compact-connected manifold predicate, using
Mathlib's Euclidean half-space models.  The relation `IsHakenSurfaceEmbedding` combines these with
boundary preservation, a bicollar, and Tau Ceti's dimension-independent `IsIncompressible`
predicate.  The closed specialization `IsClosedHakenSurfaceEmbedding` additionally records a
global bicollar.

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
* `TauCeti.IsIrreducibleThreeManifold`: every closed locally flat embedded 2-sphere bounds an
  embedded 3-ball.
* `TauCeti.IsHakenThreeManifold` and `TauCeti.IsClosedHakenThreeManifold`: the corresponding
  irreducible existential Haken predicates for ambient 3-manifolds.

## Main results

* `TauCeti.isClosedIncompressibleSurfaceEmbedding_iff` exposes the three defining conditions.
* `TauCeti.isClosedIncompressibleSurfaceEmbedding_of_leftInverse` and
  `TauCeti.isClosedIncompressibleSurfaceEmbedding_prodMk` provide reusable incompressible-surface
  witnesses.
* `TauCeti.isHakenSurfaceEmbedding_iff` exposes the additional Haken-witness conditions.
* `TauCeti.isHakenThreeManifold_of_isHakenSurfaceEmbedding` and
  `TauCeti.isClosedHakenThreeManifold_of_isClosedHakenSurfaceEmbedding` package a surface witness
  into the corresponding ambient predicate.
-/

public section

open Set Topology

open scoped Manifold ContDiff TopCat

namespace TauCeti

universe u

/-! ### Compact connected manifold predicates -/

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-- A compact, connected `n`-manifold, allowing a nonempty boundary, in the standard Euclidean
half-space model. -/
def IsCompactConnectedManifold (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ IsManifold (𝓡∂ n) ∞ X ∧
    IsCompact (univ : Set X) ∧ IsConnected (univ : Set X)

/-- The defining separation, countability, manifold, compactness, and connectedness conditions for
`IsCompactConnectedManifold`. -/
@[simp]
theorem isCompactConnectedManifold_iff (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X] :
    IsCompactConnectedManifold n X ↔
      T2Space X ∧ SecondCountableTopology X ∧ IsManifold (𝓡∂ n) ∞ X ∧
        IsCompact (univ : Set X) ∧ IsConnected (univ : Set X) :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, and countability typeclasses supply
`IsCompactConnectedManifold n X`. -/
theorem isCompactConnectedManifold (n : ℕ) [NeZero n] (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace n) X] [IsManifold (𝓡∂ n) ∞ X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] [ConnectedSpace X] :
    IsCompactConnectedManifold n X :=
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
      T2Space S ∧ SecondCountableTopology S ∧ IsManifold (𝓡∂ 2) ∞ S ∧
        IsCompact (univ : Set S) ∧ IsConnected (univ : Set S) :=
  Iff.rfl

/-- The defining conditions for a compact connected 3-manifold. -/
@[simp]
theorem isCompactConnectedThreeManifold_iff
    [ChartedSpace (EuclideanHalfSpace 3) M] :
    IsCompactConnectedThreeManifold M ↔
      T2Space M ∧ SecondCountableTopology M ∧ IsManifold (𝓡∂ 3) ∞ M ∧
        IsCompact (univ : Set M) ∧ IsConnected (univ : Set M) :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, and countability typeclasses supply the
compact-connected-surface predicate. -/
theorem isCompactConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold (𝓡∂ 2) ∞ S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S] :
    IsCompactConnectedSurface S :=
  isCompactConnectedManifold 2 S

/-- The usual compactness, connectedness, separation, and countability typeclasses supply the
compact-connected-3-manifold predicate. -/
theorem isCompactConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M] :
    IsCompactConnectedThreeManifold M :=
  isCompactConnectedManifold 3 M

/-- A compact, connected, Hausdorff, second-countable, boundaryless smooth `n`-manifold. -/
def IsClosedConnectedManifold (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] : Prop :=
  T2Space X ∧ SecondCountableTopology X ∧ IsManifold (𝓡 n) ∞ X ∧
    BoundarylessManifold (𝓡 n) X ∧ IsCompact (univ : Set X) ∧ IsConnected (univ : Set X)

/-- The defining conditions for `IsClosedConnectedManifold`. -/
@[simp]
theorem isClosedConnectedManifold_iff (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] :
    IsClosedConnectedManifold n X ↔
      T2Space X ∧ SecondCountableTopology X ∧ IsManifold (𝓡 n) ∞ X ∧
        BoundarylessManifold (𝓡 n) X ∧ IsCompact (univ : Set X) ∧ IsConnected (univ : Set X) :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, countability, and boundaryless typeclasses
supply `IsClosedConnectedManifold n X`. -/
theorem isClosedConnectedManifold (n : ℕ) (X : Type*) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [IsManifold (𝓡 n) ∞ X]
    [T2Space X] [SecondCountableTopology X] [BoundarylessManifold (𝓡 n) X]
    [CompactSpace X] [ConnectedSpace X] : IsClosedConnectedManifold n X :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, isCompact_univ, isConnected_univ⟩

/-- A **closed connected surface** is a compact, connected, Hausdorff, second-countable,
boundaryless smooth 2-manifold. The dimension is pinned by the Euclidean 2-space model. -/
def IsClosedConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] : Prop :=
  IsClosedConnectedManifold 2 S

/-- A **closed connected 3-manifold** is a compact, connected, Hausdorff, second-countable,
boundaryless smooth 3-manifold. -/
def IsClosedConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  IsClosedConnectedManifold 3 M

/-- The defining manifold, separation, compactness, connectedness, and boundarylessness conditions
for a closed connected surface. -/
@[simp]
theorem isClosedConnectedSurface_iff
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] :
    IsClosedConnectedSurface S ↔
      T2Space S ∧ SecondCountableTopology S ∧ IsManifold (𝓡 2) ∞ S ∧
        BoundarylessManifold (𝓡 2) S ∧ IsCompact (univ : Set S) ∧ IsConnected (univ : Set S) :=
  Iff.rfl

/-- The defining manifold, separation, compactness, connectedness, and boundarylessness conditions
for a closed connected 3-manifold. -/
@[simp]
theorem isClosedConnectedThreeManifold_iff
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsClosedConnectedThreeManifold M ↔
      T2Space M ∧ SecondCountableTopology M ∧ IsManifold (𝓡 3) ∞ M ∧
        BoundarylessManifold (𝓡 3) M ∧ IsCompact (univ : Set M) ∧ IsConnected (univ : Set M) :=
  Iff.rfl

/-- The usual compactness, connectedness, separation, countability, and boundaryless typeclasses
supply the closed-connected-surface predicate. -/
theorem isClosedConnectedSurface (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    [T2Space S] [SecondCountableTopology S] [BoundarylessManifold (𝓡 2) S]
    [CompactSpace S] [ConnectedSpace S] : IsClosedConnectedSurface S :=
  isClosedConnectedManifold 2 S

/-- The usual compactness, connectedness, separation, countability, and boundaryless typeclasses
supply the closed-connected-3-manifold predicate. -/
theorem isClosedConnectedThreeManifold (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M] [BoundarylessManifold (𝓡 3) M]
    [CompactSpace M] [ConnectedSpace M] : IsClosedConnectedThreeManifold M :=
  isClosedConnectedManifold 3 M

/-! ### Boundary-aware Haken witnesses -/

section BoundaryAware

variable [ChartedSpace (EuclideanHalfSpace 2) S]
  [ChartedSpace (EuclideanHalfSpace 3) M]

/-- A **Haken surface embedding** allows the standard properly embedded, boundary-bearing witness.
It preserves the manifold boundary exactly and is bicollared in the relative model
`EuclideanHalfSpace 2 × ℝ`, hence is locally flat and a closed embedding. Thus interior points
cannot land on the ambient boundary, boundary points cannot land in the interior, and the surface
has two sides even where it meets the boundary. It is also incompressible with nontrivial
fundamental group. -/
def IsHakenSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsCompactConnectedSurface S ∧ IsCompactConnectedThreeManifold M ∧
    f ⁻¹' (𝓡∂ 3).boundary M = (𝓡∂ 2).boundary S ∧ IsBicollared f ∧
      IsIncompressible f ∧ ∃ s : S, Nontrivial (FundamentalGroup S s)

/-- The defining compact, boundary-preserving, bicollared, incompressible, and non-spherical
conditions of `IsHakenSurfaceEmbedding`. -/
@[simp]
theorem isHakenSurfaceEmbedding_iff {f : C(S, M)} :
    IsHakenSurfaceEmbedding f ↔
      IsCompactConnectedSurface S ∧ IsCompactConnectedThreeManifold M ∧
        f ⁻¹' (𝓡∂ 3).boundary M = (𝓡∂ 2).boundary S ∧ IsBicollared f ∧
          IsIncompressible f ∧ ∃ s : S, Nontrivial (FundamentalGroup S s) :=
  Iff.rfl

end BoundaryAware

/-! ### Irreducible three-manifolds -/

/-- A three-manifold is **irreducible** when every closed locally flat embedded 2-sphere extends
across an embedded 3-ball.  The disk and its boundary are Mathlib's standard `𝔻 3` and `𝕊 2`
objects, so this is the usual tame sphere-bounds-a-ball condition. -/
def IsIrreducibleThreeManifold (M : Type u) [TopologicalSpace M] : Prop :=
  ∀ f : C((TopCat.sphere 2 : TopCat.{u}), M), IsClosedEmbedding f →
    IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
    ∃ g : C((TopCat.disk 3 : TopCat.{u}), M), IsClosedEmbedding g ∧
      g.comp (TopCat.diskBoundaryInclusion 3).hom = f

/-- The sphere-bounds-a-ball condition defining an irreducible 3-manifold. -/
@[simp]
theorem isIrreducibleThreeManifold_iff (M : Type u) [TopologicalSpace M] :
    IsIrreducibleThreeManifold M ↔
      ∀ f : C((TopCat.sphere 2 : TopCat.{u}), M), IsClosedEmbedding f →
        IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
        ∃ g : C((TopCat.disk 3 : TopCat.{u}), M), IsClosedEmbedding g ∧
          g.comp (TopCat.diskBoundaryInclusion 3).hom = f :=
  Iff.rfl

/-! ### Boundary-aware existential Haken predicate -/

section BoundaryHakenPredicate

/-- A compact connected 3-manifold is **Haken** when it admits a boundary-aware Haken surface
embedding.  The source type, its manifold structures, and the map are existential data, so this
predicate records the geometric witness rather than merely asserting an incompressible map
exists. -/
def IsHakenThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] : Prop :=
  IsCompactConnectedThreeManifold M ∧
    IsIrreducibleThreeManifold M ∧
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanHalfSpace 2) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanHalfSpace 2) S := cS
      ∃ f : C(S, M), IsHakenSurfaceEmbedding f

/-- The compactness, irreducibility, and boundary-aware surface-witness conditions defining a
Haken 3-manifold. -/
@[simp]
theorem isHakenThreeManifold_iff (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] :
    IsHakenThreeManifold M ↔
      IsCompactConnectedThreeManifold M ∧
        IsIrreducibleThreeManifold M ∧
        ∃ (S : Type u) (tS : TopologicalSpace S)
          (cS : ChartedSpace (EuclideanHalfSpace 2) S),
          letI : TopologicalSpace S := tS
          letI : ChartedSpace (EuclideanHalfSpace 2) S := cS
          ∃ f : C(S, M), IsHakenSurfaceEmbedding f :=
  Iff.rfl

/-- A boundary-aware Haken surface embedding supplies its ambient Haken predicate. -/
theorem isHakenThreeManifold_of_isHakenSurfaceEmbedding {S M : Type u}
    [TopologicalSpace S] [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) S] [ChartedSpace (EuclideanHalfSpace 3) M]
    (hirr : IsIrreducibleThreeManifold M) {f : C(S, M)}
    (h : IsHakenSurfaceEmbedding f) : IsHakenThreeManifold M := by
  rcases isHakenSurfaceEmbedding_iff.mp h with
    ⟨_hS, hM, _hboundary, _hbicollared, _hincompressible, _hnontrivial⟩
  exact ⟨hM, hirr, ⟨S, inferInstance, inferInstance, f, h⟩⟩

end BoundaryHakenPredicate

/-! ### Closed incompressible surface embeddings -/

section ClosedEmbeddings

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
conditions needed for the usual Haken witness: it is globally bicollared (hence locally flat and
two-sided), and its source has a nontrivial fundamental group, excluding the spherical case. The
separate `IsClosedIncompressibleSurfaceEmbedding` package intentionally remains the
dimension-independent topological core; a Haken predicate may existentially quantify this stronger
relation without admitting wild, one-sided, or spherical surfaces. -/
def IsClosedHakenSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsClosedIncompressibleSurfaceEmbedding f ∧
    IsBicollared f ∧ ∃ s : S, Nontrivial (FundamentalGroup S s)

/-- The defining conditions of `IsClosedHakenSurfaceEmbedding`. -/
@[simp]
theorem isClosedHakenSurfaceEmbedding_iff {f : C(S, M)} :
    IsClosedHakenSurfaceEmbedding f ↔
      IsClosedIncompressibleSurfaceEmbedding f ∧
        IsBicollared f ∧ ∃ s : S, Nontrivial (FundamentalGroup S s) :=
  Iff.rfl

end ClosedEmbeddings

section Closed

/-- A closed connected 3-manifold is **closed Haken** when it admits a closed Haken surface
embedding. The source type, its manifold structures, and the map are existential data; the witness
retains incompressibility, bicollaring, and non-sphericity (with local flatness derived from the
bicollar). -/
def IsClosedHakenThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  IsClosedConnectedThreeManifold M ∧
    IsIrreducibleThreeManifold M ∧
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := cS
      ∃ f : C(S, M), IsClosedHakenSurfaceEmbedding f

/-- The closedness, irreducibility, and closed surface-witness conditions defining a closed Haken
3-manifold. -/
@[simp]
theorem isClosedHakenThreeManifold_iff (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsClosedHakenThreeManifold M ↔
      IsClosedConnectedThreeManifold M ∧
        IsIrreducibleThreeManifold M ∧
        ∃ (S : Type u) (tS : TopologicalSpace S)
          (cS : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S),
          letI : TopologicalSpace S := tS
          letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := cS
          ∃ f : C(S, M), IsClosedHakenSurfaceEmbedding f :=
  Iff.rfl

/-- A closed Haken surface embedding supplies its ambient closed-Haken predicate. -/
theorem isClosedHakenThreeManifold_of_isClosedHakenSurfaceEmbedding {S M : Type u}
    [TopologicalSpace S] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (hirr : IsIrreducibleThreeManifold M) {f : C(S, M)}
    (h : IsClosedHakenSurfaceEmbedding f) : IsClosedHakenThreeManifold M := by
  rcases isClosedHakenSurfaceEmbedding_iff.mp h with
    ⟨hincompressible, _hbicollared, _hnontrivial⟩
  rcases isClosedIncompressibleSurfaceEmbedding_iff.mp hincompressible with
    ⟨_hS, hM, _hincompressible⟩
  exact ⟨hM, hirr, ⟨S, inferInstance, inferInstance, f, h⟩⟩

end Closed

end TauCeti
