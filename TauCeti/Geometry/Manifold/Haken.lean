/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Geometry.Manifold.Incompressible
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Compact surfaces and Haken embeddings

This file packages the manifold hypotheses used for the Haken condition in dimension three.
The relation `IsHakenSurfaceEmbedding` combines the standard surface and three-manifold
specializations from `Geometry.Manifold.Basic` with
boundary preservation, a bicollar, and Tau Ceti's dimension-independent `IsIncompressible`
predicate.  The surface witness has infinite fundamental group, excluding both spherical and
projective-plane witnesses.  The closed specialization `IsClosedHakenSurfaceEmbedding` uses
boundaryless Euclidean-space models and omits the boundary-preservation conjunct.

The product-slice witness is the basic example: a continuous retraction onto the first factor
makes the inclusion of a surface as a slice incompressible.  This is the standard elementary
example used when introducing Haken manifolds; the definitions follow Hatcher, *Notes on Basic
3-Manifold Topology*, Sections 1.1--1.2, and Jaco, *Lectures on Three-Manifold Topology*,
Chapter II.

## Main definitions

* `TauCeti.IsClosedIncompressibleSurfaceEmbedding`: a closed connected surface embedded
  incompressibly in a closed connected 3-manifold.
* `TauCeti.IsHakenSurfaceEmbedding`: a proper, incompressible witness with infinite fundamental
  group for Haken-ness, allowing boundary.
* `TauCeti.IsClosedHakenSurfaceEmbedding`: the closed, bicollared specialization.
* `TauCeti.IsSphereBoundsBall`: every closed locally flat embedded 2-sphere bounds an embedded
  3-ball.
* `TauCeti.IsHakenThreeManifold` and `TauCeti.IsClosedHakenThreeManifold`: the corresponding
  irreducible existential Haken predicates for ambient 3-manifolds.

## Main results

* `TauCeti.isClosedIncompressibleSurfaceEmbedding_iff` exposes the three defining conditions.
* `TauCeti.isClosedIncompressibleSurfaceEmbedding_of_leftInverse` and
  `TauCeti.isClosedIncompressibleSurfaceEmbedding_prodMk` provide reusable incompressible-surface
  witnesses.
* `TauCeti.isHakenSurfaceEmbedding_iff` exposes the additional Haken-witness conditions.
* `TauCeti.IsHakenThreeManifold.exists_isOpen_sdiff_range_eq_union` and its closed analogue expose
  the two-sided complement supplied by the existential surface witness.
-/

public section

open Set Topology

open scoped Manifold ContDiff TopCat

namespace TauCeti

universe u

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-! ### Boundary-aware Haken witnesses -/

section BoundaryAware

variable [ChartedSpace (EuclideanHalfSpace 2) S]
  [ChartedSpace (EuclideanHalfSpace 3) M]

/-- A **Haken surface embedding** allows the standard properly embedded, boundary-bearing witness.
It preserves the manifold boundary exactly and is bicollared in the relative model
`EuclideanHalfSpace 2 × ℝ`, hence is locally flat and a closed embedding. Thus interior points
cannot land on the ambient boundary, boundary points cannot land in the interior, and the surface
has two sides even where it meets the boundary. It is also incompressible with infinite
fundamental group. -/
def IsHakenSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsCompactConnectedSurface S ∧ IsCompactConnectedThreeManifold M ∧
    f ⁻¹' (𝓡∂ 3).boundary M = (𝓡∂ 2).boundary S ∧ IsBicollared f ∧
      IsIncompressible f ∧ ∃ s : S, Infinite (FundamentalGroup S s)

/-- The defining compact, boundary-preserving, bicollared, incompressible, and infinite
fundamental-group
conditions of `IsHakenSurfaceEmbedding`. -/
@[simp]
theorem isHakenSurfaceEmbedding_iff {f : C(S, M)} :
    IsHakenSurfaceEmbedding f ↔
      IsCompactConnectedSurface S ∧ IsCompactConnectedThreeManifold M ∧
        f ⁻¹' (𝓡∂ 3).boundary M = (𝓡∂ 2).boundary S ∧ IsBicollared f ∧
          IsIncompressible f ∧ ∃ s : S, Infinite (FundamentalGroup S s) :=
  Iff.rfl

end BoundaryAware

/-! ### Sphere-bounds-a-ball condition -/

/-- A space satisfies the sphere-bounds-a-ball condition when every closed locally flat embedded
2-sphere extends across an embedded 3-ball. The disk and its boundary are Mathlib's standard `𝔻 3`
and `𝕊 2` objects, so this is the usual tame condition used in irreducible 3-manifolds. -/
def IsSphereBoundsBall (M : Type u) [TopologicalSpace M] : Prop :=
  ∀ f : C((TopCat.sphere 2 : TopCat.{u}), M), IsClosedEmbedding f →
    IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
    ∃ g : C((TopCat.disk 3 : TopCat.{u}), M), IsClosedEmbedding g ∧
      g.comp (TopCat.diskBoundaryInclusion 3).hom = f

/-- The sphere-bounds-a-ball condition defining `IsSphereBoundsBall`. -/
@[simp]
theorem isSphereBoundsBall_iff (M : Type u) [TopologicalSpace M] :
    IsSphereBoundsBall M ↔
      ∀ f : C((TopCat.sphere 2 : TopCat.{u}), M), IsClosedEmbedding f →
        IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
        ∃ g : C((TopCat.disk 3 : TopCat.{u}), M), IsClosedEmbedding g ∧
          g.comp (TopCat.diskBoundaryInclusion 3).hom = f :=
  Iff.rfl

/-! ### Boundary-aware existential Haken predicate -/

section BoundaryHakenPredicate

/-- A compact connected **irreducible** 3-manifold is **Haken** when it admits a boundary-aware
Haken surface embedding. The source type, its manifold structures, and the map are existential
data, so this predicate records the geometric witness rather than merely asserting an
incompressible map exists. -/
def IsHakenThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] : Prop :=
  IsSphereBoundsBall M ∧
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanHalfSpace 2) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanHalfSpace 2) S := cS
      ∃ f : C(S, M), IsHakenSurfaceEmbedding f

/-- The irreducibility and boundary-aware surface-witness conditions defining a Haken 3-manifold.
The ambient compact-connected package is carried by the surface witness. -/
@[simp]
theorem isHakenThreeManifold_iff (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] :
    IsHakenThreeManifold M ↔
      IsSphereBoundsBall M ∧
        ∃ (S : Type u) (tS : TopologicalSpace S)
          (cS : ChartedSpace (EuclideanHalfSpace 2) S),
          letI : TopologicalSpace S := tS
          letI : ChartedSpace (EuclideanHalfSpace 2) S := cS
          ∃ f : C(S, M), IsHakenSurfaceEmbedding f :=
  Iff.rfl

/-- A boundary-aware Haken surface embedding supplies its ambient Haken predicate when the ambient
sphere-bounds-a-ball condition holds. -/
theorem isHakenThreeManifold_of_isSphereBoundsBall_of_isHakenSurfaceEmbedding {S M : Type u}
    [TopologicalSpace S] [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) S] [ChartedSpace (EuclideanHalfSpace 3) M]
    (hirr : IsSphereBoundsBall M) {f : C(S, M)}
    (h : IsHakenSurfaceEmbedding f) : IsHakenThreeManifold M := by
  exact (isHakenThreeManifold_iff M).mpr ⟨hirr, ⟨S, inferInstance, inferInstance, f, h⟩⟩

namespace IsHakenThreeManifold

/-- A Haken 3-manifold contains a surface with a two-sided open neighbourhood: the complement of
the surface in that neighbourhood is the union of two disjoint nonempty open sets. -/
theorem exists_isOpen_sdiff_range_eq_union {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (h : IsHakenThreeManifold M) :
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanHalfSpace 2) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanHalfSpace 2) S := cS
      ∃ (f : C(S, M)) (U V W : Set M),
        IsHakenSurfaceEmbedding f ∧ IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ range f ⊆ U ∧
          V.Nonempty ∧ W.Nonempty ∧ Disjoint V W ∧ U \ range f = V ∪ W := by
  rcases (isHakenThreeManifold_iff M).mp h with ⟨_hirr, ⟨S, tS, cS, f, hf⟩⟩
  rcases isHakenSurfaceEmbedding_iff.mp hf with
    ⟨hS, hM, hboundary, hb, hincompressible, s, hs⟩
  let _ : Nonempty S := ⟨s⟩
  rcases hb.exists_isOpen_sdiff_range_eq_union with ⟨U, V, W, hU, hV, hW, hrange,
    hVne, hWne, hdisjoint, hsdiff⟩
  exact ⟨S, tS, cS, f, U, V, W, isHakenSurfaceEmbedding_iff.mpr
    ⟨hS, hM, hboundary, hb, hincompressible, s, hs⟩,
    hU, hV, hW, hrange, hVne, hWne, hdisjoint, hsdiff⟩

end IsHakenThreeManifold

end BoundaryHakenPredicate

section ClosedEmbeddings

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- A **closed Haken surface embedding** is a closed incompressible embedding with the geometric
conditions needed for the usual Haken witness: it is globally bicollared (hence locally flat and
two-sided), and its source has an infinite fundamental group, excluding spherical and
projective-plane cases. The
dimension-independent topological core is `IsIncompressible`; the separate
`IsClosedIncompressibleSurfaceEmbedding` package combines it with dimension-specific closed
surface and ambient-manifold predicates. A Haken predicate may existentially quantify this
stronger relation without admitting wild, one-sided, or spherical surfaces. -/
def IsClosedHakenSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsClosedIncompressibleSurfaceEmbedding f ∧
    IsBicollared f ∧ ∃ s : S, Infinite (FundamentalGroup S s)

/-- The defining conditions of `IsClosedHakenSurfaceEmbedding`. -/
@[simp]
theorem isClosedHakenSurfaceEmbedding_iff {f : C(S, M)} :
    IsClosedHakenSurfaceEmbedding f ↔
      IsClosedIncompressibleSurfaceEmbedding f ∧
        IsBicollared f ∧ ∃ s : S, Infinite (FundamentalGroup S s) :=
  Iff.rfl

end ClosedEmbeddings

section Closed

/-- An irreducible closed connected 3-manifold is **closed Haken** when it admits a closed Haken
surface embedding. The source type, its manifold structures, and the map are existential data; the
witness retains incompressibility, bicollaring, and non-sphericity (with local flatness derived
from the bicollar). -/
def IsClosedHakenThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  IsSphereBoundsBall M ∧
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := cS
      ∃ f : C(S, M), IsClosedHakenSurfaceEmbedding f

/-- The irreducibility and closed surface-witness conditions defining a closed Haken 3-manifold.
The ambient closed-connected package is carried by the surface witness. -/
@[simp]
theorem isClosedHakenThreeManifold_iff (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsClosedHakenThreeManifold M ↔
      IsSphereBoundsBall M ∧
        ∃ (S : Type u) (tS : TopologicalSpace S)
          (cS : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S),
          letI : TopologicalSpace S := tS
          letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := cS
          ∃ f : C(S, M), IsClosedHakenSurfaceEmbedding f :=
  Iff.rfl

/-- A closed Haken surface embedding supplies its ambient closed-Haken predicate when the ambient
sphere-bounds-a-ball condition holds. -/
theorem
    isClosedHakenThreeManifold_of_isSphereBoundsBall_of_isClosedHakenSurfaceEmbedding
    {S M : Type u}
    [TopologicalSpace S] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (hirr : IsSphereBoundsBall M) {f : C(S, M)}
    (h : IsClosedHakenSurfaceEmbedding f) : IsClosedHakenThreeManifold M := by
  exact (isClosedHakenThreeManifold_iff M).mpr
    ⟨hirr, ⟨S, inferInstance, inferInstance, f, h⟩⟩

namespace IsClosedHakenThreeManifold

/-- A closed Haken 3-manifold contains a surface with a two-sided open neighbourhood: the
complement of the surface in that neighbourhood is the union of two disjoint nonempty open sets. -/
theorem exists_isOpen_sdiff_range_eq_union {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (h : IsClosedHakenThreeManifold M) :
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := cS
      ∃ (f : C(S, M)) (U V W : Set M),
        IsClosedHakenSurfaceEmbedding f ∧ IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ range f ⊆ U ∧
          V.Nonempty ∧ W.Nonempty ∧ Disjoint V W ∧ U \ range f = V ∪ W := by
  rcases (isClosedHakenThreeManifold_iff M).mp h with ⟨_hirr, ⟨S, tS, cS, f, hf⟩⟩
  rcases isClosedHakenSurfaceEmbedding_iff.mp hf with ⟨hincompressible, hb, s, hs⟩
  let _ : Nonempty S := ⟨s⟩
  rcases hb.exists_isOpen_sdiff_range_eq_union with ⟨U, V, W, hU, hV, hW, hrange,
    hVne, hWne, hdisjoint, hsdiff⟩
  exact ⟨S, tS, cS, f, U, V, W, isClosedHakenSurfaceEmbedding_iff.mpr
    ⟨hincompressible, hb, s, hs⟩,
    hU, hV, hW, hrange, hVne, hWne, hdisjoint, hsdiff⟩

end IsClosedHakenThreeManifold

end Closed

end TauCeti
