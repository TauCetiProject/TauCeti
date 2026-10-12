/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Incompressible
public import TauCeti.Geometry.Manifold.Irreducible

/-!
# Compact surfaces and Haken embeddings

This file packages the manifold hypotheses used for the Haken condition in dimension three.
The relation `IsHakenSurfaceEmbedding` combines the standard surface and three-manifold
specializations from `Geometry.Manifold.Basic` with
boundary preservation, a bicollar, and Tau Ceti's dimension-independent `IsIncompressible`
predicate.  A boundary-bearing witness may be a disk; a boundaryless witness must have infinite
fundamental group, excluding spherical and projective-plane witnesses.  The closed specialization
`IsClosedHakenSurfaceEmbedding` uses boundaryless Euclidean-space models and omits the
boundary-preservation conjunct.

The imported incompressible-surface API includes the basic product-slice witness: a continuous
retraction onto the first factor makes the inclusion of a surface as a slice incompressible. The
imported irreducibility API supplies `IsSphereBoundsBall`. These are the standard ingredients used
when introducing Haken manifolds; the definitions here follow Hatcher, *Notes on Basic 3-Manifold
Topology*, Sections 1.1--1.2, and Jaco, *Lectures on Three-Manifold Topology*, Chapter II.

## Main definitions

* `TauCeti.IsHakenSurfaceEmbedding`: a proper, incompressible witness with either nonempty
  boundary or infinite fundamental group for Haken-ness, allowing boundary.
* `TauCeti.IsClosedHakenSurfaceEmbedding`: the closed, bicollared specialization.
* `TauCeti.IsPossiblyNonorientableHakenThreeManifold` and
  `TauCeti.IsPossiblyNonorientableClosedHakenThreeManifold`: the corresponding irreducible
  existential Haken predicates for ambient 3-manifolds. They record no orientability hypothesis,
  allowing results that require orientability to impose it separately.

## Main results

* `TauCeti.isHakenSurfaceEmbedding_iff` exposes the additional Haken-witness conditions.
* `TauCeti.isClosedHakenSurfaceEmbedding_iff` characterizes the closed specialization.
* `TauCeti.IsPossiblyNonorientableHakenThreeManifold.exists_isOpen_sdiff_range_eq_union` and its
  closed analogue expose the two-sided complement supplied by the existential surface witness.
* `TauCeti.IsPossiblyNonorientableClosedHakenThreeManifold.isClosedConnectedThreeManifold`: a
  closed Haken 3-manifold is a closed connected 3-manifold.
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
has two sides even where it meets the boundary. It is also incompressible, and either has
nonempty boundary or has infinite fundamental group. -/
def IsHakenSurfaceEmbedding (f : C(S, M)) : Prop :=
  IsCompactConnectedSurface S ∧ IsCompactConnectedThreeManifold M ∧
    f ⁻¹' (𝓡∂ 3).boundary M = (𝓡∂ 2).boundary S ∧ IsBicollared f ∧
      IsIncompressible f ∧
        (((𝓡∂ 2).boundary S).Nonempty ∨ ∃ s : S, Infinite (FundamentalGroup S s))

/-- The defining compact, boundary-preserving, bicollared, incompressible, and non-spherical
conditions of `IsHakenSurfaceEmbedding`. -/
@[simp]
theorem isHakenSurfaceEmbedding_iff {f : C(S, M)} :
    IsHakenSurfaceEmbedding f ↔
      IsCompactConnectedSurface S ∧ IsCompactConnectedThreeManifold M ∧
        f ⁻¹' (𝓡∂ 3).boundary M = (𝓡∂ 2).boundary S ∧ IsBicollared f ∧
          IsIncompressible f ∧
            (((𝓡∂ 2).boundary S).Nonempty ∨ ∃ s : S, Infinite (FundamentalGroup S s)) :=
  Iff.rfl

end BoundaryAware

/-! ### Boundary-aware existential Haken predicate -/

section BoundaryHakenPredicate

/-- A compact connected irreducible 3-manifold is possibly nonorientable Haken when it admits a
boundary-aware Haken surface embedding. The source type, its manifold structures, and the map are
existential data, so this predicate records the geometric witness rather than merely asserting an
incompressible map exists. Orientability is intentionally left as a separate hypothesis. -/
def IsPossiblyNonorientableHakenThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] : Prop :=
  IsSphereBoundsBall M ∧
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanHalfSpace 2) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanHalfSpace 2) S := cS
      ∃ f : C(S, M), IsHakenSurfaceEmbedding f

/-- The irreducibility and boundary-aware surface-witness conditions defining a possibly
nonorientable Haken 3-manifold. The ambient compact-connected package is carried by the surface
witness. -/
@[simp]
theorem isPossiblyNonorientableHakenThreeManifold_iff (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] :
    IsPossiblyNonorientableHakenThreeManifold M ↔
      IsSphereBoundsBall M ∧
        ∃ (S : Type u) (tS : TopologicalSpace S)
          (cS : ChartedSpace (EuclideanHalfSpace 2) S),
          letI : TopologicalSpace S := tS
          letI : ChartedSpace (EuclideanHalfSpace 2) S := cS
          ∃ f : C(S, M), IsHakenSurfaceEmbedding f :=
  Iff.rfl

/-- A boundary-aware Haken surface embedding supplies its ambient possibly nonorientable Haken
predicate when the sphere-bounds-a-ball condition holds. -/
theorem
    isPossiblyNonorientableHakenThreeManifold_of_isSphereBoundsBall_of_isHakenSurfaceEmbedding
    {S M : Type u}
    [TopologicalSpace S] [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) S] [ChartedSpace (EuclideanHalfSpace 3) M]
    (hirr : IsSphereBoundsBall M) {f : C(S, M)}
    (h : IsHakenSurfaceEmbedding f) : IsPossiblyNonorientableHakenThreeManifold M := by
  exact (isPossiblyNonorientableHakenThreeManifold_iff M).mpr
    ⟨hirr, ⟨S, inferInstance, inferInstance, f, h⟩⟩

namespace IsPossiblyNonorientableHakenThreeManifold

/-- A possibly nonorientable Haken 3-manifold contains a surface with a two-sided open
neighbourhood: the complement of
the surface in that neighbourhood is the union of two disjoint nonempty open sets. -/
theorem exists_isOpen_sdiff_range_eq_union {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    (h : IsPossiblyNonorientableHakenThreeManifold M) :
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanHalfSpace 2) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanHalfSpace 2) S := cS
      ∃ (f : C(S, M)) (U V W : Set M),
        IsHakenSurfaceEmbedding f ∧ IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ range f ⊆ U ∧
          V.Nonempty ∧ W.Nonempty ∧ Disjoint V W ∧ U \ range f = V ∪ W := by
  rcases (isPossiblyNonorientableHakenThreeManifold_iff M).mp h with
    ⟨_hirr, ⟨S, tS, cS, f, hf⟩⟩
  rcases isHakenSurfaceEmbedding_iff.mp hf with
    ⟨hS, hM, hboundary, hb, hincompressible, hsurface⟩
  let _ : Nonempty S := by
    rcases hsurface with ⟨s, _⟩ | ⟨s, _⟩
    · exact ⟨s⟩
    · exact ⟨s⟩
  rcases hb.exists_isOpen_sdiff_range_eq_union with ⟨U, V, W, hU, hV, hW, hrange,
    hVne, hWne, hdisjoint, hsdiff⟩
  exact ⟨S, tS, cS, f, U, V, W, isHakenSurfaceEmbedding_iff.mpr
    ⟨hS, hM, hboundary, hb, hincompressible, hsurface⟩,
    hU, hV, hW, hrange, hVne, hWne, hdisjoint, hsdiff⟩

end IsPossiblyNonorientableHakenThreeManifold

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

/-- An irreducible closed connected 3-manifold is possibly nonorientable closed Haken when it admits
a closed Haken surface embedding. The source type, its manifold structures, and the map are
existential data; the witness retains incompressibility, bicollaring, and non-sphericity (with
local flatness derived from the bicollar). Orientability is intentionally left as a separate
hypothesis. -/
def IsPossiblyNonorientableClosedHakenThreeManifold (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  IsSphereBoundsBall M ∧
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := cS
      ∃ f : C(S, M), IsClosedHakenSurfaceEmbedding f

/-- The irreducibility and closed surface-witness conditions defining a possibly nonorientable
closed Haken 3-manifold. The ambient closed-connected package is carried by the surface witness. -/
@[simp]
theorem isPossiblyNonorientableClosedHakenThreeManifold_iff (M : Type u)
    [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    IsPossiblyNonorientableClosedHakenThreeManifold M ↔
      IsSphereBoundsBall M ∧
        ∃ (S : Type u) (tS : TopologicalSpace S)
          (cS : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S),
          letI : TopologicalSpace S := tS
          letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := cS
          ∃ f : C(S, M), IsClosedHakenSurfaceEmbedding f :=
  Iff.rfl

namespace IsPossiblyNonorientableClosedHakenThreeManifold

/-- A possibly nonorientable closed Haken 3-manifold is a closed connected 3-manifold, as the
ambient space of its surface witness. -/
theorem isClosedConnectedThreeManifold {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (h : IsPossiblyNonorientableClosedHakenThreeManifold M) : IsClosedConnectedThreeManifold M := by
  rcases (isPossiblyNonorientableClosedHakenThreeManifold_iff M).mp h with
    ⟨_hirr, ⟨S, tS, cS, f, hf⟩⟩
  exact (isClosedIncompressibleSurfaceEmbedding_iff.mp
    (isClosedHakenSurfaceEmbedding_iff.mp hf).1).2.1

/-- A closed Haken surface embedding supplies its ambient possibly nonorientable closed-Haken
predicate when the sphere-bounds-a-ball condition holds. -/
theorem of_isSphereBoundsBall_of_isClosedHakenSurfaceEmbedding
    {S M : Type u}
    [TopologicalSpace S] [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (hirr : IsSphereBoundsBall M) {f : C(S, M)}
    (h : IsClosedHakenSurfaceEmbedding f) :
      IsPossiblyNonorientableClosedHakenThreeManifold M := by
  exact (isPossiblyNonorientableClosedHakenThreeManifold_iff M).mpr
    ⟨hirr, ⟨S, inferInstance, inferInstance, f, h⟩⟩

/-- A possibly nonorientable closed Haken 3-manifold contains a surface with a two-sided open
neighbourhood: the
complement of the surface in that neighbourhood is the union of two disjoint nonempty open sets. -/
theorem exists_isOpen_sdiff_range_eq_union {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (h : IsPossiblyNonorientableClosedHakenThreeManifold M) :
    ∃ (S : Type u) (tS : TopologicalSpace S)
      (cS : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S),
      letI : TopologicalSpace S := tS
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := cS
      ∃ (f : C(S, M)) (U V W : Set M),
        IsClosedHakenSurfaceEmbedding f ∧ IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ range f ⊆ U ∧
          V.Nonempty ∧ W.Nonempty ∧ Disjoint V W ∧ U \ range f = V ∪ W := by
  rcases (isPossiblyNonorientableClosedHakenThreeManifold_iff M).mp h with
    ⟨_hirr, ⟨S, tS, cS, f, hf⟩⟩
  rcases isClosedHakenSurfaceEmbedding_iff.mp hf with ⟨hincompressible, hb, s, hs⟩
  let _ : Nonempty S := ⟨s⟩
  rcases hb.exists_isOpen_sdiff_range_eq_union with ⟨U, V, W, hU, hV, hW, hrange,
    hVne, hWne, hdisjoint, hsdiff⟩
  exact ⟨S, tS, cS, f, U, V, W, isClosedHakenSurfaceEmbedding_iff.mpr
    ⟨hincompressible, hb, s, hs⟩,
    hU, hV, hW, hrange, hVne, hWne, hdisjoint, hsdiff⟩

end IsPossiblyNonorientableClosedHakenThreeManifold

end Closed

end TauCeti
