/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Annulus.Diagonal
public import TauCeti.KnotTheory.Grid.Commutation.Disjoint.Reduction
public import TauCeti.KnotTheory.Grid.Differential.Square.SideOverlap

/-!
# Orientations of overlapping domains in grid commutation

The off-diagonal coefficients of the grid-commutation chain-map equation reduce to composite
domains whose two underlying rectangles share exactly one side column. There are four orientations
of that column. In the same-side orientations it is initial for both rectangles or terminal for
both; in the mixed-side orientations it is initial for one and terminal for the other.

This file makes that dichotomy exhaustive at the level of the four finite coefficient families:
rectangle--pentagon and pentagon--rectangle domains, for pentagons turning on either side. Each
overlap sum is split into its same-side and mixed-side summands. Together with the previously
proved diagonal identity, this rewrites the full chain-map equation as an off-diagonal identity
between those eight explicitly oriented sums. The subsequent recut argument can therefore work
only with the geometric orientations, without carrying a negated disjointness predicate.

## Main results

* `TauCeti.GridDiagram.sum_rectanglePentagon_overlap_eq_sameSide_add_mixedSide` and its
  three analogues split each overlap coefficient sum by orientation.
* `TauCeti.GridDiagram.commutationMap_comp_unblockedDifferential_eq_iff_oriented_overlap` reduces
  the chain-map equation to the oriented off-diagonal sums; diagonal coefficients are discharged
  by the annulus calculation.

## References

This is the case division in the pentagon--rectangle juxtaposition argument of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

open scoped Classical in
private theorem sum_overlap_eq_sameSide_add_mixedSide
    {α M : Type*} [AddCommMonoid M] {x z : GridState n}
    (S : Finset α) (underlying : α → GridRectangleDecomposition x z)
    (w : α → M) (hzx : z ≠ x) :
    ∑ D ∈ S.filter (fun D => ¬(underlying D).HasDisjointSides), w D =
      (∑ D ∈ S.filter (fun D => (underlying D).HasSameSideOverlap), w D) +
        ∑ D ∈ S.filter (fun D => (underlying D).HasMixedSideOverlap), w D := by
  classical
  have horientation (D : α) :
      ¬(underlying D).HasDisjointSides ↔
        (underlying D).HasSameSideOverlap ∨ (underlying D).HasMixedSideOverlap := by
    constructor
    · intro hdisjoint
      have hone := ((underlying D).hasDisjointSides_or_hasOneCommonSide_of_ne hzx).resolve_left
        hdisjoint
      exact (underlying D).hasSameSideOverlap_or_hasMixedSideOverlap hone
    · rintro (hsame | hmixed)
      · exact (underlying D).not_hasDisjointSides_of_hasOneCommonSide
          ((underlying D).hasSameSideOverlap_iff.mp hsame).1
      · exact (underlying D).not_hasDisjointSides_of_hasOneCommonSide
          ((underlying D).hasMixedSideOverlap_iff.mp hmixed).1
  have hunion :
      S.filter (fun D => ¬(underlying D).HasDisjointSides) =
        S.filter (fun D => (underlying D).HasSameSideOverlap) ∪
          S.filter (fun D => (underlying D).HasMixedSideOverlap) := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_union, ← and_or_left, horientation]
  have hdisjoint : Disjoint
      (S.filter (fun D => (underlying D).HasSameSideOverlap))
      (S.filter (fun D => (underlying D).HasMixedSideOverlap)) := by
    rw [Finset.disjoint_filter]
    intro D _ hsame
    exact (underlying D).not_hasMixedSideOverlap_of_hasSameSideOverlap hsame
  rw [hunion, Finset.sum_union hdisjoint]

open scoped Classical in
/-- The off-diagonal rectangle--pentagon overlap sum is the sum of its same-side and mixed-side
parts. -/
theorem sum_rectanglePentagon_overlap_eq_sameSide_add_mixedSide
    {M : Type*} [AddCommMonoid M] (S : Finset (GridRectanglePentagonDecomposition
      C.column C.turnRow x z)) (w : GridRectanglePentagonDecomposition
        C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ D ∈ S.filter (fun D => ¬D.HasDisjointSides), w D =
      (∑ D ∈ S.filter (fun D => D.toRectangleDecomposition.HasSameSideOverlap), w D) +
        ∑ D ∈ S.filter (fun D => D.toRectangleDecomposition.HasMixedSideOverlap), w D := by
  simpa only [GridRectanglePentagonDecomposition.hasDisjointSides_def] using
    sum_overlap_eq_sameSide_add_mixedSide S
      GridRectanglePentagonDecomposition.toRectangleDecomposition w hzx

open scoped Classical in
/-- The off-diagonal pentagon--rectangle overlap sum is the sum of its same-side and mixed-side
parts. -/
theorem sum_pentagonRectangle_overlap_eq_sameSide_add_mixedSide
    {M : Type*} [AddCommMonoid M] (S : Finset (GridPentagonRectangleDecomposition
      C.column C.turnRow x z)) (w : GridPentagonRectangleDecomposition
        C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ D ∈ S.filter (fun D => ¬D.HasDisjointSides), w D =
      (∑ D ∈ S.filter (fun D => D.toRectangleDecomposition.HasSameSideOverlap), w D) +
        ∑ D ∈ S.filter (fun D => D.toRectangleDecomposition.HasMixedSideOverlap), w D := by
  simpa only [GridPentagonRectangleDecomposition.hasDisjointSides_def] using
    sum_overlap_eq_sameSide_add_mixedSide S
      GridPentagonRectangleDecomposition.toRectangleDecomposition w hzx

open scoped Classical in
/-- The off-diagonal rectangle--initial-pentagon overlap sum is the sum of its same-side and
mixed-side parts. -/
theorem sum_rectangleInitialPentagon_overlap_eq_sameSide_add_mixedSide
    {M : Type*} [AddCommMonoid M] (S : Finset (GridRectangleInitialPentagonDecomposition
      C.column C.turnRow x z)) (w : GridRectangleInitialPentagonDecomposition
        C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ D ∈ S.filter (fun D => ¬D.toGridRectangleDecomposition.HasDisjointSides), w D =
      (∑ D ∈ S.filter (fun D =>
          D.toGridRectangleDecomposition.HasSameSideOverlap), w D) +
        ∑ D ∈ S.filter (fun D =>
          D.toGridRectangleDecomposition.HasMixedSideOverlap), w D := by
  exact sum_overlap_eq_sameSide_add_mixedSide S
    GridRectangleInitialPentagonDecomposition.toGridRectangleDecomposition w hzx

open scoped Classical in
/-- The off-diagonal initial-pentagon--rectangle overlap sum is the sum of its same-side and
mixed-side parts. -/
theorem sum_initialPentagonRectangle_overlap_eq_sameSide_add_mixedSide
    {M : Type*} [AddCommMonoid M] (S : Finset (GridInitialPentagonRectangleDecomposition
      C.column C.turnRow x z)) (w : GridInitialPentagonRectangleDecomposition
        C.column C.turnRow x z → M) (hzx : z ≠ x) :
    ∑ D ∈ S.filter (fun D => ¬D.toGridRectangleDecomposition.HasDisjointSides), w D =
      (∑ D ∈ S.filter (fun D =>
          D.toGridRectangleDecomposition.HasSameSideOverlap), w D) +
        ∑ D ∈ S.filter (fun D =>
          D.toGridRectangleDecomposition.HasMixedSideOverlap), w D := by
  exact sum_overlap_eq_sameSide_add_mixedSide S
    GridInitialPentagonRectangleDecomposition.toGridRectangleDecomposition w hzx

variable (R : Type*) [CommSemiring R] [IsCancelAdd R] [CharP R 2]

open scoped Classical in
/-- The commutation map is a chain map exactly when its off-diagonal same-side and mixed-side
overlap contributions agree. The diagonal coefficients are already the thin-annulus identity. -/
theorem commutationMap_comp_unblockedDifferential_eq_iff_oriented_overlap :
    (G.commutationMap R C).comp (G.unblockedDifferential R) =
        ((G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R).comp
          (G.commutationMap R C) ↔
      ∀ x z : GridState n, z ≠ x →
        ((∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter
              (fun D => D.toRectangleDecomposition.HasSameSideOverlap),
              G.rectanglePentagonWeight C R D) +
            ∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter
              (fun D => D.toRectangleDecomposition.HasMixedSideOverlap),
              G.rectanglePentagonWeight C R D) +
          ((∑ D ∈ (G.rectangleInitialPentagonDecompositions C x z).filter
              (fun D => D.toGridRectangleDecomposition.HasSameSideOverlap),
              G.rectangleInitialPentagonWeight C R D) +
            ∑ D ∈ (G.rectangleInitialPentagonDecompositions C x z).filter
              (fun D => D.toGridRectangleDecomposition.HasMixedSideOverlap),
              G.rectangleInitialPentagonWeight C R D) =
        ((∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
              (fun D => D.toRectangleDecomposition.HasSameSideOverlap),
              G.pentagonRectangleWeight C R D) +
            ∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
              (fun D => D.toRectangleDecomposition.HasMixedSideOverlap),
              G.pentagonRectangleWeight C R D) +
          ((∑ D ∈ (G.initialPentagonRectangleDecompositions C x z).filter
              (fun D => D.toGridRectangleDecomposition.HasSameSideOverlap),
              G.initialPentagonRectangleWeight C R D) +
            ∑ D ∈ (G.initialPentagonRectangleDecompositions C x z).filter
              (fun D => D.toGridRectangleDecomposition.HasMixedSideOverlap),
              G.initialPentagonRectangleWeight C R D) := by
  rw [G.commutationMap_comp_unblockedDifferential_eq_iff_overlap C R]
  constructor
  · intro h x z hzx
    simpa only [G.sum_rectanglePentagon_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
      G.sum_rectangleInitialPentagon_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
      G.sum_pentagonRectangle_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
      G.sum_initialPentagonRectangle_overlap_eq_sameSide_add_mixedSide C _ _ hzx]
      using h x z
  · intro h x z
    by_cases hzx : z = x
    · subst z
      have hrp : (G.rectanglePentagonDecompositions C x x).filter
          (fun D => ¬D.HasDisjointSides) = G.rectanglePentagonDecompositions C x x :=
        Finset.filter_true_of_mem fun D _ hD =>
          D.toRectangleDecomposition.target_ne_source_of_hasDisjointSides
            (D.hasDisjointSides_def.mp hD) rfl
      have hpr : (G.pentagonRectangleDecompositions C x x).filter
          (fun D => ¬D.HasDisjointSides) = G.pentagonRectangleDecompositions C x x :=
        Finset.filter_true_of_mem fun D _ hD =>
          D.toRectangleDecomposition.target_ne_source_of_hasDisjointSides
            (D.hasDisjointSides_def.mp hD) rfl
      have hrip : (G.rectangleInitialPentagonDecompositions C x x).filter
          (fun D => ¬D.toGridRectangleDecomposition.HasDisjointSides) =
            G.rectangleInitialPentagonDecompositions C x x :=
        Finset.filter_true_of_mem fun D _ hD =>
          D.toGridRectangleDecomposition.target_ne_source_of_hasDisjointSides hD rfl
      have hipr : (G.initialPentagonRectangleDecompositions C x x).filter
          (fun D => ¬D.toGridRectangleDecomposition.HasDisjointSides) =
            G.initialPentagonRectangleDecompositions C x x :=
        Finset.filter_true_of_mem fun D _ hD =>
          D.toGridRectangleDecomposition.target_ne_source_of_hasDisjointSides hD rfl
      simpa only [hrp, hpr, hrip, hipr] using
        G.sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_self C R x
    · simpa only [G.sum_rectanglePentagon_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
        G.sum_rectangleInitialPentagon_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
        G.sum_pentagonRectangle_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
        G.sum_initialPentagonRectangle_overlap_eq_sameSide_add_mixedSide C _ _ hzx]
        using h x z hzx

end TauCeti.GridDiagram
