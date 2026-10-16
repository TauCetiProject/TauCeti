/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Disjoint
public import TauCeti.KnotTheory.Grid.Differential.Square.SideOverlap

/-!
# Overlap orientations in the grid-commutation homotopy equation

After the disjoint rectangle--hexagon terms cancel, the commutation homotopy equation separates
into two geometric cases. On the diagonal, both underlying rectangles use the same pair of side
columns. Off the diagonal, they share exactly one side, either with the same orientation or with
opposite orientations.

This file makes that separation exact for both orders of composition. It splits each off-diagonal
hexagon--rectangle sum into its same-side and mixed-side parts and rewrites the full homotopy
equation as a diagonal identity together with the oriented off-diagonal identity. These are the
two inputs for matching the remaining terms with pairs of forward and reverse commutation
pentagons.

## Main results

* `TauCeti.GridDiagram.sum_hexagonRectangle_overlap_eq_sameSide_add_mixedSide` and
  `TauCeti.GridDiagram.sum_rectangleHexagon_overlap_eq_sameSide_add_mixedSide` split the two
  off-diagonal overlap sums by orientation.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff_oriented_overlap`
  separates the homotopy equation into its diagonal and oriented off-diagonal coefficient
  identities.

## References

This is the case division in the hexagon--rectangle juxtaposition argument of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

open scoped Classical in
/-- The off-diagonal hexagon--rectangle overlap sum is the sum of its same-side and mixed-side
parts. -/
theorem sum_hexagonRectangle_overlap_eq_sameSide_add_mixedSide
    {M : Type*} [AddCommMonoid M] (S : Finset
      (GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z))
    (w : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z → M)
    (hzx : z ≠ x) :
    ∑ D ∈ S.filter (fun D => ¬D.toRectangleDecomposition.HasDisjointSides), w D =
      (∑ D ∈ S.filter (fun D => D.toRectangleDecomposition.HasSameSideOverlap), w D) +
        ∑ D ∈ S.filter (fun D => D.toRectangleDecomposition.HasMixedSideOverlap), w D := by
  exact GridRectangleDecomposition.sum_filter_not_hasDisjointSides_eq_sameSide_add_mixedSide S
    GridHexagonRectangleDecomposition.toRectangleDecomposition w hzx

open scoped Classical in
/-- The off-diagonal rectangle--hexagon overlap sum is the sum of its same-side and mixed-side
parts. -/
theorem sum_rectangleHexagon_overlap_eq_sameSide_add_mixedSide
    {M : Type*} [AddCommMonoid M] (S : Finset
      (GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z))
    (w : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z → M)
    (hzx : z ≠ x) :
    ∑ D ∈ S.filter (fun D => ¬D.toRectangleDecomposition.HasDisjointSides), w D =
      (∑ D ∈ S.filter (fun D => D.toRectangleDecomposition.HasSameSideOverlap), w D) +
        ∑ D ∈ S.filter (fun D => D.toRectangleDecomposition.HasMixedSideOverlap), w D := by
  exact GridRectangleDecomposition.sum_filter_not_hasDisjointSides_eq_sameSide_add_mixedSide S
    GridRectangleHexagonDecomposition.toRectangleDecomposition w hzx

variable (R : Type*) [CommSemiring R] [CharP R 2]

open scoped Classical in
/-- The commutation homotopy equation holds exactly when its diagonal coefficient identity and
its off-diagonal same-side and mixed-side overlap identity both hold. -/
theorem unblockedDifferential_commutationHomotopy_add_eq_iff_oriented_overlap :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.commutationHomotopy R C c) +
          G.commutationHomotopy R C (G.unblockedDifferential R c) =
        c + (G.swapColumns C.column (finRotate n C.column)).commutationMap R C.reverse
          (G.commutationMap R C c)) ↔
      (∀ x : GridState n,
        (∑ D ∈ G.hexagonRectangleDecompositions C x x, G.hexagonRectangleWeight C R D) +
            ∑ D ∈ G.rectangleHexagonDecompositions C x x,
              G.rectangleHexagonWeight C R D =
          1 + ∑ D ∈ G.pentagonPairDecompositions C x x, G.pentagonPairWeight C R D) ∧
      ∀ x z : GridState n, z ≠ x →
        ((∑ D ∈ (G.hexagonRectangleDecompositions C x z).filter
                (fun D => D.toRectangleDecomposition.HasSameSideOverlap),
              G.hexagonRectangleWeight C R D) +
            ∑ D ∈ (G.hexagonRectangleDecompositions C x z).filter
                (fun D => D.toRectangleDecomposition.HasMixedSideOverlap),
              G.hexagonRectangleWeight C R D) +
          ((∑ D ∈ (G.rectangleHexagonDecompositions C x z).filter
                (fun D => D.toRectangleDecomposition.HasSameSideOverlap),
              G.rectangleHexagonWeight C R D) +
            ∑ D ∈ (G.rectangleHexagonDecompositions C x z).filter
                (fun D => D.toRectangleDecomposition.HasMixedSideOverlap),
              G.rectangleHexagonWeight C R D) =
        ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D := by
  rw [G.unblockedDifferential_commutationHomotopy_add_eq_iff_overlap C R]
  constructor
  · intro h
    constructor
    · intro x
      simpa only [GridRectangleDecomposition.filter_not_hasDisjointSides_eq_self,
        eq_self, ite_true] using h x x
    · intro x z hzx
      simpa only [G.sum_hexagonRectangle_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
        G.sum_rectangleHexagon_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
        ite_eq_right (Ne.symm hzx), zero_add] using h x z
  · rintro ⟨hdiag, hoff⟩ x z
    by_cases hzx : z = x
    · subst z
      simpa only [GridRectangleDecomposition.filter_not_hasDisjointSides_eq_self,
        eq_self, ite_true] using hdiag x
    · simpa only [G.sum_hexagonRectangle_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
        G.sum_rectangleHexagon_overlap_eq_sameSide_add_mixedSide C _ _ hzx,
        ite_eq_right (Ne.symm hzx), zero_add] using hoff x z hzx

end TauCeti.GridDiagram
