/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Recut
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.SameSideRecut

/-!
# Off-diagonal unpaired hexagon composites have a mixed-side overlap

On the left-hand side `∂ ∘ H + H ∘ ∂` of the homotopy equation of a column commutation, a counted
hexagon composite whose two rectangles share exactly one side column cancels against its recut
whenever that recut is again a counted composite (`Homotopy.Recut`). This file shows that this
always happens when the shared column is initial for both rectangles or terminal for both.
Consequently, off the diagonal, every unpaired composite has a mixed-side overlap.

The argument has two independent parts.

* *Markings.* A counted composite covers exactly one `X`-marking, that of the column its hexagon
  cuts away. If a repartition of its domain into two empty rectangles has a piece with the shape of
  a commutation hexagon, that piece covers the `X`-marking of its own cut-away column, which must
  therefore be the single one. Its hexagon carries no `X`-marking, the other piece carries none
  either, and the repartition is a counted composite
  (`GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition`, an instance of
  `GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition_of_mem_iff` via
  `GridDiagram.mem_commutationHexagons_iff_XSet_inter_eq`).
* *Shapes.* For a same-side overlap, the recut cuts the L-shaped union the other way, and one of
  its pieces again underlies a commutation hexagon of the same kind
  (`GridHexagonCompositeDecomposition.exists_hexagon_of_isRecut`).

## Main results

* `TauCeti.GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition`: a repartition of a
  counted composite into empty rectangles, one of which underlies a commutation hexagon, underlies
  a counted composite.
* `TauCeti.GridDiagram.exists_isRecut_of_hasSameSideOverlap`: the recut of a counted composite
  with a same-side overlap underlies a counted composite.
* `TauCeti.GridDiagram.hasMixedSideOverlap_of_mem_unpairedHexagonComposites`: off the diagonal,
  every unpaired composite has a mixed-side overlap.

## References

This is the same-side case of the hexagon--rectangle juxtaposition argument of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "a" => C.column

/-! ### Promoting a repartition to a counted composite -/

/-- The counted composites are the counted hexagons and unblocked rectangles, in either order. -/
private theorem mem_hexagonCompositeDecompositions_iff_mem_disjSum {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z) :
    F ∈ G.hexagonCompositeDecompositions C x z ↔
      F ∈ (GridTwoStepDecomposition.decompositionsOf (G.commutationHexagons C)
          G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles
          (G.commutationHexagons C) x z) := by
  cases F <;> simp

/-- A repartition of a counted composite into two empty rectangles, one of which underlies a
commutation hexagon, is the underlying rectangle decomposition of a counted composite. -/
theorem exists_toRectangleDecomposition_eq_of_isRepartition {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z) {E : GridRectangleDecomposition x z}
    (hrep : F.toRectangleDecomposition.IsRepartition E) (hfirst : E.first.IsEmpty)
    (hsecond : E.second.IsEmpty)
    (hhex : (∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow x E.middle,
        P.toGridRectangleBetween = E.first) ∨
      ∃ P : GridCommutationHexagonBetween a C.turnRow C.oppositeTurnRow E.middle z,
        P.toGridRectangleBetween = E.second) :
    ∃ F' ∈ G.hexagonCompositeDecompositions C x z, F'.toRectangleDecomposition = E := by
  obtain ⟨F', hF', hF'E⟩ := exists_toRectangleDecomposition_eq_of_isRepartition_of_mem_iff
    (G.mem_commutationHexagons_iff_XSet_inter_eq C)
    (G.cutColumn_X_mem_toGridRectangle_coveredSquares C)
    ((G.mem_hexagonCompositeDecompositions_iff_mem_disjSum C F).mp hF) hrep hfirst hsecond hhex
  exact ⟨F', (G.mem_hexagonCompositeDecompositions_iff_mem_disjSum C F').mpr hF', hF'E⟩

/-! ### Same-side composites are paired -/

/-- The recut of a counted composite whose two rectangles share a side column with the same
orientation, initial for both or terminal for both, is the underlying rectangle decomposition of a
counted composite. -/
theorem exists_isRecut_of_hasSameSideOverlap {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.hexagonCompositeDecompositions C x z)
    (hsame : F.toRectangleDecomposition.HasSameSideOverlap) :
    ∃ F' ∈ G.hexagonCompositeDecompositions C x z,
      F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition := by
  obtain ⟨F', hF', hrecut⟩ := exists_isRecut_of_hasSameSideOverlap_of_mem_iff
    (G.mem_commutationHexagons_iff_XSet_inter_eq C)
    (G.cutColumn_X_mem_toGridRectangle_coveredSquares C)
    ((G.mem_hexagonCompositeDecompositions_iff_mem_disjSum C F).mp hF) hsame
  exact ⟨F', (G.mem_hexagonCompositeDecompositions_iff_mem_disjSum C F').mpr hF', hrecut⟩

/-- Off the diagonal, every unpaired hexagon composite has a mixed-side overlap: its two
rectangles share exactly one side column, initial for one and terminal for the other. -/
theorem hasMixedSideOverlap_of_mem_unpairedHexagonComposites {x z : GridState n} (hzx : z ≠ x)
    {F : GridHexagonCompositeDecomposition a C.turnRow C.oppositeTurnRow x z}
    (hF : F ∈ G.unpairedHexagonComposites C x z) :
    F.toRectangleDecomposition.HasMixedSideOverlap := by
  obtain ⟨hF, hdisj, hnot⟩ := (G.mem_unpairedHexagonComposites C F).mp hF
  refine ((F.toRectangleDecomposition
    |>.not_hasDisjointSides_iff_sameSideOverlap_or_mixedSideOverlap_of_ne hzx).mp hdisj)
    |>.resolve_left fun hsame => ?_
  obtain ⟨F', hF', hrecut⟩ := G.exists_isRecut_of_hasSameSideOverlap C hF hsame
  exact hnot F' hF' hrecut

end TauCeti.GridDiagram
