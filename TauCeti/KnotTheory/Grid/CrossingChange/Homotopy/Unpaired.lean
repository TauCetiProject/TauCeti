/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Recut
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.SameSideRecut

/-!
# Off-diagonal unpaired crossing change composites have a mixed-side overlap

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row such that the annulus squares
`GridDiagram.crossingChangeAnnulusSquares C t` carry no `X`-marking, as for the crossing change
maps of interleaving columns. On the left-hand side `∂ ∘ H + H ∘ ∂` of the crossing change
homotopy equation, a counted composite whose two rectangles share exactly one side column cancels
against its recut whenever that recut is again a counted composite (`Homotopy.Recut`). This file
shows that this always happens when the shared column is initial for both rectangles or terminal
for both. Consequently, off the diagonal, every unpaired composite has a mixed-side overlap, and
only those remain to be matched with the pairs of pentagons counted by `Ψ ∘ Φ`.

The argument has two independent parts.

* *Markings.* A counted composite covers exactly one `X`-marking, that of the column its hexagon
  cuts away. The rectangle under any crossing-change hexagon covers the `X`-marking of its own
  cut-away column, and the hexagon is counted as soon as its rectangle is empty and covers no
  other `X`-marking
  (`GridDiagram.mem_crossingChangeCommutationHexagons_iff_XSet_inter_eq`). So if a repartition of
  the domain of a counted composite into two empty rectangles has a piece underlying a hexagon,
  that hexagon is counted, the other piece carries no `X`-marking, and the repartition is a
  counted composite
  (`GridDiagram.exists_crossingChange_toRectangleDecomposition_eq_of_isRepartition`). This is
  the argument shared with the column commutation,
  `GridDiagram.exists_toRectangleDecomposition_eq_of_isRepartition_of_mem_iff`.
* *Shapes.* For a same-side overlap, one piece of the recut again underlies a hexagon of the same
  kind (`GridHexagonCompositeDecomposition.exists_hexagon_of_isRecut`), exactly as for the
  homotopy of a column commutation.

## Main results

* `TauCeti.GridDiagram.exists_crossingChange_toRectangleDecomposition_eq_of_isRepartition`:
  a repartition of a counted composite into empty rectangles, one of which underlies a hexagon,
  underlies a counted composite.
* `TauCeti.GridDiagram.exists_crossingChange_isRecut_of_hasSameSideOverlap`: the
  recut of a counted composite with a same-side overlap underlies a counted composite.
* `TauCeti.GridDiagram.hasMixedSideOverlap_of_mem_crossingChangeUnpairedHexagonComposites`: off the
  diagonal, every unpaired composite has a mixed-side overlap.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 5.1 and 6.1: the juxtaposition argument for the hexagon
  homotopies of commutation and of a crossing change.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for the hexagons with corners at the two turn points.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} {G : GridDiagram n} {C : ColumnTurn n} {t : Fin n}

local notation "a" => C.column

/-! ### Promoting a repartition to a counted composite -/

/-- The counted composites are the counted hexagons and unblocked rectangles, in either order. -/
private theorem mem_crossingChangeHexagonCompositeDecompositions_iff_mem_disjSum
    {x z : GridState n} (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ↔
      F ∈ (GridTwoStepDecomposition.decompositionsOf (G.crossingChangeCommutationHexagons C t)
          G.unblockedRectangles x z).disjSum
        (GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles
          (G.crossingChangeCommutationHexagons C t) x z) := by
  cases F <;> simp

/-- If the annulus squares carry no `X`-marking, a repartition of a counted composite into two
empty rectangles, one of which underlies a crossing-change hexagon, is the underlying rectangle
decomposition of a counted composite. -/
theorem exists_crossingChange_toRectangleDecomposition_eq_of_isRepartition
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z)
    {E : GridRectangleDecomposition x z} (hrep : F.toRectangleDecomposition.IsRepartition E)
    (hfirst : E.first.IsEmpty) (hsecond : E.second.IsEmpty)
    (hhex : (∃ P : GridCommutationHexagonBetween a C.turnRow t x E.middle,
        P.toGridRectangleBetween = E.first) ∨
      ∃ P : GridCommutationHexagonBetween a C.turnRow t E.middle z,
        P.toGridRectangleBetween = E.second) :
    ∃ F' ∈ G.crossingChangeHexagonCompositeDecompositions C t x z,
      F'.toRectangleDecomposition = E := by
  obtain ⟨F', hF', hF'E⟩ := exists_toRectangleDecomposition_eq_of_isRepartition_of_mem_iff
    (mem_crossingChangeCommutationHexagons_iff_XSet_inter_eq hX)
    (cutColumn_X_mem_toGridRectangle_coveredSquares_of_disjoint_crossingChangeAnnulusSquares hX)
    ((mem_crossingChangeHexagonCompositeDecompositions_iff_mem_disjSum F).mp hF)
    hrep hfirst hsecond hhex
  exact ⟨F', (mem_crossingChangeHexagonCompositeDecompositions_iff_mem_disjSum F').mpr hF', hF'E⟩

/-! ### Same-side composites are paired -/

/-- If the annulus squares carry no `X`-marking, the recut of a counted composite whose two
rectangles share a side column with the same orientation, initial for both or terminal for both,
is the underlying rectangle decomposition of a counted composite. -/
theorem exists_crossingChange_isRecut_of_hasSameSideOverlap
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n}
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeHexagonCompositeDecompositions C t x z)
    (hsame : F.toRectangleDecomposition.HasSameSideOverlap) :
    ∃ F' ∈ G.crossingChangeHexagonCompositeDecompositions C t x z,
      F.toRectangleDecomposition.IsRecut F'.toRectangleDecomposition := by
  obtain ⟨F', hF', hrecut⟩ := exists_isRecut_of_hasSameSideOverlap_of_mem_iff
    (mem_crossingChangeCommutationHexagons_iff_XSet_inter_eq hX)
    (cutColumn_X_mem_toGridRectangle_coveredSquares_of_disjoint_crossingChangeAnnulusSquares hX)
    ((mem_crossingChangeHexagonCompositeDecompositions_iff_mem_disjSum F).mp hF) hsame
  exact ⟨F', (mem_crossingChangeHexagonCompositeDecompositions_iff_mem_disjSum F').mpr hF',
    hrecut⟩

/-- If the annulus squares carry no `X`-marking, then off the diagonal every unpaired composite of
the crossing change homotopy equation has a mixed-side overlap: its two rectangles share exactly
one side column, initial for one and terminal for the other. -/
theorem hasMixedSideOverlap_of_mem_crossingChangeUnpairedHexagonComposites
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x)
    {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeUnpairedHexagonComposites C t x z) :
    F.toRectangleDecomposition.HasMixedSideOverlap := by
  obtain ⟨hF, hdisj, hnot⟩ := (G.mem_crossingChangeUnpairedHexagonComposites C t F).mp hF
  refine ((F.toRectangleDecomposition
    |>.not_hasDisjointSides_iff_sameSideOverlap_or_mixedSideOverlap_of_ne hzx).mp hdisj)
    |>.resolve_left fun hsame => ?_
  obtain ⟨F', hF', hrecut⟩ :=
    exists_crossingChange_isRecut_of_hasSameSideOverlap hX hF hsame
  exact hnot F' hF' hrecut

end TauCeti.GridDiagram
