/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import TauCeti.KnotTheory.Grid.CrossingChange.Basic
public import TauCeti.KnotTheory.Grid.Move.Unknot

/-!
# Crossing changes and the unknotting number of grid links

A grid link is a grid diagram modulo grid moves. Two grid links differ by a crossing change when
they are presented by two diagrams related by a cross-commutation
(`GridLink.IsCrossingChange`). The unknotting number of a grid link is the least number of
crossing changes needed to turn it into the unknot (`GridLink.unknottingNumber`). It is defined as
the distance from the unknot in the graph whose edges are the crossing changes
(`GridLink.crossingChangeGraph`), so it takes values in `ℕ∞`. Crossing changes preserve the number
of components, so a grid link with several components never reaches the unknot, and its unknotting
number is `⊤`.

This is the unknotting number of the grid-diagram presentation of links. It agrees with the
classical unknotting number of the presented knot by Cromwell's theorem together with the fact,
proved in Ozsváth--Stipsicz--Szabó, that a crossing change between two knots is realised by a
cross-commutation of suitable grid diagrams; neither fact is formalised here. The definition is
the one in which the inequality `|τ(K)| ≤ u(K)` of grid homology is proved: the crossing change
maps bound the change of `τ` across a single cross-commutation, and summing along an unknotting
sequence bounds `τ` by the unknotting number.

As checks of the definition, the Hopf link has unknotting number `⊤`
(`GridLink.unknottingNumber_toGridLink_torusLink_one_one`), while the trefoil, presented by the
standard `5 × 5` grid of the `(2, 3)` torus knot, is unknotted by a single crossing change
(`GridLink.unknottingNumber_toGridLink_torusLink_one_two_le_one`), and the `(3, 4)` torus knot,
presented by its standard `7 × 7` grid, by three
(`GridLink.unknottingNumber_toGridLink_torusLink_two_three_le_three`). These are the upper bounds
`u(T_{p,q}) ≤ (p - 1) (q - 1) / 2` of the Milnor conjecture for these two torus knots, obtained
from explicit sequences of cross-commutations and commutations.

## Main definitions

* `TauCeti.GridLink.IsCrossingChange`: two grid links differ by one crossing change.
* `TauCeti.GridLink.crossingChangeGraph`: the graph on grid links whose edges are crossing
  changes.
* `TauCeti.GridLink.unknottingNumber`: the distance from the unknot in that graph.

## Main results

* `TauCeti.GridLink.unknottingNumber_eq_zero_iff`: only the unknot has unknotting number zero.
* `TauCeti.GridLink.IsCrossingChange.unknottingNumber_le`: a crossing change changes the
  unknotting number by at most one.
* `TauCeti.GridLink.isKnot_of_unknottingNumber_ne_top`: a grid link with finite unknotting number
  is a knot.
* `TauCeti.GridDiagram.unknottingNumber_toGridLink_le_swapColumns_add_one`: exchanging two
  adjacent interleaving columns changes the unknotting number by at most one.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_le_one`: the trefoil has
  unknotting number at most one.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three_le_three`: the `(3, 4)` torus
  knot has unknotting number at most three.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6: crossing changes as cross-commutations, the unknotting
  number, and the bound `|τ(K)| ≤ u(K)`.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 2.1.
-/

public section

namespace TauCeti

namespace GridLink

/-- Two grid links differ by a crossing change when they are presented by two grid diagrams
related by a cross-commutation. -/
def IsCrossingChange (L L' : GridLink) : Prop :=
  ∃ (n : ℕ) (G G' : GridDiagram n),
    G.IsCrossCommutation G' ∧ G.toGridLink = L ∧ G'.toGridLink = L'

/-- Characterization of a crossing change by presenting diagrams. -/
theorem isCrossingChange_iff (L L' : GridLink) :
    IsCrossingChange L L' ↔ ∃ (n : ℕ) (G G' : GridDiagram n),
      G.IsCrossCommutation G' ∧ G.toGridLink = L ∧ G'.toGridLink = L' :=
  Iff.rfl

/-- The grid links of two diagrams related by a cross-commutation differ by a crossing change. -/
theorem _root_.TauCeti.GridDiagram.IsCrossCommutation.isCrossingChange {n : ℕ}
    {G G' : GridDiagram n} (h : G.IsCrossCommutation G') :
    IsCrossingChange G.toGridLink G'.toGridLink :=
  ⟨n, G, G', h, rfl, rfl⟩

/-- A crossing change can be undone by a crossing change. -/
theorem IsCrossingChange.symm {L L' : GridLink} (h : IsCrossingChange L L') :
    IsCrossingChange L' L := by
  obtain ⟨n, G, G', h, rfl, rfl⟩ := h
  exact (GridDiagram.isCrossCommutation_comm.mp h).isCrossingChange

/-- The crossing change relation is symmetric. -/
theorem isCrossingChange_comm {L L' : GridLink} : IsCrossingChange L L' ↔ IsCrossingChange L' L :=
  ⟨IsCrossingChange.symm, IsCrossingChange.symm⟩

/-- A crossing change preserves the number of components. -/
theorem IsCrossingChange.componentCount_eq {L L' : GridLink} (h : IsCrossingChange L L') :
    L'.componentCount = L.componentCount := by
  obtain ⟨n, G, G', h, rfl, rfl⟩ := h
  simpa using h.componentCount_eq

/-- The crossing change graph: two distinct grid links are adjacent when they differ by a crossing
change. -/
def crossingChangeGraph : SimpleGraph GridLink where
  Adj L L' := L ≠ L' ∧ IsCrossingChange L L'
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Two grid links are adjacent in the crossing change graph exactly when they are distinct and
differ by a crossing change. -/
@[simp]
theorem crossingChangeGraph_adj {L L' : GridLink} :
    crossingChangeGraph.Adj L L' ↔ L ≠ L' ∧ IsCrossingChange L L' :=
  Iff.rfl

/-- The unknotting number of a grid link: the least number of crossing changes turning it into
the unknot, or `⊤` if no sequence of crossing changes does. -/
noncomputable def unknottingNumber (L : GridLink) : ℕ∞ :=
  crossingChangeGraph.edist L unknot

/-- The unknotting number is the distance from the unknot in the crossing change graph. -/
theorem unknottingNumber_def (L : GridLink) :
    L.unknottingNumber = crossingChangeGraph.edist L unknot :=
  (rfl)

/-- Only the unknot has unknotting number zero. -/
@[simp]
theorem unknottingNumber_eq_zero_iff {L : GridLink} : L.unknottingNumber = 0 ↔ L = unknot :=
  SimpleGraph.edist_eq_zero_iff

/-- The unknot has unknotting number zero. -/
@[simp]
theorem unknottingNumber_unknot : unknot.unknottingNumber = 0 :=
  unknottingNumber_eq_zero_iff.mpr rfl

/-- A crossing change changes the unknotting number by at most one. -/
theorem IsCrossingChange.unknottingNumber_le {L L' : GridLink} (h : IsCrossingChange L L') :
    L.unknottingNumber ≤ L'.unknottingNumber + 1 := by
  have hLL' : crossingChangeGraph.edist L L' ≤ 1 := by
    rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
    by_cases hne : L = L'
    · exact Or.inr hne
    · exact Or.inl ⟨hne, h⟩
  calc L.unknottingNumber ≤ crossingChangeGraph.edist L L' + L'.unknottingNumber :=
        SimpleGraph.edist_triangle
    _ ≤ 1 + L'.unknottingNumber := by gcongr
    _ = L'.unknottingNumber + 1 := add_comm _ _

/-- Exchanging a cyclically adjacent interleaving pair of columns of a grid diagram changes the
unknotting number of its grid link by at most one. -/
theorem _root_.TauCeti.GridDiagram.unknottingNumber_toGridLink_le_swapColumns_add_one {n : ℕ}
    (G : GridDiagram n) {a : Fin n} (h : G.ColumnsInterleaving a (finRotate n a)) :
    G.toGridLink.unknottingNumber ≤
      (G.swapColumns a (finRotate n a)).toGridLink.unknottingNumber + 1 :=
  ((GridDiagram.isCrossCommutation_iff _ _).mpr
    (Or.inr (G.isColumnCrossCommutation_swapColumns h))).isCrossingChange.unknottingNumber_le

/-- Grid links joined by a sequence of crossing changes have the same number of components. -/
private theorem componentCount_eq_of_reachable {L L' : GridLink}
    (h : crossingChangeGraph.Reachable L L') : L'.componentCount = L.componentCount := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hadj ih => exact hadj.2.componentCount_eq.trans ih

/-- A grid link with finite unknotting number is a knot: crossing changes preserve the number of
components. -/
theorem isKnot_of_unknottingNumber_ne_top {L : GridLink} (h : L.unknottingNumber ≠ ⊤) :
    L.IsKnot := by
  rw [isKnot_def, componentCount_eq_of_reachable (SimpleGraph.reachable_of_edist_ne_top h).symm,
    ← isKnot_def]
  exact isKnot_unknot

/-- The Hopf link, presented by the standard `4 × 4` grid of the `(2, 2)` torus link, has
unknotting number `⊤`: it has two components, so no sequence of crossing changes reaches the
unknot. -/
theorem unknottingNumber_toGridLink_torusLink_one_one :
    (GridDiagram.torusLink 1 1).toGridLink.unknottingNumber = ⊤ := by
  by_contra h
  have := isKnot_of_unknottingNumber_ne_top h
  rw [isKnot_toGridLink] at this
  exact GridDiagram.not_isKnot_torusLink_one_one this

/-- The standard `5 × 5` grid of the `(2, 3)` torus knot with its markings made explicit. -/
private def trefoilGrid : GridDiagram 5 where
  O := ⟨1⟩
  X := ⟨finRotate 5 ^ 3⟩
  disjoint := by decide

private theorem torusLink_one_two_eq_trefoilGrid : GridDiagram.torusLink 1 2 = trefoilGrid := by
  ext c <;> simp [trefoilGrid]

/-- The standard `5 × 5` unknot grid with its markings made explicit. -/
private def unknotGrid : GridDiagram 5 where
  O := ⟨1⟩
  X := ⟨finRotate 5⟩
  disjoint := by decide

private theorem unknot_three_eq_unknotGrid : GridDiagram.unknot 3 = unknotGrid := by
  ext c <;> simp [unknotGrid]

/-- The trefoil, presented by the standard `5 × 5` grid of the `(2, 3)` torus knot, has unknotting
number at most one. Exchanging its first two columns is a cross-commutation, and five
commutations turn the result into the standard `5 × 5` unknot grid. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_le_one :
    (GridDiagram.torusLink 1 2).toGridLink.unknottingNumber ≤ 1 := by
  rw [torusLink_one_two_eq_trefoilGrid]
  set G₀ := trefoilGrid.swapColumns 0 (finRotate 5 0)
  set G₁ := G₀.swapRows 0 (finRotate 5 0)
  set G₂ := G₁.swapRows 1 (finRotate 5 1)
  set G₃ := G₂.swapColumns 1 (finRotate 5 1)
  set G₄ := G₃.swapRows 4 (finRotate 5 4)
  have hcross : trefoilGrid.toGridLink.unknottingNumber ≤ G₀.toGridLink.unknottingNumber + 1 :=
    trefoilGrid.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 0) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have hmoves : G₀.MovesTo (GridDiagram.unknot 3) := by
    have h₅ : G₄.swapColumns 4 (finRotate 5 4) = GridDiagram.unknot 3 := by
      rw [unknot_three_eq_unknotGrid]
      ext c
      all_goals revert c; decide
    rw [← h₅]
    -- Each step exchanges an adjacent non-interleaving pair of rows or columns.
    refine (G₀.movesTo_swapRows 0 (by decide) ?_).trans <|
      (G₁.movesTo_swapRows 1 (by decide) ?_).trans <|
      (G₂.movesTo_swapColumns 1 (by decide) ?_).trans <|
      (G₃.movesTo_swapRows 4 (by decide) ?_).trans <| G₄.movesTo_swapColumns 4 (by decide) ?_
    all_goals
      simp only [GridDiagram.RowsNoninterleaving, GridDiagram.ColumnsNoninterleaving,
        Grid.Noninterleaving, Grid.mem_cIoo]
      decide
  calc trefoilGrid.toGridLink.unknottingNumber ≤ G₀.toGridLink.unknottingNumber + 1 := hcross
    _ = 1 := by
      rw [(G₀.toGridLink_eq_iff_movesTo).mpr hmoves, GridDiagram.toGridLink_unknot,
        unknottingNumber_unknot, zero_add]

/-- The standard `7 × 7` grid of the `(3, 4)` torus knot with its markings made explicit. -/
private def torusTwoThreeGrid : GridDiagram 7 where
  O := ⟨1⟩
  X := ⟨finRotate 7 ^ 4⟩
  disjoint := by decide

private theorem torusLink_two_three_eq_torusTwoThreeGrid :
    GridDiagram.torusLink 2 3 = torusTwoThreeGrid := by
  ext c <;> simp [torusTwoThreeGrid]

/-- The standard `7 × 7` unknot grid with its markings made explicit. -/
private def unknotSevenGrid : GridDiagram 7 where
  O := ⟨1⟩
  X := ⟨finRotate 7⟩
  disjoint := by decide

private theorem unknot_five_eq_unknotSevenGrid : GridDiagram.unknot 5 = unknotSevenGrid := by
  ext c <;> simp [unknotSevenGrid]

/-- The `(3, 4)` torus knot, presented by its standard `7 × 7` grid, has unknotting number at most
three. Three cross-commutations of adjacent columns, interspersed with nine commutations, turn
it into the standard `7 × 7` unknot grid.

This is the upper bound `u(T_{3,4}) ≤ (3 - 1) (4 - 1) / 2` of the Milnor conjecture for this torus
knot. -/
theorem unknottingNumber_toGridLink_torusLink_two_three_le_three :
    (GridDiagram.torusLink 2 3).toGridLink.unknottingNumber ≤ 3 := by
  rw [torusLink_two_three_eq_torusTwoThreeGrid]
  -- The diagrams `G₁`, `G₃` and `G₇` are reached by a cross-commutation (`h₁`, `h₃`, `h₇`), each
  -- of the others by a commutation; the commutations are grouped into the move sequences `h₂`,
  -- `h₆` and `h₁₂`, the last of which ends at the standard unknot grid.
  set G₁ := torusTwoThreeGrid.swapColumns 0 (finRotate 7 0)
  set G₂ := G₁.swapRows 0 (finRotate 7 0)
  set G₃ := G₂.swapColumns 1 (finRotate 7 1)
  set G₄ := G₃.swapRows 1 (finRotate 7 1)
  set G₅ := G₄.swapRows 2 (finRotate 7 2)
  set G₆ := G₅.swapColumns 2 (finRotate 7 2)
  set G₇ := G₆.swapColumns 6 (finRotate 7 6)
  set G₈ := G₇.swapRows 6 (finRotate 7 6)
  set G₉ := G₈.swapRows 0 (finRotate 7 0)
  set G₁₀ := G₉.swapColumns 0 (finRotate 7 0)
  set G₁₁ := G₁₀.swapRows 5 (finRotate 7 5)
  have h₁ : torusTwoThreeGrid.toGridLink.unknottingNumber ≤ G₁.toGridLink.unknottingNumber + 1 :=
    torusTwoThreeGrid.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 0) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₃ : G₂.toGridLink.unknottingNumber ≤ G₃.toGridLink.unknottingNumber + 1 :=
    G₂.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 1) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₇ : G₆.toGridLink.unknottingNumber ≤ G₇.toGridLink.unknottingNumber + 1 :=
    G₆.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 6) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₂ : G₁.MovesTo G₂ := G₁.movesTo_swapRows 0 (by decide) (by
    simp only [GridDiagram.RowsNoninterleaving, Grid.Noninterleaving, Grid.mem_cIoo]
    decide)
  have h₆ : G₃.MovesTo G₆ := by
    refine (G₃.movesTo_swapRows 1 (by decide) ?_).trans <|
      (G₄.movesTo_swapRows 2 (by decide) ?_).trans <| G₅.movesTo_swapColumns 2 (by decide) ?_
    all_goals
      simp only [GridDiagram.RowsNoninterleaving, GridDiagram.ColumnsNoninterleaving,
        Grid.Noninterleaving, Grid.mem_cIoo]
      decide
  have h₁₂ : G₇.MovesTo (GridDiagram.unknot 5) := by
    have h : G₁₁.swapColumns 5 (finRotate 7 5) = GridDiagram.unknot 5 := by
      rw [unknot_five_eq_unknotSevenGrid]
      ext c
      all_goals revert c; decide
    rw [← h]
    refine (G₇.movesTo_swapRows 6 (by decide) ?_).trans <|
      (G₈.movesTo_swapRows 0 (by decide) ?_).trans <|
      (G₉.movesTo_swapColumns 0 (by decide) ?_).trans <|
      (G₁₀.movesTo_swapRows 5 (by decide) ?_).trans <| G₁₁.movesTo_swapColumns 5 (by decide) ?_
    all_goals
      simp only [GridDiagram.RowsNoninterleaving, GridDiagram.ColumnsNoninterleaving,
        Grid.Noninterleaving, Grid.mem_cIoo]
      decide
  calc torusTwoThreeGrid.toGridLink.unknottingNumber
      ≤ G₁.toGridLink.unknottingNumber + 1 := h₁
    _ = G₂.toGridLink.unknottingNumber + 1 := by rw [(G₁.toGridLink_eq_iff_movesTo).mpr h₂]
    _ ≤ G₃.toGridLink.unknottingNumber + 1 + 1 := by gcongr
    _ = G₆.toGridLink.unknottingNumber + 1 + 1 := by rw [(G₃.toGridLink_eq_iff_movesTo).mpr h₆]
    _ ≤ G₇.toGridLink.unknottingNumber + 1 + 1 + 1 := by gcongr
    _ = 3 := by
      rw [(G₇.toGridLink_eq_iff_movesTo).mpr h₁₂, GridDiagram.toGridLink_unknot,
        unknottingNumber_unknot]
      norm_num

end GridLink

end TauCeti
