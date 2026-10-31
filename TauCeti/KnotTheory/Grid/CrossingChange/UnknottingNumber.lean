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

The unknotting numbers of specific torus links are bounded in
`TauCeti.KnotTheory.Grid.TorusLink.UnknottingNumber`.

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

end GridLink

end TauCeti
