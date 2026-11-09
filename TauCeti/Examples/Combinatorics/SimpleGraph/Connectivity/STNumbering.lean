/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.STNumbering
import Mathlib.Tactic.FinCases

/-!
# `st`-numberings and bipolar orientations on the diamond graph

The diamond graph on `Fin 4` is the four-cycle `0 — 1 — 2 — 3 — 0` together with the diagonal
`0 — 2`, obtained from `⊤` by deleting the single edge `s(1, 3)`. These examples exercise the
public API of `SimpleGraph.STNumbering` and its induced `TauCeti.DoubledQuiver.Orientation` on:

* a cycle edge (`s = 0`, `t = 3`), ordered `[0, 1, 2, 3]` along the four-cycle arc `0 — 1 — 2 — 3`
  with the chord `0 — 2` oriented forward;
* the diagonal edge (`s = 0`, `t = 2`), ordered `[0, 1, 3, 2]` by starting at the triangle
  `0 — 1 — 2 — 0` and inserting the open ear `0 — 3 — 2` before `2`;
* the nonadjacent pair (`s = 1`, `t = 3`), ordered `[1, 0, 2, 3]`, certifying
  `2`-vertex-connectivity of `diamond ⊔ SimpleGraph.edge 1 3` and illustrating the
  Lempel–Even–Cederbaum equivalence
  `SimpleGraph.nonempty_stNumbering_iff_isVertexConnected_two_sup_edge` when `s` and `t` are not
  adjacent.
-/

public section

namespace TauCeti.STNumberingExample

open SimpleGraph TauCeti.DoubledQuiver

/-- The diamond graph on `Fin 4`: four-cycle `0 — 1 — 2 — 3 — 0` with diagonal `0 — 2`. -/
abbrev diamond : SimpleGraph (Fin 4) :=
  (⊤ : SimpleGraph (Fin 4)).deleteEdges {s(1, 3)}

private theorem diamond_adj {u v : Fin 4} :
    diamond.Adj u v ↔ u ≠ v ∧ ¬(u = 1 ∧ v = 3) ∧ ¬(u = 3 ∧ v = 1) := by
  simp [diamond, deleteEdges_adj]

/-- Explicit `st`-numbering `[0, 1, 2, 3]` across the cycle edge `0 — 3`. -/
def diamondCycleST : diamond.STNumbering 0 3 where
  numbering := Equiv.refl (Fin 4)
  source_first := rfl
  sink_last := rfl
  lower_neighbor v hv0 hv3 := by
    fin_cases v
    · exact (hv0 rfl).elim
    · exact ⟨0, by rw [diamond_adj]; decide, by decide⟩
    · exact ⟨1, by rw [diamond_adj]; decide, by decide⟩
    · exact (hv3 rfl).elim
  higher_neighbor v hv0 hv3 := by
    fin_cases v
    · exact (hv0 rfl).elim
    · exact ⟨2, by rw [diamond_adj]; decide, by decide⟩
    · exact ⟨3, by rw [diamond_adj]; decide, by decide⟩
    · exact (hv3 rfl).elim

@[simp]
private theorem val_diamondCycleST_numbering (v : Fin 4) :
    (diamondCycleST.numbering v).val = v.val :=
  (rfl)

/-- Explicit `st`-numbering `[0, 1, 3, 2]` (values `0 ↦ 0, 1 ↦ 1, 2 ↦ 3, 3 ↦ 2`) across the
diagonal edge `0 — 2`. -/
def diamondDiagST : diamond.STNumbering 0 2 where
  numbering := Equiv.swap (2 : Fin 4) 3
  source_first := by decide
  sink_last := by decide
  lower_neighbor v hv0 hv2 := by
    fin_cases v
    · exact (hv0 rfl).elim
    · exact ⟨0, by rw [diamond_adj]; decide, by decide⟩
    · exact (hv2 rfl).elim
    · exact ⟨0, by rw [diamond_adj]; decide, by decide⟩
  higher_neighbor v hv0 hv2 := by
    fin_cases v
    · exact (hv0 rfl).elim
    · exact ⟨2, by rw [diamond_adj]; decide, by decide⟩
    · exact (hv2 rfl).elim
    · exact ⟨2, by rw [diamond_adj]; decide, by decide⟩

/-- Explicit `st`-numbering across the nonadjacent pair `(1, 3)` (`1 ↦ 0, 0 ↦ 1, 2 ↦ 2, 3 ↦ 3`). -/
def diamondNonEdgeST : diamond.STNumbering 1 3 where
  numbering := Equiv.swap (0 : Fin 4) 1
  source_first := by decide
  sink_last := by decide
  lower_neighbor v hv1 hv3 := by
    fin_cases v
    · exact ⟨1, by rw [diamond_adj]; decide, by decide⟩
    · exact (hv1 rfl).elim
    · exact ⟨1, by rw [diamond_adj]; decide, by decide⟩
    · exact (hv3 rfl).elim
  higher_neighbor v hv1 hv3 := by
    fin_cases v
    · exact ⟨2, by rw [diamond_adj]; decide, by decide⟩
    · exact (hv1 rfl).elim
    · exact ⟨3, by rw [diamond_adj]; decide, by decide⟩
    · exact (hv3 rfl).elim

-- Every dart in the `(0, 3)` orientation points from smaller index to larger index, and reversing
-- the numbering flips every dart.
example (d : diamond.Dart) :
    (d ∈ diamondCycleST.toOrientation ↔ d.fst < d.snd) ∧
      (d ∈ diamondCycleST.symm.toOrientation ↔ d.snd < d.fst) := by
  rw [STNumbering.mem_symm_toOrientation]
  simp [← Fin.val_fin_lt]

-- The `(0, 3)` cycle-edge orientation is acyclic, routes every vertex from `0` to `3`, and has `0`
-- as its unique source and `3` as its unique sink.
example :
    TauCeti.Quiver.IsAcyclic (OrientedQuiver diamond diamondCycleST.toOrientation) ∧
      (∀ x : OrientedQuiver diamond diamondCycleST.toOrientation,
        Nonempty (Quiver.Path (OrientedQuiver.vertex diamond diamondCycleST.toOrientation 0) x) ∧
        Nonempty (Quiver.Path x (OrientedQuiver.vertex diamond diamondCycleST.toOrientation 3))) ∧
      ((∀ x : OrientedQuiver diamond diamondCycleST.toOrientation,
          TauCeti.Quiver.IsSource x ↔
            x = OrientedQuiver.vertex diamond diamondCycleST.toOrientation 0) ∧
        (∀ x : OrientedQuiver diamond diamondCycleST.toOrientation,
          TauCeti.Quiver.IsSink x ↔
            x = OrientedQuiver.vertex diamond diamondCycleST.toOrientation 3)) := by
  have hconn : diamond.Preconnected :=
    diamondCycleST.preconnected_of_adj (by rw [diamond_adj]; decide)
  exact ⟨diamondCycleST.isAcyclic_toOrientation,
    fun x ↦ ⟨diamondCycleST.nonempty_path_from_source hconn x,
      diamondCycleST.nonempty_path_to_sink hconn x⟩,
    ⟨fun _ ↦ diamondCycleST.isSource_iff hconn,
      fun _ ↦ diamondCycleST.isSink_iff hconn⟩⟩

-- Across the diagonal edge `0 — 2`, the induced orientation is acyclic, routes every vertex from
-- `0` to `2`, and has `0` and `2` as the unique vertices with no lower-numbered (respectively
-- higher-numbered) neighbour.
example :
    TauCeti.Quiver.IsAcyclic (OrientedQuiver diamond diamondDiagST.toOrientation) ∧
      (∀ x : OrientedQuiver diamond diamondDiagST.toOrientation,
        Nonempty (Quiver.Path (OrientedQuiver.vertex diamond diamondDiagST.toOrientation 0) x) ∧
        Nonempty (Quiver.Path x (OrientedQuiver.vertex diamond diamondDiagST.toOrientation 2))) ∧
      (∀ v, (∀ u, ¬(diamond.Adj u v ∧ diamondDiagST.numbering u < diamondDiagST.numbering v)) ↔
        v = 0) ∧
      (∀ v, (∀ w, ¬(diamond.Adj v w ∧ diamondDiagST.numbering v < diamondDiagST.numbering w)) ↔
        v = 2) := by
  have hconn : diamond.Preconnected :=
    diamondDiagST.preconnected_of_adj (by rw [diamond_adj]; decide)
  exact ⟨diamondDiagST.isAcyclic_toOrientation,
    fun x ↦ ⟨diamondDiagST.nonempty_path_from_source hconn x,
      diamondDiagST.nonempty_path_to_sink hconn x⟩,
    fun _ ↦ diamondDiagST.forall_not_adj_and_numbering_lt_iff hconn,
    fun _ ↦ diamondDiagST.forall_not_adj_and_lt_numbering_iff hconn⟩

-- Even across the non-edge `(1, 3)`, `Fintype.card (Fin 4) ≥ 3` guarantees preconnectedness and
-- directed paths from `1` to `v` and from `v` to `3` for every `v`, and certifies
-- `2`-vertex-connectivity of `diamond ⊔ edge 1 3`.
example (v : Fin 4) :
    ¬diamond.Adj 1 3 ∧
      (diamond ⊔ SimpleGraph.edge 1 3).IsVertexConnected 2 ∧
      Nonempty (Quiver.Path
        (OrientedQuiver.vertex diamond diamondNonEdgeST.toOrientation 1)
        (OrientedQuiver.vertex diamond diamondNonEdgeST.toOrientation v)) ∧
      Nonempty (Quiver.Path
        (OrientedQuiver.vertex diamond diamondNonEdgeST.toOrientation v)
        (OrientedQuiver.vertex diamond diamondNonEdgeST.toOrientation 3)) := by
  have hconn : diamond.Preconnected := diamondNonEdgeST.preconnected_of_three_le_card (by decide)
  exact ⟨by rw [diamond_adj]; decide,
    diamondNonEdgeST.isVertexConnected_two_sup_edge (by decide),
    diamondNonEdgeST.nonempty_path_from_source hconn _,
    diamondNonEdgeST.nonempty_path_to_sink hconn _⟩

-- The explicit `st`-numbering across `0 — 3` certifies `2`-vertex-connectivity of the diamond
-- graph, matching the Lempel–Even–Cederbaum equivalences for both edges and non-edges.
example :
    diamond.IsVertexConnected 2 ∧
      (Nonempty (diamond.STNumbering 0 3) ↔ diamond.IsVertexConnected 2) ∧
      (Nonempty (diamond.STNumbering 1 3) ↔
        (diamond ⊔ SimpleGraph.edge 1 3).IsVertexConnected 2) :=
  ⟨diamondCycleST.isVertexConnected_two (by decide) (by rw [diamond_adj]; decide),
    nonempty_stNumbering_iff_isVertexConnected_two (by decide) (by rw [diamond_adj]; decide),
    nonempty_stNumbering_iff_isVertexConnected_two_sup_edge (by decide) (by decide)⟩

end TauCeti.STNumberingExample
