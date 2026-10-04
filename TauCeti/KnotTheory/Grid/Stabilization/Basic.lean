/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.KnotTheory.Grid.Diagram.Basic

import TauCeti.Data.Fin.Basic

/-!
# Elementary grid stabilization moves

A grid stabilization inserts one row and one column near a marking. In the resulting local
`2 × 2` block, the chosen marking is split across two opposite corners and one marking of the
other type occupies a third corner. Deleting the new row and column recovers the original
diagram.

This file first gives the two permutation operations underlying this construction.
`GridState.insertPoint` inserts one point at the intersection of the new row and column, while
`GridState.splitPoint` replaces a chosen old point by the other two corners of that local block.
It then constructs stabilizations that split either an `O`- or an `X`-marking.

The predicates `GridDiagram.IsOStabilization` and `GridDiagram.IsXStabilization` require the new
row and column to be cyclically adjacent to the row and column of the split marking. Allowing
either cyclic orientation in each coordinate gives the four corner types for each marking, hence
the eight standard stabilization types. `GridDiagram.IsStabilization` combines the two marking
types, and `GridDiagram.IsDestabilization` reverses the relation.

## Main definitions

* `TauCeti.GridState.insertPoint`: insert a point into a permutation graph.
* `TauCeti.GridState.splitPoint`: split one old point across the other corners of an inserted
  row and column.
* `TauCeti.GridDiagram.stabilizeO`, `TauCeti.GridDiagram.stabilizeX`: the two marking-level
  stabilization constructions.
* `TauCeti.GridDiagram.IsStabilization`, `TauCeti.GridDiagram.IsDestabilization`: elementary
  stabilization and destabilization relations.

## Main results

* `TauCeti.GridDiagram.stabilizeO_castSucc_eq_stabilizeX_succ` and
  `TauCeti.GridDiagram.stabilizeO_succ_eq_stabilizeX_castSucc`: with the new column next to the
  split column, an `O`-stabilization is the `X`-stabilization of the same column with the new
  column on the other side.
* `TauCeti.GridDiagram.stabilizeX_castSucc_swapColumns` and
  `TauCeti.GridDiagram.stabilizeX_swapRows`: swapping the new column or row of an
  `X`-stabilization with an adjacent old one moves it to the other side.
* `TauCeti.GridDiagram.stabilizeX_last_relabelRows`,
  `TauCeti.GridDiagram.stabilizeX_last_relabelColumns` and
  `TauCeti.GridDiagram.stabilizeO_last_relabelColumns`: a cyclic permutation moves a new last row
  or column to the front.

## References

This supplies the stabilization half of the standing convention in
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md` that a link is initially a grid diagram
modulo grid moves. The local three-marking construction and its eight types follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- Insert a new point `(newColumn, newRow)` into a grid state.

Every old point `(c, x c)` is sent to
`(newColumn.succAbove c, newRow.succAbove (x c))`. -/
def insertPoint (x : GridState n) (newColumn newRow : Fin (n + 1)) : GridState (n + 1) where
  toPerm :=
    (finSuccEquiv' newColumn).trans
      ((Equiv.optionCongr x.toPerm).trans (finSuccEquiv' newRow).symm)

/-- The inserted column contains the inserted row. -/
@[simp]
theorem insertPoint_apply_newColumn (x : GridState n) (newColumn newRow : Fin (n + 1)) :
    x.insertPoint newColumn newRow newColumn = newRow := by
  simp [insertPoint]

/-- An old column contains the embedded image of its old row after inserting a point. -/
@[simp]
theorem insertPoint_apply_succAbove (x : GridState n) (newColumn newRow : Fin (n + 1)) (c : Fin n) :
    x.insertPoint newColumn newRow (newColumn.succAbove c) =
      newRow.succAbove (x c) := by
  simp [insertPoint]

/-- Inserting the same point into two grid states gives equal states only if the states were
equal. -/
theorem insertPoint_injective (newColumn newRow : Fin (n + 1)) :
    Function.Injective fun x : GridState n => x.insertPoint newColumn newRow := by
  intro x y h
  refine GridState.ext fun c => newRow.succAbove_right_injective ?_
  simpa using congrArg (fun z : GridState (n + 1) => z (newColumn.succAbove c)) h

/-- Every grid state containing the point `(newColumn, newRow)` is obtained by inserting that
point into a grid state of the smaller grid. -/
theorem exists_insertPoint_eq {newColumn newRow : Fin (n + 1)} {y : GridState (n + 1)}
    (h : y newColumn = newRow) : ∃ x : GridState n, x.insertPoint newColumn newRow = y := by
  let e : Equiv.Perm (Option (Fin n)) :=
    (finSuccEquiv' newColumn).symm.trans (y.toPerm.trans (finSuccEquiv' newRow))
  have hnone : e none = none := by
    simp only [e, Equiv.trans_apply, finSuccEquiv'_symm_none, finSuccEquiv'_eq_none]
    exact h.symm
  refine ⟨⟨Equiv.removeNone e⟩, GridState.ext fun c => ?_⟩
  induction c using Fin.succAboveCases newColumn with
  | x => simp [h]
  | p c =>
    have hsome : some (Equiv.removeNone e c) = e (some c) :=
      Equiv.removeNone_some e (Option.ne_none_iff_exists'.mp fun hc =>
        Option.some_ne_none c (e.injective (hc.trans hnone.symm)))
    simpa [e] using congrArg (finSuccEquiv' newRow).symm hsome

/-- Split the point in column `splitColumn` across an inserted row and column.

The old point at `(splitColumn, x splitColumn)` is replaced by the two points
`(newColumn, newRow.succAbove (x splitColumn))` and
`(newColumn.succAbove splitColumn, newRow)`. All other old points are embedded as in
`GridState.insertPoint`. -/
def splitPoint (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n) : GridState (n + 1) :=
  (x.insertPoint newColumn newRow).swapColumns newColumn
    (newColumn.succAbove splitColumn)

/-- The new column of a split point contains the embedded old row of the split point. -/
@[simp]
theorem splitPoint_apply_newColumn (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n) :
    x.splitPoint newColumn newRow splitColumn newColumn =
      newRow.succAbove (x splitColumn) := by
  simp [splitPoint]

/-- The embedded old column of a split point contains the new row. -/
@[simp]
theorem splitPoint_apply_splitColumn (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n) :
    x.splitPoint newColumn newRow splitColumn (newColumn.succAbove splitColumn) =
      newRow := by
  simp [splitPoint]

/-- When the new column is inserted immediately before the split column, the split column moves
to its successor and contains the new row. -/
@[simp]
theorem splitPoint_castSucc_apply_succ (x : GridState n) (newRow : Fin (n + 1))
    (splitColumn : Fin n) :
    x.splitPoint splitColumn.castSucc newRow splitColumn splitColumn.succ = newRow := by
  simpa using x.splitPoint_apply_splitColumn splitColumn.castSucc newRow splitColumn

/-- Away from the split column, `splitPoint` embeds old points in the inserted grid. -/
@[simp]
theorem splitPoint_apply_succAbove (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn c : Fin n) :
    x.splitPoint newColumn newRow splitColumn (newColumn.succAbove c) =
      if c = splitColumn then newRow else newRow.succAbove (x c) := by
  by_cases h : c = splitColumn
  · subst c
    simp
  · rw [splitPoint, swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (newColumn.succAbove_ne c)
        (fun hc ↦ h (Fin.succAbove_right_injective hc))]
    simpa using h

/-- After inserting a point, the new row is occupied only in the new column. -/
@[simp]
theorem insertPoint_apply_eq_iff (x : GridState n) (newColumn newRow c : Fin (n + 1)) :
    x.insertPoint newColumn newRow c = newRow ↔ c = newColumn := by
  refine ⟨fun h ↦ (x.insertPoint newColumn newRow).toPerm.injective ?_, ?_⟩
  · exact h.trans (by simp)
  · rintro rfl
    simp

/-- After splitting a point, the new row is occupied only in the embedded split column. -/
@[simp]
theorem splitPoint_apply_eq_iff (x : GridState n) (newColumn newRow : Fin (n + 1))
    (splitColumn : Fin n) (c : Fin (n + 1)) :
    x.splitPoint newColumn newRow splitColumn c = newRow ↔ c = newColumn.succAbove splitColumn := by
  refine ⟨fun h ↦ (x.splitPoint newColumn newRow splitColumn).toPerm.injective ?_, ?_⟩
  · exact h.trans (by simp)
  · rintro rfl
    simp

/-- Splitting the point of column `s` across a column inserted just before it is inserting the
point `(s.succ, newRow)`: the old point of column `s` moves to the new column `s.castSucc`, and
every other column is embedded alike by `s.castSucc.succAbove` and `s.succ.succAbove`. -/
theorem splitPoint_castSucc_eq_insertPoint (x : GridState n) (s : Fin n)
    (newRow : Fin (n + 1)) :
    x.splitPoint s.castSucc newRow s = x.insertPoint s.succ newRow := by
  refine GridState.ext fun c => ?_
  induction c using Fin.succAboveCases s.castSucc with
  | x => rw [splitPoint_apply_newColumn, ← Fin.succAbove_succ_self, insertPoint_apply_succAbove]
  | p c =>
    rw [splitPoint_apply_succAbove]
    split_ifs with hc
    · rw [hc, Fin.succAbove_castSucc_self, insertPoint_apply_newColumn]
    · rcases lt_or_gt_of_ne hc with h | h
      · rw [Fin.succAbove_castSucc_of_lt _ _ h, ← Fin.succAbove_succ_of_le _ _ h.le,
          insertPoint_apply_succAbove]
      · rw [Fin.succAbove_castSucc_of_le _ _ h.le, ← Fin.succAbove_succ_of_lt _ _ h,
          insertPoint_apply_succAbove]

/-- Splitting the point of column `s` across a column inserted just after it is inserting the
point `(s.castSucc, newRow)`: the old point of column `s` moves to the new column `s.succ`. -/
theorem splitPoint_succ_eq_insertPoint (x : GridState n) (s : Fin n) (newRow : Fin (n + 1)) :
    x.splitPoint s.succ newRow s = x.insertPoint s.castSucc newRow := by
  rw [splitPoint, Fin.succAbove_succ_self, swapColumns_comm,
    ← x.splitPoint_castSucc_eq_insertPoint, splitPoint, Fin.succAbove_castSucc_self,
    swapColumns_swapColumns]

/-- Swapping an inserted column `s.castSucc` with the old column `s` just after it moves the
inserted column to `s.succ`. -/
theorem insertPoint_castSucc_swapColumns (x : GridState n) (s : Fin n) (newRow : Fin (n + 1)) :
    (x.insertPoint s.castSucc newRow).swapColumns s.castSucc s.succ =
      x.insertPoint s.succ newRow := by
  simpa only [splitPoint, Fin.succAbove_castSucc_self] using
    x.splitPoint_castSucc_eq_insertPoint s newRow

/-- Swapping an inserted column `s.succ` with the old column `s` just before it moves the
inserted column to `s.castSucc`. -/
theorem insertPoint_succ_swapColumns (x : GridState n) (s : Fin n) (newRow : Fin (n + 1)) :
    (x.insertPoint s.succ newRow).swapColumns s.castSucc s.succ =
      x.insertPoint s.castSucc newRow := by
  simpa only [splitPoint, Fin.succAbove_succ_self, swapColumns_comm] using
    x.splitPoint_succ_eq_insertPoint s newRow

/-- Reflecting in the diagonal exchanges the roles of the inserted row and column. -/
theorem transpose_insertPoint (x : GridState n) (newColumn newRow : Fin (n + 1)) :
    (x.insertPoint newColumn newRow).transpose = x.transpose.insertPoint newRow newColumn :=
  GridState.ext fun r ↦ by simp [insertPoint, transpose, Equiv.optionCongr_symm]

/-- Swapping an inserted row `k.castSucc` with the old row `k` just above it moves the inserted
row to `k.succ`. -/
theorem insertPoint_swapRows (x : GridState n) (newColumn : Fin (n + 1)) (k : Fin n) :
    (x.insertPoint newColumn k.castSucc).swapRows k.castSucc k.succ =
      x.insertPoint newColumn k.succ := by
  refine GridState.ext fun c ↦ ?_
  induction c using Fin.succAboveCases newColumn with
  | x => simp
  | p c => simp [Fin.swap_castSucc_succ_succAbove]

/-- Swapping an inserted row `k.castSucc` with the old row `k` just above it moves the inserted
row of a split point to `k.succ`. -/
theorem splitPoint_swapRows (x : GridState n) (newColumn : Fin (n + 1)) (k s : Fin n) :
    (x.splitPoint newColumn k.castSucc s).swapRows k.castSucc k.succ =
      x.splitPoint newColumn k.succ s := by
  refine GridState.ext fun c ↦ ?_
  induction c using Fin.succAboveCases newColumn with
  | x => simp [Fin.swap_castSucc_succ_succAbove]
  | p c =>
    simp only [swapRows_apply, splitPoint_apply_succAbove]
    split_ifs <;> simp [Fin.swap_castSucc_succ_succAbove]

/-- Cyclically permuting the rows moves an inserted top row to the bottom. -/
theorem insertPoint_last_relabelRows (x : GridState n) (newColumn : Fin (n + 1)) :
    (x.insertPoint newColumn (Fin.last n)).relabelRows (finRotate (n + 1)) =
      x.insertPoint newColumn 0 := by
  refine GridState.ext fun c ↦ ?_
  induction c using Fin.succAboveCases newColumn with
  | x => simp
  | p c => simp [finRotate_apply, Fin.coeSucc_eq_succ]

/-- Cyclically permuting the rows moves the inserted top row of a split point to the bottom. -/
theorem splitPoint_last_relabelRows (x : GridState n) (newColumn : Fin (n + 1)) (s : Fin n) :
    (x.splitPoint newColumn (Fin.last n) s).relabelRows (finRotate (n + 1)) =
      x.splitPoint newColumn 0 s := by
  refine GridState.ext fun c ↦ ?_
  induction c using Fin.succAboveCases newColumn with
  | x => simp [finRotate_apply, Fin.coeSucc_eq_succ]
  | p c =>
    simp only [relabelRows_apply, splitPoint_apply_succAbove]
    split_ifs <;> simp [finRotate_apply, Fin.coeSucc_eq_succ]

/-- Cyclically permuting the columns moves an inserted last column to the front. -/
theorem insertPoint_last_relabelColumns (x : GridState n) (newRow : Fin (n + 1)) :
    (x.insertPoint (Fin.last n) newRow).relabelColumns (finRotate (n + 1)) =
      x.insertPoint 0 newRow := by
  refine GridState.ext fun c ↦ ?_
  induction c using Fin.cases with
  | zero =>
    rw [relabelColumns_apply, (Equiv.symm_apply_eq _).mpr finRotate_last.symm,
      insertPoint_apply_newColumn, insertPoint_apply_newColumn]
  | succ c =>
    rw [relabelColumns_apply,
      (Equiv.symm_apply_eq _).mpr (by rw [finRotate_apply, Fin.coeSucc_eq_succ]),
      ← Fin.succAbove_last_apply, ← Fin.succAbove_zero_apply, insertPoint_apply_succAbove,
      insertPoint_apply_succAbove]

/-- Cyclically permuting the columns moves the inserted last column of a split point to the
front. -/
theorem splitPoint_last_relabelColumns (x : GridState n) (newRow : Fin (n + 1)) (s : Fin n) :
    (x.splitPoint (Fin.last n) newRow s).relabelColumns (finRotate (n + 1)) =
      x.splitPoint 0 newRow s := by
  refine GridState.ext fun c ↦ ?_
  induction c using Fin.cases with
  | zero =>
    rw [relabelColumns_apply, (Equiv.symm_apply_eq _).mpr finRotate_last.symm,
      splitPoint_apply_newColumn, splitPoint_apply_newColumn]
  | succ c =>
    rw [relabelColumns_apply,
      (Equiv.symm_apply_eq _).mpr (by rw [finRotate_apply, Fin.coeSucc_eq_succ]),
      ← Fin.succAbove_last_apply, ← Fin.succAbove_zero_apply, splitPoint_apply_succAbove,
      splitPoint_apply_succAbove]

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- Stabilize a grid diagram by splitting the `O`-marking in `splitColumn`.

The `O` state uses the two off-diagonal corners of the inserted row and column, while the new
`X`-marking occupies their intersection. The elementary-move predicate below separately requires
the inserted row and column to be adjacent to the split marking. -/
def stabilizeO (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    GridDiagram (n + 1) where
  O := G.O.splitPoint newColumn newRow splitColumn
  X := G.X.insertPoint newColumn newRow
  disjoint := by
    intro c
    refine Fin.succAboveCases newColumn ?_ (fun i ↦ ?_) c
    · simpa only [GridState.splitPoint_apply_newColumn,
        GridState.insertPoint_apply_newColumn] using
        newRow.succAbove_ne (G.O splitColumn)
    · by_cases hi : i = splitColumn
      · subst i
        simpa only [GridState.splitPoint_apply_splitColumn,
          GridState.insertPoint_apply_succAbove] using
          (newRow.succAbove_ne (G.X splitColumn)).symm
      · simp only [GridState.splitPoint_apply_succAbove,
          GridState.insertPoint_apply_succAbove, ite_eq_right hi]
        exact fun h ↦ G.disjoint i (Fin.succAbove_right_injective h)

/-- Stabilize a grid diagram by splitting the `X`-marking in `splitColumn`.

The `X` state uses the two off-diagonal corners of the inserted row and column, while the new
`O`-marking occupies their intersection. The elementary-move predicate below separately requires
the inserted row and column to be adjacent to the split marking. -/
def stabilizeX (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    GridDiagram (n + 1) where
  O := G.O.insertPoint newColumn newRow
  X := G.X.splitPoint newColumn newRow splitColumn
  disjoint := by
    intro c
    refine Fin.succAboveCases newColumn ?_ (fun i ↦ ?_) c
    · simpa only [GridState.insertPoint_apply_newColumn,
        GridState.splitPoint_apply_newColumn] using
        (newRow.succAbove_ne (G.X splitColumn)).symm
    · by_cases hi : i = splitColumn
      · subst i
        simpa only [GridState.insertPoint_apply_succAbove,
          GridState.splitPoint_apply_splitColumn] using
          newRow.succAbove_ne (G.O splitColumn)
      · simp only [GridState.insertPoint_apply_succAbove,
          GridState.splitPoint_apply_succAbove, ite_eq_right hi]
        exact fun h ↦ G.disjoint i (Fin.succAbove_right_injective h)

/-- The `O` state of an `O`-stabilization is obtained by splitting the chosen `O`-marking. -/
@[simp]
theorem stabilizeO_O (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeO newColumn newRow splitColumn).O =
      G.O.splitPoint newColumn newRow splitColumn :=
  (rfl)

/-- The `X` state of an `O`-stabilization is obtained by inserting the new `X`-marking. -/
@[simp]
theorem stabilizeO_X (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeO newColumn newRow splitColumn).X =
      G.X.insertPoint newColumn newRow :=
  (rfl)

/-- The `O` state of an `X`-stabilization is obtained by inserting the new `O`-marking. -/
@[simp]
theorem stabilizeX_O (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeX newColumn newRow splitColumn).O =
      G.O.insertPoint newColumn newRow :=
  (rfl)

/-- The `X` state of an `X`-stabilization is obtained by splitting the chosen `X`-marking. -/
@[simp]
theorem stabilizeX_X (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeX newColumn newRow splitColumn).X =
      G.X.splitPoint newColumn newRow splitColumn :=
  (rfl)

/-- In the stabilization splitting the `X`-marking of column `s`, the row `(G.X s).castSucc`
carries its `O`-marking only in the new column `s.castSucc`. -/
theorem stabilizeX_O_eq_castSucc_iff (s : Fin n) (c : Fin (n + 1)) :
    (G.O.insertPoint s.castSucc (G.X s).castSucc) c = (G.X s).castSucc ↔
      c = s.castSucc := by
  simp

/-- In the stabilization splitting the `X`-marking of column `s`, the row `(G.X s).castSucc`
carries its `X`-marking only in the column `s.succ`. -/
theorem stabilizeX_X_eq_castSucc_iff (s : Fin n) (c : Fin (n + 1)) :
    (G.X.splitPoint s.castSucc (G.X s).castSucc s) c = (G.X s).castSucc ↔
      c = s.succ := by
  simp

/-- In the stabilization splitting the `X`-marking of column `s`, the `X`-marking of each column
collapses under `Fin.predAbove` onto the `X`-marking of `G` in the collapsed column: both
`X`-markings of the new block collapse onto the split marking. -/
theorem predAbove_X_stabilizeX (s : Fin n) (c : Fin (n + 1)) :
    (G.X s).predAbove ((G.stabilizeX s.castSucc (G.X s).castSucc s).X c) =
      G.X (s.predAbove c) := by
  induction c using Fin.succAboveCases s.castSucc with
  | x => simp
  | p i =>
    rw [stabilizeX_X, GridState.splitPoint_apply_succAbove, Fin.predAbove_succAbove]
    split_ifs with h
    · simp [h]
    · exact Fin.predAbove_succAbove _ _

/-- Exchanging the marking types turns an `O`-stabilization into an `X`-stabilization. -/
@[simp]
theorem stabilizeO_swapMarkings (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeO newColumn newRow splitColumn).swapMarkings =
      G.swapMarkings.stabilizeX newColumn newRow splitColumn := by
  ext c <;> simp

/-- Exchanging the marking types turns an `X`-stabilization into an `O`-stabilization. -/
@[simp]
theorem stabilizeX_swapMarkings (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n) :
    (G.stabilizeX newColumn newRow splitColumn).swapMarkings =
      G.swapMarkings.stabilizeO newColumn newRow splitColumn := by
  ext c <;> simp

/-- With the new column inserted just before the split column, the `X` state of an
`X`-stabilization inserts its point in the column `s.succ` of the split marking. -/
theorem stabilizeX_castSucc_X (s : Fin n) (newRow : Fin (n + 1)) :
    (G.stabilizeX s.castSucc newRow s).X = G.X.insertPoint s.succ newRow := by
  rw [stabilizeX_X, GridState.splitPoint_castSucc_eq_insertPoint]

/-- With the new column inserted just after the split column, the `X` state of an
`X`-stabilization inserts its point in the column `s.castSucc` of the split marking. -/
theorem stabilizeX_succ_X (s : Fin n) (newRow : Fin (n + 1)) :
    (G.stabilizeX s.succ newRow s).X = G.X.insertPoint s.castSucc newRow := by
  rw [stabilizeX_X, GridState.splitPoint_succ_eq_insertPoint]

/-- Splitting the `O`-marking of column `s` with a new column just before it gives the same
diagram as splitting its `X`-marking with a new column just after it: both put an `O` at
`(s.succ, newRow)` and an `X` at `(s.castSucc, newRow)`. -/
theorem stabilizeO_castSucc_eq_stabilizeX_succ (s : Fin n) (newRow : Fin (n + 1)) :
    G.stabilizeO s.castSucc newRow s = G.stabilizeX s.succ newRow s := by
  ext1
  · rw [stabilizeO_O, stabilizeX_O, GridState.splitPoint_castSucc_eq_insertPoint]
  · rw [stabilizeO_X, stabilizeX_succ_X]

/-- Splitting the `O`-marking of column `s` with a new column just after it gives the same
diagram as splitting its `X`-marking with a new column just before it. -/
theorem stabilizeO_succ_eq_stabilizeX_castSucc (s : Fin n) (newRow : Fin (n + 1)) :
    G.stabilizeO s.succ newRow s = G.stabilizeX s.castSucc newRow s := by
  ext1
  · rw [stabilizeO_O, stabilizeX_O, GridState.splitPoint_succ_eq_insertPoint]
  · rw [stabilizeO_X, stabilizeX_castSucc_X]

/-- Swapping the two columns of the new block exchanges the `X`-stabilizations with the new
column on either side of the split column. -/
theorem stabilizeX_castSucc_swapColumns (s : Fin n) (newRow : Fin (n + 1)) :
    (G.stabilizeX s.castSucc newRow s).swapColumns s.castSucc s.succ =
      G.stabilizeX s.succ newRow s := by
  ext1
  · rw [swapColumns_O, stabilizeX_O, stabilizeX_O,
      GridState.insertPoint_castSucc_swapColumns]
  · rw [swapColumns_X, stabilizeX_castSucc_X, stabilizeX_succ_X,
      GridState.insertPoint_succ_swapColumns]

/-- Swapping the new row `k.castSucc` of an `X`-stabilization with the old row `k` just above it
moves the new row to `k.succ`. -/
theorem stabilizeX_swapRows (newColumn : Fin (n + 1)) (k s : Fin n) :
    (G.stabilizeX newColumn k.castSucc s).swapRows k.castSucc k.succ =
      G.stabilizeX newColumn k.succ s := by
  ext1
  · rw [swapRows_O, stabilizeX_O, stabilizeX_O, GridState.insertPoint_swapRows]
  · rw [swapRows_X, stabilizeX_X, stabilizeX_X, GridState.splitPoint_swapRows]

/-- Cyclically permuting the rows moves the new top row of an `X`-stabilization to the
bottom. -/
theorem stabilizeX_last_relabelRows (newColumn : Fin (n + 1)) (s : Fin n) :
    (G.stabilizeX newColumn (Fin.last n) s).relabelRows (finRotate (n + 1)) =
      G.stabilizeX newColumn 0 s := by
  ext1
  · rw [relabelRows_O, stabilizeX_O, stabilizeX_O, GridState.insertPoint_last_relabelRows]
  · rw [relabelRows_X, stabilizeX_X, stabilizeX_X, GridState.splitPoint_last_relabelRows]

/-- Cyclically permuting the columns moves the new last column of an `X`-stabilization to the
front. -/
theorem stabilizeX_last_relabelColumns (newRow : Fin (n + 1)) (s : Fin n) :
    (G.stabilizeX (Fin.last n) newRow s).relabelColumns (finRotate (n + 1)) =
      G.stabilizeX 0 newRow s := by
  ext1
  · rw [relabelColumns_O, stabilizeX_O, stabilizeX_O,
      GridState.insertPoint_last_relabelColumns]
  · rw [relabelColumns_X, stabilizeX_X, stabilizeX_X,
      GridState.splitPoint_last_relabelColumns]

/-- Cyclically permuting the columns moves the new last column of an `O`-stabilization to the
front. -/
theorem stabilizeO_last_relabelColumns (newRow : Fin (n + 1)) (s : Fin n) :
    (G.stabilizeO (Fin.last n) newRow s).relabelColumns (finRotate (n + 1)) =
      G.stabilizeO 0 newRow s := by
  ext1
  · rw [relabelColumns_O, stabilizeO_O, stabilizeO_O,
      GridState.splitPoint_last_relabelColumns]
  · rw [relabelColumns_X, stabilizeO_X, stabilizeO_X,
      GridState.insertPoint_last_relabelColumns]

/-- Two grid diagrams differ by an elementary stabilization that splits an `O`-marking.

The new column is cyclically adjacent to the embedded split column, and the new row is cyclically
adjacent to the embedded row of its `O`-marking. The two disjunctions independently choose the
cyclic orientation, giving the four `O`-stabilization corner types. -/
def IsOStabilization (G : GridDiagram n) (G' : GridDiagram (n + 1)) : Prop :=
  ∃ newColumn newRow splitColumn,
    (finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
      finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn) ∧
    (finRotate (n + 1) newRow = newRow.succAbove (G.O splitColumn) ∨
      finRotate (n + 1) (newRow.succAbove (G.O splitColumn)) = newRow) ∧
    G' = G.stabilizeO newColumn newRow splitColumn

/-- An elementary `O`-stabilization is the `O`-stabilization construction at a new row and column
cyclically adjacent to the split marking. -/
theorem isOStabilization_iff (G : GridDiagram n) (G' : GridDiagram (n + 1)) :
    IsOStabilization G G' ↔ ∃ newColumn newRow splitColumn,
      (finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
        finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn) ∧
      (finRotate (n + 1) newRow = newRow.succAbove (G.O splitColumn) ∨
        finRotate (n + 1) (newRow.succAbove (G.O splitColumn)) = newRow) ∧
      G' = G.stabilizeO newColumn newRow splitColumn :=
  Iff.rfl

/-- A local `O`-stabilization construction is an elementary `O`-stabilization. -/
theorem isOStabilization_stabilizeO (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n)
    (hColumn : finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
      finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn)
    (hRow : finRotate (n + 1) newRow = newRow.succAbove (G.O splitColumn) ∨
      finRotate (n + 1) (newRow.succAbove (G.O splitColumn)) = newRow) :
    IsOStabilization G (G.stabilizeO newColumn newRow splitColumn) :=
  ⟨newColumn, newRow, splitColumn, hColumn, hRow, rfl⟩

/-- Inserting a column immediately before `splitColumn` and a row immediately before its
`O`-marking gives an elementary `O`-stabilization. -/
theorem isOStabilization_stabilizeO_castSucc (splitColumn : Fin n) :
    IsOStabilization G
      (G.stabilizeO splitColumn.castSucc (G.O splitColumn).castSucc splitColumn) := by
  apply G.isOStabilization_stabilizeO
  · left
    simp
  · left
    simp

/-- Two grid diagrams differ by an elementary stabilization that splits an `X`-marking.

The new column is cyclically adjacent to the embedded split column, and the new row is cyclically
adjacent to the embedded row of its `X`-marking. The two disjunctions independently choose the
cyclic orientation, giving the four `X`-stabilization corner types. -/
def IsXStabilization (G : GridDiagram n) (G' : GridDiagram (n + 1)) : Prop :=
  ∃ newColumn newRow splitColumn,
    (finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
      finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn) ∧
    (finRotate (n + 1) newRow = newRow.succAbove (G.X splitColumn) ∨
      finRotate (n + 1) (newRow.succAbove (G.X splitColumn)) = newRow) ∧
    G' = G.stabilizeX newColumn newRow splitColumn

/-- An elementary `X`-stabilization is the `X`-stabilization construction at a new row and column
cyclically adjacent to the split marking. -/
theorem isXStabilization_iff (G : GridDiagram n) (G' : GridDiagram (n + 1)) :
    IsXStabilization G G' ↔ ∃ newColumn newRow splitColumn,
      (finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
        finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn) ∧
      (finRotate (n + 1) newRow = newRow.succAbove (G.X splitColumn) ∨
        finRotate (n + 1) (newRow.succAbove (G.X splitColumn)) = newRow) ∧
      G' = G.stabilizeX newColumn newRow splitColumn :=
  Iff.rfl

/-- A local `X`-stabilization construction is an elementary `X`-stabilization. -/
theorem isXStabilization_stabilizeX (newColumn newRow : Fin (n + 1)) (splitColumn : Fin n)
    (hColumn : finRotate (n + 1) newColumn = newColumn.succAbove splitColumn ∨
      finRotate (n + 1) (newColumn.succAbove splitColumn) = newColumn)
    (hRow : finRotate (n + 1) newRow = newRow.succAbove (G.X splitColumn) ∨
      finRotate (n + 1) (newRow.succAbove (G.X splitColumn)) = newRow) :
    IsXStabilization G (G.stabilizeX newColumn newRow splitColumn) :=
  ⟨newColumn, newRow, splitColumn, hColumn, hRow, rfl⟩

/-- Inserting a column immediately before `splitColumn` and a row immediately before its
`X`-marking gives an elementary `X`-stabilization. -/
theorem isXStabilization_stabilizeX_castSucc (splitColumn : Fin n) :
    IsXStabilization G
      (G.stabilizeX splitColumn.castSucc (G.X splitColumn).castSucc splitColumn) := by
  apply G.isXStabilization_stabilizeX
  · left
    simp
  · left
    simp

/-- Exchanging the marking types turns an `O`-stabilization relation into an
`X`-stabilization relation. -/
@[simp]
theorem isOStabilization_swapMarkings (G : GridDiagram n) (G' : GridDiagram (n + 1)) :
    IsOStabilization G.swapMarkings G'.swapMarkings ↔ IsXStabilization G G' := by
  constructor
  · rintro ⟨newColumn, newRow, splitColumn, hColumn, hRow, hG'⟩
    refine ⟨newColumn, newRow, splitColumn, hColumn, ?_, ?_⟩
    · simpa using hRow
    · simpa using congrArg GridDiagram.swapMarkings hG'
  · rintro ⟨newColumn, newRow, splitColumn, hColumn, hRow, hG'⟩
    refine ⟨newColumn, newRow, splitColumn, hColumn, ?_, ?_⟩
    · simpa using hRow
    · simpa using congrArg GridDiagram.swapMarkings hG'

/-- Exchanging the marking types turns an `X`-stabilization relation into an
`O`-stabilization relation. -/
@[simp]
theorem isXStabilization_swapMarkings (G : GridDiagram n) (G' : GridDiagram (n + 1)) :
    IsXStabilization G.swapMarkings G'.swapMarkings ↔ IsOStabilization G G' := by
  simpa only [swapMarkings_swapMarkings] using
    (isOStabilization_swapMarkings G.swapMarkings G'.swapMarkings).symm

/-- One elementary grid stabilization, splitting either an `O`- or an `X`-marking. -/
def IsStabilization (G : GridDiagram n) (G' : GridDiagram (n + 1)) : Prop :=
  IsOStabilization G G' ∨ IsXStabilization G G'

/-- An elementary stabilization splits either an `O`-marking or an `X`-marking. -/
theorem isStabilization_iff (G : GridDiagram n) (G' : GridDiagram (n + 1)) :
    IsStabilization G G' ↔ IsOStabilization G G' ∨ IsXStabilization G G' :=
  Iff.rfl

/-- Exchanging the marking types preserves the elementary stabilization relation. -/
@[simp]
theorem isStabilization_swapMarkings (G : GridDiagram n) (G' : GridDiagram (n + 1)) :
    IsStabilization G.swapMarkings G'.swapMarkings ↔ IsStabilization G G' := by
  simp only [IsStabilization, isOStabilization_swapMarkings,
    isXStabilization_swapMarkings, or_comm]

/-- One elementary grid destabilization, oriented from the larger diagram to the smaller one. -/
def IsDestabilization (G' : GridDiagram (n + 1)) (G : GridDiagram n) : Prop :=
  IsStabilization G G'

/-- A destabilization from the larger diagram to the smaller one is the reverse orientation of
the corresponding stabilization. -/
theorem isDestabilization_iff_isStabilization (G' : GridDiagram (n + 1)) (G : GridDiagram n) :
    IsDestabilization G' G ↔ IsStabilization G G' :=
  Iff.rfl

/-- Exchanging the marking types preserves the elementary destabilization relation. -/
@[simp]
theorem isDestabilization_swapMarkings (G' : GridDiagram (n + 1)) (G : GridDiagram n) :
    IsDestabilization G'.swapMarkings G.swapMarkings ↔ IsDestabilization G' G := by
  simpa only [IsDestabilization] using isStabilization_swapMarkings G G'

end GridDiagram

end TauCeti
