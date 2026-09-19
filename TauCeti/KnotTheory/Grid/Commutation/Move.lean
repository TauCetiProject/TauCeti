/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import TauCeti.KnotTheory.Grid.Commutation.Relabeling

/-!
# Elementary grid commutation moves

This file packages row and column commutations as relations between grid diagrams. Two columns
are eligible for an elementary commutation when they are cyclically adjacent, their marking
segments are non-interleaving, and the target diagram is obtained by swapping them. Row
commutations are defined dually.

Cyclic adjacency is represented without an extra predicate: an edge of the cyclically ordered
set `Fin n` is the pair `a`, `finRotate n a`. Requiring these endpoints to be distinct excludes
the degenerate one-column identity swap. The resulting relations are symmetric because a swap
is an involution and preserves non-interleaving of the swapped pair.

## Main definitions

* `TauCeti.GridDiagram.IsColumnCommutation`: one elementary column commutation.
* `TauCeti.GridDiagram.ColumnCommutationData`: a column commutation together with the two turn
  rows and the placement of the adjacent-column markings in the resulting bigons.
* `TauCeti.GridDiagram.IsRowCommutation`: one elementary row commutation.
* `TauCeti.GridDiagram.IsCommutation`: one elementary commutation of either kind.

## Main results

* `TauCeti.GridDiagram.isColumnCommutation_comm` and
  `TauCeti.GridDiagram.isRowCommutation_comm`: elementary moves are reversible.
* `TauCeti.GridDiagram.ColumnCommutationData.reverse`: the validated data for the reverse
  column commutation.
* `TauCeti.GridDiagram.ColumnCommutationData.ofNoninterleaving`,
  `TauCeti.GridDiagram.isColumnCommutation_iff_exists_columnCommutationData`: every elementary
  column commutation admits validated commutation data.
* `TauCeti.GridDiagram.isRowCommutation_transpose` and
  `TauCeti.GridDiagram.isColumnCommutation_transpose`: diagonal reflection exchanges the two
  kinds of commutation.
* `TauCeti.GridDiagram.isCommutation_comm`: the combined commutation relation is symmetric.

## References

This is a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.5,
"Invariance over 𝔽₂. Grid moves = commutation + (de)stabilization": the later pentagon-counting
chain maps are attached to the elementary moves defined here. The definition follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ}

/-- Two grid diagrams differ by one elementary column commutation.

The columns are consecutive in the cyclic order on `Fin n`, have non-interleaving marking
segments in the source diagram, and are swapped to obtain the target diagram. -/
def IsColumnCommutation (G G' : GridDiagram n) : Prop :=
  ∃ a : Fin n, a ≠ finRotate n a ∧
    ColumnsNoninterleaving G a (finRotate n a) ∧
      G' = G.swapColumns a (finRotate n a)

/-- Characterization of an elementary column commutation by its exchanged columns. -/
theorem isColumnCommutation_iff (G G' : GridDiagram n) :
    IsColumnCommutation G G' ↔
      ∃ a : Fin n, a ≠ finRotate n a ∧
        ColumnsNoninterleaving G a (finRotate n a) ∧
          G' = G.swapColumns a (finRotate n a) :=
  Iff.rfl

/-- Swapping a cyclically adjacent non-interleaving pair of columns is a column commutation. -/
theorem isColumnCommutation_swapColumns (G : GridDiagram n) (a : Fin n)
    (ha : a ≠ finRotate n a) (hG : ColumnsNoninterleaving G a (finRotate n a)) :
    IsColumnCommutation G (G.swapColumns a (finRotate n a)) :=
  ⟨a, ha, hG, rfl⟩

/-- Validated geometric data for a column commutation.

The column `column` and its cyclic successor are distinct and non-interleaving. The curves in the
combined diagram meet in the square rows `turnRow` and `oppositeTurnRow`. Going upwards from the
opposite turn to `turnRow` gives the bigon containing both markings of `column`; going upwards
from `turnRow` to the opposite turn gives the bigon containing both markings of the successor.
At an intersection row, which side of the intersection contains a marking is determined by its
column, so the terminal row of either discrete interval is admitted. -/
structure ColumnCommutationData (G : GridDiagram n) where
  /-- The first of the two adjacent columns being commuted. -/
  column : Fin n
  /-- The square row containing the distinguished intersection used by the forward pentagon map. -/
  turnRow : Fin n
  /-- The square row containing the other intersection of the two vertical curves. -/
  oppositeTurnRow : Fin n
  /-- The adjacent columns are distinct. -/
  column_ne_next : column ≠ finRotate n column
  /-- The two marking segments satisfy the hypothesis for a column commutation. -/
  noninterleaving : ColumnsNoninterleaving G column (finRotate n column)
  /-- The `O`-marking of the first column lies in the bigon below the distinguished turn. -/
  O_column_below : G.O column ∈ insert turnRow (Grid.cIco oppositeTurnRow turnRow)
  /-- The `X`-marking of the first column lies in the bigon below the distinguished turn. -/
  X_column_below : G.X column ∈ insert turnRow (Grid.cIco oppositeTurnRow turnRow)
  /-- The `O`-marking of the successor column lies in the bigon above the distinguished turn. -/
  O_next_above :
    G.O (finRotate n column) ∈ insert oppositeTurnRow (Grid.cIco turnRow oppositeTurnRow)
  /-- The `X`-marking of the successor column lies in the bigon above the distinguished turn. -/
  X_next_above :
    G.X (finRotate n column) ∈ insert oppositeTurnRow (Grid.cIco turnRow oppositeTurnRow)

namespace ColumnCommutationData

variable {G : GridDiagram n}

/-- Validated column-commutation data determines an elementary column commutation. -/
theorem isColumnCommutation (C : ColumnCommutationData G) :
    IsColumnCommutation G (G.swapColumns C.column (finRotate n C.column)) :=
  G.isColumnCommutation_swapColumns C.column C.column_ne_next C.noninterleaving

/-- The validated data for the reverse column commutation, using the other intersection as its
distinguished turn. -/
def reverse (C : ColumnCommutationData G) :
    ColumnCommutationData (G.swapColumns C.column (finRotate n C.column)) where
  column := C.column
  turnRow := C.oppositeTurnRow
  oppositeTurnRow := C.turnRow
  column_ne_next := C.column_ne_next
  noninterleaving := by
    simpa [columnsNoninterleaving_comm] using C.noninterleaving
  O_column_below := by
    simpa using C.O_next_above
  X_column_below := by
    simpa using C.X_next_above
  O_next_above := by
    simpa using C.O_column_below
  X_next_above := by
    simpa using C.X_column_below

/-- Reversing commutation data preserves the first column. -/
@[simp]
theorem reverse_column (C : ColumnCommutationData G) : C.reverse.column = C.column :=
  (rfl)

/-- Reversing commutation data uses the other intersection as its distinguished turn. -/
@[simp]
theorem reverse_turnRow (C : ColumnCommutationData G) : C.reverse.turnRow = C.oppositeTurnRow :=
  (rfl)

/-- Reversing commutation data makes the old distinguished turn the other intersection. -/
@[simp]
theorem reverse_oppositeTurnRow (C : ColumnCommutationData G) :
    C.reverse.oppositeTurnRow = C.turnRow :=
  (rfl)

/-- A row off the open arc from `u` to `v` lies in the closed complementary arc from `v` to `u`. -/
private theorem mem_insert_cIco_of_notMem_cIoo {u v r : Fin n} (huv : u ≠ v)
    (hr : r ∉ Grid.cIoo u v) : r ∈ insert u (Grid.cIco v u) := by
  rcases (Grid.not_mem_cIoo_iff huv).mp hr with rfl | rfl | hr
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Grid.left_mem_cIco huv.symm)
  · exact Finset.mem_insert_of_mem (Grid.cIoo_subset_cIco _ _ hr)

/-- A row on the open arc from `u` to `v` lies in the closed arc from `u` to `v`. -/
private theorem mem_insert_cIco_of_mem_cIoo {u v r : Fin n} (hr : r ∈ Grid.cIoo u v) :
    r ∈ insert v (Grid.cIco u v) :=
  Finset.mem_insert_of_mem (Grid.cIoo_subset_cIco _ _ hr)

/-- Both endpoints of a nondegenerate arc lie in its closed version. -/
private theorem mem_insert_cIco_left {u v : Fin n} (huv : u ≠ v) :
    u ∈ insert v (Grid.cIco u v) :=
  Finset.mem_insert_of_mem (Grid.left_mem_cIco huv)

/-- Validated commutation data for every adjacent non-interleaving pair of columns.

The two rows of the markings of `a` serve as the turn rows. Non-interleaving puts both markings
of the successor column on one side of them, which fixes which of the two rows is the
distinguished turn. -/
noncomputable def ofNoninterleaving (a : Fin n) (ha : a ≠ finRotate n a)
    (hG : ColumnsNoninterleaving G a (finRotate n a)) : ColumnCommutationData G := by
  classical
  have hOX := G.disjoint a
  have hb := ((columnsNoninterleaving_iff G _ _).mp hG).2
  simp only [mem_columnArc] at hb
  exact if h : G.O (finRotate n a) ∈ Grid.cIoo (G.O a) (G.X a) then
    { column := a
      turnRow := G.O a
      oppositeTurnRow := G.X a
      column_ne_next := ha
      noninterleaving := hG
      O_column_below := Finset.mem_insert_self _ _
      X_column_below := mem_insert_cIco_left hOX.symm
      O_next_above := mem_insert_cIco_of_mem_cIoo h
      X_next_above := mem_insert_cIco_of_mem_cIoo (hb.mp h) }
  else
    { column := a
      turnRow := G.X a
      oppositeTurnRow := G.O a
      column_ne_next := ha
      noninterleaving := hG
      O_column_below := mem_insert_cIco_left hOX
      X_column_below := Finset.mem_insert_self _ _
      O_next_above := mem_insert_cIco_of_notMem_cIoo hOX h
      X_next_above := mem_insert_cIco_of_notMem_cIoo hOX (mt hb.mpr h) }

/-- The data built from a non-interleaving pair commutes the given column. -/
@[simp]
theorem ofNoninterleaving_column (a : Fin n) (ha : a ≠ finRotate n a)
    (hG : ColumnsNoninterleaving G a (finRotate n a)) :
    (ofNoninterleaving a ha hG).column = a := by
  unfold ofNoninterleaving
  split_ifs <;> rfl

end ColumnCommutationData

/-- Every elementary column commutation is realised by validated column-commutation data. -/
theorem isColumnCommutation_iff_exists_columnCommutationData {G G' : GridDiagram n} :
    IsColumnCommutation G G' ↔
      ∃ C : ColumnCommutationData G, G' = G.swapColumns C.column (finRotate n C.column) := by
  constructor
  · rintro ⟨a, ha, hG, rfl⟩
    exact ⟨.ofNoninterleaving a ha hG, by rw [ColumnCommutationData.ofNoninterleaving_column]⟩
  · rintro ⟨C, rfl⟩
    exact C.isColumnCommutation

/-- An elementary column commutation is reversible. -/
theorem isColumnCommutation_comm {G G' : GridDiagram n} :
    IsColumnCommutation G G' ↔ IsColumnCommutation G' G := by
  constructor
  · rintro ⟨a, ha, hnon, rfl⟩
    refine ⟨a, ha, ?_, by simp⟩
    simpa [columnsNoninterleaving_comm] using hnon
  · rintro ⟨a, ha, hnon, rfl⟩
    refine ⟨a, ha, ?_, by simp⟩
    simpa [columnsNoninterleaving_comm] using hnon

/-- Two grid diagrams differ by one elementary row commutation.

The rows are consecutive in the cyclic order on `Fin n`, have non-interleaving marking
segments in the source diagram, and are swapped to obtain the target diagram. -/
def IsRowCommutation (G G' : GridDiagram n) : Prop :=
  ∃ a : Fin n, a ≠ finRotate n a ∧
    RowsNoninterleaving G a (finRotate n a) ∧
      G' = G.swapRows a (finRotate n a)

/-- Characterization of an elementary row commutation by its exchanged rows. -/
theorem isRowCommutation_iff (G G' : GridDiagram n) :
    IsRowCommutation G G' ↔
      ∃ a : Fin n, a ≠ finRotate n a ∧
        RowsNoninterleaving G a (finRotate n a) ∧
          G' = G.swapRows a (finRotate n a) :=
  Iff.rfl

/-- Swapping a cyclically adjacent non-interleaving pair of rows is a row commutation. -/
theorem isRowCommutation_swapRows (G : GridDiagram n) (a : Fin n)
    (ha : a ≠ finRotate n a) (hG : RowsNoninterleaving G a (finRotate n a)) :
    IsRowCommutation G (G.swapRows a (finRotate n a)) :=
  ⟨a, ha, hG, rfl⟩

/-- An elementary row commutation is reversible. -/
theorem isRowCommutation_comm {G G' : GridDiagram n} :
    IsRowCommutation G G' ↔ IsRowCommutation G' G := by
  constructor
  · rintro ⟨a, ha, hnon, rfl⟩
    refine ⟨a, ha, ?_, by simp⟩
    simpa [rowsNoninterleaving_comm] using hnon
  · rintro ⟨a, ha, hnon, rfl⟩
    refine ⟨a, ha, ?_, by simp⟩
    simpa [rowsNoninterleaving_comm] using hnon

/-- Diagonal reflection turns a row commutation into a column commutation. -/
@[simp]
theorem isRowCommutation_transpose (G G' : GridDiagram n) :
    IsRowCommutation G.transpose G'.transpose ↔ IsColumnCommutation G G' := by
  constructor
  · rintro ⟨a, ha, hnon, hswap⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hnon
    · have := congrArg GridDiagram.transpose hswap
      simpa using this
  · rintro ⟨a, ha, hnon, hswap⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hnon
    · simpa using congrArg GridDiagram.transpose hswap

/-- Diagonal reflection turns a column commutation into a row commutation. -/
@[simp]
theorem isColumnCommutation_transpose (G G' : GridDiagram n) :
    IsColumnCommutation G.transpose G'.transpose ↔ IsRowCommutation G G' := by
  constructor
  · rintro ⟨a, ha, hnon, hswap⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hnon
    · have := congrArg GridDiagram.transpose hswap
      simpa using this
  · rintro ⟨a, ha, hnon, hswap⟩
    refine ⟨a, ha, ?_, ?_⟩
    · simpa using hnon
    · simpa using congrArg GridDiagram.transpose hswap

/-- One elementary grid commutation, either of rows or of columns. -/
def IsCommutation (G G' : GridDiagram n) : Prop :=
  IsRowCommutation G G' ∨ IsColumnCommutation G G'

/-- A commutation is either an elementary row commutation or an elementary column
commutation. -/
theorem isCommutation_iff (G G' : GridDiagram n) :
    IsCommutation G G' ↔ IsRowCommutation G G' ∨ IsColumnCommutation G G' :=
  Iff.rfl

/-- The elementary grid commutation relation is symmetric. -/
theorem isCommutation_comm {G G' : GridDiagram n} :
    IsCommutation G G' ↔ IsCommutation G' G := by
  unfold IsCommutation
  rw [isRowCommutation_comm,
    isColumnCommutation_comm]

/-- Diagonal reflection preserves the elementary commutation relation, exchanging row and
column moves. -/
@[simp]
theorem isCommutation_transpose (G G' : GridDiagram n) :
    IsCommutation G.transpose G'.transpose ↔ IsCommutation G G' := by
  unfold IsCommutation
  rw [isRowCommutation_transpose, isColumnCommutation_transpose, or_comm]

end GridDiagram

end TauCeti
