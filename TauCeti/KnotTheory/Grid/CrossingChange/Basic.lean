/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Move
public import TauCeti.KnotTheory.Grid.Diagram.Components

/-!
# Cross-commutations of grid diagrams

A commutation exchanges two adjacent columns (or rows) whose marking segments do not interleave,
and does not change the represented link. Exchanging two adjacent columns whose segments *do*
interleave is a *cross-commutation*. Topologically, the two diagrams then present links that
differ by a single crossing change, and every crossing change between two knots arises this way
for suitable grid diagrams (Ozsváth--Stipsicz--Szabó, Chapter 6); these statements about embedded
links are not formalised here. Grid homology reaches crossing changes through this move: the
crossing change maps of Ozsváth--Stipsicz--Szabó, which bound the change of `τ`, are maps between
the grid complexes of two diagrams related by a cross-commutation.

Two columns interleave when one marking of the first lies on the open arc of the second, from its
`O`-marking up to its `X`-marking, and the other marking lies on the opposite open arc
(`GridDiagram.ColumnsInterleaving`). The four markings then lie in four distinct rows that
alternate between the two columns around the vertical circle. On a planar picture of the grid,
this says that the two vertical segments overlap but neither contains the other. This is exactly
the failure of the non-interleaving hypothesis of a commutation, except in the degenerate case in
which an `O`-marking of one column shares its row with the `X`-marking of the other
(`GridDiagram.columnsInterleaving_iff_not_columnsNoninterleaving`). Two segments sharing an
endpoint are never interleaving.

## Main definitions

* `TauCeti.GridDiagram.ColumnsInterleaving`, `TauCeti.GridDiagram.RowsInterleaving`: the marking
  segments of two columns, or of two rows, interleave.
* `TauCeti.GridDiagram.IsColumnCrossCommutation`, `TauCeti.GridDiagram.IsRowCrossCommutation`:
  two diagrams differ by exchanging two adjacent interleaving columns, or rows.
* `TauCeti.GridDiagram.IsCrossCommutation`: one cross-commutation of either kind.

## Main results

* `TauCeti.GridDiagram.columnsInterleaving_iff_not_columnsNoninterleaving`: interleaving is the
  negation of non-interleaving, for segments with four distinct endpoints.
* `TauCeti.GridDiagram.columnsInterleaving_comm`: interleaving is symmetric in the two columns.
* `TauCeti.GridDiagram.isCrossCommutation_comm`: cross-commutations are reversible.
* `TauCeti.GridDiagram.isCrossCommutation_transpose`: diagonal reflection exchanges row and column
  cross-commutations.
* `TauCeti.GridDiagram.IsCrossCommutation.componentCount_eq`,
  `TauCeti.GridDiagram.IsCrossCommutation.isKnot_iff`: a cross-commutation preserves the number of
  components, as a crossing change must.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6: crossing changes realised by cross-commutations, and the
  crossing change maps.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Definition 2.2:
  the cross-commutation move.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ}

section Interleaving

variable (G : GridDiagram n)

/-- The marking segments of columns `a` and `b` interleave: one marking of column `a` lies on the
open arc of column `b`, from its `O`-marking up to its `X`-marking, and the other lies on the
opposite open arc. The four markings then lie in four distinct rows which alternate between the
two columns around the vertical circle. -/
def ColumnsInterleaving (a b : Fin n) : Prop :=
  G.O a ∈ G.columnArc b ∧ G.X a ∈ Grid.cIoo (G.X b) (G.O b) ∨
    G.O a ∈ Grid.cIoo (G.X b) (G.O b) ∧ G.X a ∈ G.columnArc b

/-- The marking segments of rows `a` and `b` interleave: one marking of row `a` lies on the open
arc of row `b`, from the column of its `O`-marking to the column of its `X`-marking, and the
other lies on the opposite open arc. -/
def RowsInterleaving (a b : Fin n) : Prop :=
  G.O.transpose a ∈ G.rowArc b ∧
      G.X.transpose a ∈ Grid.cIoo (G.X.transpose b) (G.O.transpose b) ∨
    G.O.transpose a ∈ Grid.cIoo (G.X.transpose b) (G.O.transpose b) ∧
      G.X.transpose a ∈ G.rowArc b

/-- The defining condition for interleaving columns. -/
theorem columnsInterleaving_iff (a b : Fin n) :
    G.ColumnsInterleaving a b ↔
      G.O a ∈ G.columnArc b ∧ G.X a ∈ Grid.cIoo (G.X b) (G.O b) ∨
        G.O a ∈ Grid.cIoo (G.X b) (G.O b) ∧ G.X a ∈ G.columnArc b :=
  Iff.rfl

/-- The defining condition for interleaving rows. -/
theorem rowsInterleaving_iff (a b : Fin n) :
    G.RowsInterleaving a b ↔
      G.O.transpose a ∈ G.rowArc b ∧
          G.X.transpose a ∈ Grid.cIoo (G.X.transpose b) (G.O.transpose b) ∨
        G.O.transpose a ∈ Grid.cIoo (G.X.transpose b) (G.O.transpose b) ∧
          G.X.transpose a ∈ G.rowArc b :=
  Iff.rfl

variable {G}

/-- A column does not interleave with itself. -/
theorem ColumnsInterleaving.ne {a b : Fin n} (h : G.ColumnsInterleaving a b) : a ≠ b := by
  rintro rfl
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · exact Grid.left_notMem_cIoo _ _ h
  · exact Grid.right_notMem_cIoo _ _ h

/-- Interleaving of columns is symmetric. -/
theorem ColumnsInterleaving.symm {a b : Fin n} (h : G.ColumnsInterleaving a b) :
    G.ColumnsInterleaving b a := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inr ⟨Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap h₂ h₁,
      Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap h₁ h₂⟩
  · exact Or.inl ⟨Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap h₁ h₂,
      Grid.mem_cIoo_of_mem_cIoo_of_mem_cIoo_swap h₂ h₁⟩

variable (G)

/-- Interleaving of columns is symmetric in the two columns. -/
theorem columnsInterleaving_comm (a b : Fin n) :
    G.ColumnsInterleaving a b ↔ G.ColumnsInterleaving b a :=
  ⟨ColumnsInterleaving.symm, ColumnsInterleaving.symm⟩

/-- Two columns interleave exactly when they fail to be non-interleaving and no `O`-marking of
one shares its row with the `X`-marking of the other. -/
theorem columnsInterleaving_iff_not_columnsNoninterleaving (a b : Fin n) :
    G.ColumnsInterleaving a b ↔
      ¬G.ColumnsNoninterleaving a b ∧ G.O a ≠ G.X b ∧ G.X a ≠ G.O b := by
  have hb := G.disjoint b
  constructor
  · intro h
    refine ⟨fun hN ↦ ?_, ?_⟩
    · have hiff := ((columnsNoninterleaving_iff G a b).mp hN).1
      rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) (hiff.mp h₁) h₂
      · exact Finset.disjoint_left.mp (Grid.disjoint_cIoo_swap _ _) (hiff.mpr h₂) h₁
    · rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact ⟨Grid.ne_right_of_mem_cIoo h₁, Grid.ne_right_of_mem_cIoo h₂⟩
      · exact ⟨Grid.ne_left_of_mem_cIoo h₁, Grid.ne_left_of_mem_cIoo h₂⟩
  · rintro ⟨hN, hOX, hXO⟩
    have hab : a ≠ b := by
      rintro rfl
      exact hN (columnsNoninterleaving_self G a)
    have hOO : G.O a ≠ G.O b := fun h ↦ hab (G.O.toPerm.injective h)
    have hXX : G.X a ≠ G.X b := fun h ↦ hab (G.X.toPerm.injective h)
    -- A marking of column `a` off the arc of column `b` lies on the opposite arc.
    have opp {r : Fin n} (hrO : r ≠ G.O b) (hrX : r ≠ G.X b) (hr : r ∉ G.columnArc b) :
        r ∈ Grid.cIoo (G.X b) (G.O b) :=
      Grid.mem_cIoo_swap_of_notMem hb hrO hrX hr
    by_cases hiff : G.O a ∈ G.columnArc b ↔ G.X a ∈ G.columnArc b
    · -- Then the second half of non-interleaving fails, so `b` interleaves with `a`.
      have hiff' : ¬(G.O b ∈ G.columnArc a ↔ G.X b ∈ G.columnArc a) := fun h' ↦
        hN ((columnsNoninterleaving_iff G a b).mpr ⟨hiff, h'⟩)
      have ha := G.disjoint a
      refine ColumnsInterleaving.symm ?_
      by_cases hO : G.O b ∈ G.columnArc a
      · exact Or.inl ⟨hO, Grid.mem_cIoo_swap_of_notMem ha hOX.symm hXX.symm
          fun hX ↦ hiff' (iff_of_true hO hX)⟩
      · exact Or.inr ⟨Grid.mem_cIoo_swap_of_notMem ha hOO.symm hXO.symm hO,
          by_contra fun hX ↦ hiff' (iff_of_false hO hX)⟩
    · by_cases hO : G.O a ∈ G.columnArc b
      · exact Or.inl ⟨hO, opp hXO hXX fun hX ↦ hiff (iff_of_true hO hX)⟩
      · exact Or.inr ⟨opp hOO hOX hO, by_contra fun hX ↦ hiff (iff_of_false hO hX)⟩

/-- Interleaving columns are not non-interleaving, so they cannot be commuted. -/
theorem ColumnsInterleaving.not_columnsNoninterleaving {a b : Fin n}
    (h : G.ColumnsInterleaving a b) : ¬G.ColumnsNoninterleaving a b :=
  ((columnsInterleaving_iff_not_columnsNoninterleaving G a b).mp h).1

/-- Exchanging two columns exchanges their roles in the interleaving condition. -/
@[simp]
theorem columnsInterleaving_swapColumns (a b : Fin n) :
    (G.swapColumns a b).ColumnsInterleaving a b ↔ G.ColumnsInterleaving b a := by
  simp [ColumnsInterleaving, GridState.swapColumns_apply]

/-- Diagonal reflection turns column interleaving in the reflected diagram into row interleaving
in the original diagram. -/
@[simp]
theorem columnsInterleaving_transpose (a b : Fin n) :
    G.transpose.ColumnsInterleaving a b ↔ G.RowsInterleaving a b := by
  simp only [ColumnsInterleaving, RowsInterleaving, columnArc_transpose, transpose_O, transpose_X]

/-- Diagonal reflection turns row interleaving in the reflected diagram into column interleaving
in the original diagram. -/
@[simp]
theorem rowsInterleaving_transpose (a b : Fin n) :
    G.transpose.RowsInterleaving a b ↔ G.ColumnsInterleaving a b := by
  rw [← columnsInterleaving_transpose, transpose_transpose]

/-- Interleaving of rows is symmetric in the two rows. -/
theorem rowsInterleaving_comm (a b : Fin n) :
    G.RowsInterleaving a b ↔ G.RowsInterleaving b a := by
  rw [← columnsInterleaving_transpose, ← columnsInterleaving_transpose, columnsInterleaving_comm]

/-- Two rows interleave exactly when they fail to be non-interleaving and no `O`-marking of one
shares its column with the `X`-marking of the other. -/
theorem rowsInterleaving_iff_not_rowsNoninterleaving (a b : Fin n) :
    G.RowsInterleaving a b ↔
      ¬G.RowsNoninterleaving a b ∧ G.O.transpose a ≠ G.X.transpose b ∧
        G.X.transpose a ≠ G.O.transpose b := by
  rw [← columnsInterleaving_transpose, columnsInterleaving_iff_not_columnsNoninterleaving,
    columnsNoninterleaving_transpose, transpose_O, transpose_X]

end Interleaving

/-- Two grid diagrams differ by one column cross-commutation: two cyclically adjacent columns
with interleaving marking segments in the source diagram are exchanged. -/
def IsColumnCrossCommutation (G G' : GridDiagram n) : Prop :=
  ∃ a : Fin n, G.ColumnsInterleaving a (finRotate n a) ∧ G' = G.swapColumns a (finRotate n a)

/-- Characterization of a column cross-commutation by its exchanged columns. -/
theorem isColumnCrossCommutation_iff (G G' : GridDiagram n) :
    IsColumnCrossCommutation G G' ↔
      ∃ a : Fin n, G.ColumnsInterleaving a (finRotate n a) ∧
        G' = G.swapColumns a (finRotate n a) :=
  Iff.rfl

/-- Exchanging a cyclically adjacent interleaving pair of columns is a column
cross-commutation. -/
theorem isColumnCrossCommutation_swapColumns (G : GridDiagram n) {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) :
    IsColumnCrossCommutation G (G.swapColumns a (finRotate n a)) :=
  ⟨a, h, rfl⟩

/-- A column cross-commutation is reversible. -/
theorem isColumnCrossCommutation_comm {G G' : GridDiagram n} :
    IsColumnCrossCommutation G G' ↔ IsColumnCrossCommutation G' G := by
  suffices ∀ {G G' : GridDiagram n}, IsColumnCrossCommutation G G' →
      IsColumnCrossCommutation G' G from ⟨this, this⟩
  rintro G _ ⟨a, h, rfl⟩
  exact ⟨a, by simpa using h.symm, by simp⟩

/-- Two grid diagrams differ by one row cross-commutation: two cyclically adjacent rows with
interleaving marking segments in the source diagram are exchanged. -/
def IsRowCrossCommutation (G G' : GridDiagram n) : Prop :=
  ∃ a : Fin n, G.RowsInterleaving a (finRotate n a) ∧ G' = G.swapRows a (finRotate n a)

/-- Characterization of a row cross-commutation by its exchanged rows. -/
theorem isRowCrossCommutation_iff (G G' : GridDiagram n) :
    IsRowCrossCommutation G G' ↔
      ∃ a : Fin n, G.RowsInterleaving a (finRotate n a) ∧ G' = G.swapRows a (finRotate n a) :=
  Iff.rfl

/-- Exchanging a cyclically adjacent interleaving pair of rows is a row cross-commutation. -/
theorem isRowCrossCommutation_swapRows (G : GridDiagram n) {a : Fin n}
    (h : G.RowsInterleaving a (finRotate n a)) :
    IsRowCrossCommutation G (G.swapRows a (finRotate n a)) :=
  ⟨a, h, rfl⟩

/-- Diagonal reflection turns a column cross-commutation of the reflected diagrams into a row
cross-commutation of the original ones. -/
@[simp]
theorem isColumnCrossCommutation_transpose (G G' : GridDiagram n) :
    IsColumnCrossCommutation G.transpose G'.transpose ↔ IsRowCrossCommutation G G' := by
  constructor
  · rintro ⟨a, h, hswap⟩
    exact ⟨a, by simpa using h, by simpa using congrArg GridDiagram.transpose hswap⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨a, by simpa using h, by simp⟩

/-- Diagonal reflection turns a row cross-commutation of the reflected diagrams into a column
cross-commutation of the original ones. -/
@[simp]
theorem isRowCrossCommutation_transpose (G G' : GridDiagram n) :
    IsRowCrossCommutation G.transpose G'.transpose ↔ IsColumnCrossCommutation G G' := by
  rw [← isColumnCrossCommutation_transpose, transpose_transpose, transpose_transpose]

/-- A row cross-commutation is reversible. -/
theorem isRowCrossCommutation_comm {G G' : GridDiagram n} :
    IsRowCrossCommutation G G' ↔ IsRowCrossCommutation G' G := by
  rw [← isColumnCrossCommutation_transpose, ← isColumnCrossCommutation_transpose,
    isColumnCrossCommutation_comm]

/-- One cross-commutation, either of rows or of columns. -/
def IsCrossCommutation (G G' : GridDiagram n) : Prop :=
  IsRowCrossCommutation G G' ∨ IsColumnCrossCommutation G G'

/-- A cross-commutation is a row cross-commutation or a column cross-commutation. -/
theorem isCrossCommutation_iff (G G' : GridDiagram n) :
    IsCrossCommutation G G' ↔ IsRowCrossCommutation G G' ∨ IsColumnCrossCommutation G G' :=
  Iff.rfl

/-- The cross-commutation relation is symmetric. -/
theorem isCrossCommutation_comm {G G' : GridDiagram n} :
    IsCrossCommutation G G' ↔ IsCrossCommutation G' G := by
  rw [isCrossCommutation_iff, isCrossCommutation_iff, isRowCrossCommutation_comm,
    isColumnCrossCommutation_comm]

/-- Diagonal reflection preserves the cross-commutation relation, exchanging row and column
cross-commutations. -/
@[simp]
theorem isCrossCommutation_transpose (G G' : GridDiagram n) :
    IsCrossCommutation G.transpose G'.transpose ↔ IsCrossCommutation G G' := by
  rw [isCrossCommutation_iff, isCrossCommutation_iff, isRowCrossCommutation_transpose,
    isColumnCrossCommutation_transpose, or_comm]

/-- A cross-commutation preserves the multiset of component sizes. -/
theorem IsCrossCommutation.componentCycleType_eq {G G' : GridDiagram n}
    (h : IsCrossCommutation G G') : G'.componentCycleType = G.componentCycleType := by
  rcases h with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩
  · exact componentCycleType_relabelRows G _
  · exact componentCycleType_relabelColumns G _

/-- A cross-commutation preserves the number of components of the represented link. -/
theorem IsCrossCommutation.componentCount_eq {G G' : GridDiagram n}
    (h : IsCrossCommutation G G') : G'.componentCount = G.componentCount := by
  rw [componentCount_def, h.componentCycleType_eq, componentCount_def]

/-- A cross-commutation preserves whether a grid diagram represents a knot. -/
theorem IsCrossCommutation.isKnot_iff {G G' : GridDiagram n} (h : IsCrossCommutation G G') :
    G'.IsKnot ↔ G.IsKnot := by
  rw [isKnot_def, h.componentCount_eq, isKnot_def]

end GridDiagram

end TauCeti
