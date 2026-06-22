/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.KnotTheory.Grid.Commutation

/-!
# Relabeling and grid commutation arcs

This file records the relabeling bookkeeping for the row and column arcs used in grid
commutation hypotheses. A column relabeling only renames the columns, so it transports column
arcs and column non-interleaving by applying the inverse column permutation to the labels. Dually,
a row relabeling only renames the rows, so it transports row arcs and row non-interleaving by the
inverse row permutation.

The deliberately absent mixed statements are the point: an arbitrary row permutation need not
preserve the cyclic order in the row coordinate, so it does not transport column arcs to column
arcs; likewise for arbitrary column permutations and row arcs. The swap corollaries specialize the
permutation formulas to the elementary grid commutations used later.

## Main results

* `TauCeti.GridDiagram.columnArc_relabelColumns` and
  `TauCeti.GridDiagram.columnsNoninterleaving_relabelColumns`: column commutation data is renamed
  by column relabeling.
* `TauCeti.GridDiagram.rowArc_relabelRows` and
  `TauCeti.GridDiagram.rowsNoninterleaving_relabelRows`: row commutation data is renamed by row
  relabeling.
* `TauCeti.GridDiagram.columnArc_swapColumns`,
  `TauCeti.GridDiagram.columnsNoninterleaving_swapColumns`,
  `TauCeti.GridDiagram.rowArc_swapRows`, and
  `TauCeti.GridDiagram.rowsNoninterleaving_swapRows`: the corresponding elementary swap forms.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane
G.5, "Invariance over 𝔽₂. Grid moves = commutation + (de)stabilization", where commutation maps
are attached to elementary row and column commutations. The conventions follow
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

namespace GridState

variable {n : ℕ} (x : GridState n)

/-- Row relabeling moves the column containing a given row by reading the old state at the
inverse row label. -/
@[simp]
theorem columnOfRow_relabelRows (ρ : Equiv.Perm (Fin n)) (r : Fin n) :
    (x.relabelRows ρ).columnOfRow r = x.columnOfRow (ρ.symm r) := by
  apply (x.relabelRows ρ).toPerm.injective
  simp

/-- Column relabeling moves the column containing a given row by applying the column permutation
to the old column. -/
@[simp]
theorem columnOfRow_relabelColumns (κ : Equiv.Perm (Fin n)) (r : Fin n) :
    (x.relabelColumns κ).columnOfRow r = κ (x.columnOfRow r) := by
  apply (x.relabelColumns κ).toPerm.injective
  simp

/-- After swapping rows, the column containing row `r` is the old column containing the swapped
row label. -/
@[simp]
theorem columnOfRow_swapRows (a b r : Fin n) :
    (x.swapRows a b).columnOfRow r = x.columnOfRow (Equiv.swap a b r) := by
  simp [swapRows]

/-- After swapping columns, the column containing row `r` is the swap of the old column
containing that row. -/
@[simp]
theorem columnOfRow_swapColumns (a b r : Fin n) :
    (x.swapColumns a b).columnOfRow r = Equiv.swap a b (x.columnOfRow r) := by
  simp [swapColumns]

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- Row relabeling moves the `O` column lookup by reading the old diagram at the inverse row
label. -/
@[simp]
theorem OColumnOfRow_relabelRows (ρ : Equiv.Perm (Fin n)) (r : Fin n) :
    OColumnOfRow (G.relabelRows ρ) r = OColumnOfRow G (ρ.symm r) := by
  simp [OColumnOfRow]

/-- Row relabeling moves the `X` column lookup by reading the old diagram at the inverse row
label. -/
@[simp]
theorem XColumnOfRow_relabelRows (ρ : Equiv.Perm (Fin n)) (r : Fin n) :
    XColumnOfRow (G.relabelRows ρ) r = XColumnOfRow G (ρ.symm r) := by
  simp [XColumnOfRow]

/-- Column relabeling moves the `O` column lookup by applying the column permutation to the old
lookup. -/
@[simp]
theorem OColumnOfRow_relabelColumns (κ : Equiv.Perm (Fin n)) (r : Fin n) :
    OColumnOfRow (G.relabelColumns κ) r = κ (OColumnOfRow G r) := by
  simp [OColumnOfRow]

/-- Column relabeling moves the `X` column lookup by applying the column permutation to the old
lookup. -/
@[simp]
theorem XColumnOfRow_relabelColumns (κ : Equiv.Perm (Fin n)) (r : Fin n) :
    XColumnOfRow (G.relabelColumns κ) r = κ (XColumnOfRow G r) := by
  simp [XColumnOfRow]

/-- After swapping rows, the `O` marking in row `r` lies in the old `O` column for the swapped
row label. -/
@[simp]
theorem OColumnOfRow_swapRows (a b r : Fin n) :
    OColumnOfRow (G.swapRows a b) r = OColumnOfRow G (Equiv.swap a b r) := by
  simp [swapRows]

/-- After swapping rows, the `X` marking in row `r` lies in the old `X` column for the swapped
row label. -/
@[simp]
theorem XColumnOfRow_swapRows (a b r : Fin n) :
    XColumnOfRow (G.swapRows a b) r = XColumnOfRow G (Equiv.swap a b r) := by
  simp [swapRows]

/-- After swapping columns, the `O` marking in row `r` lies in the swapped old `O` column. -/
@[simp]
theorem OColumnOfRow_swapColumns (a b r : Fin n) :
    OColumnOfRow (G.swapColumns a b) r = Equiv.swap a b (OColumnOfRow G r) := by
  simp [swapColumns]

/-- After swapping columns, the `X` marking in row `r` lies in the swapped old `X` column. -/
@[simp]
theorem XColumnOfRow_swapColumns (a b r : Fin n) :
    XColumnOfRow (G.swapColumns a b) r = Equiv.swap a b (XColumnOfRow G r) := by
  simp [swapColumns]

/-- Column relabeling only renames the column whose vertical arc is being read. -/
@[simp]
theorem columnArc_relabelColumns (κ : Equiv.Perm (Fin n)) (c : Fin n) :
    columnArc (G.relabelColumns κ) c = columnArc G (κ.symm c) := by
  simp [columnArc]

/-- Membership in a column arc after column relabeling is membership in the old arc with the
inverse column label. -/
@[simp]
theorem mem_columnArc_relabelColumns (κ : Equiv.Perm (Fin n)) (c r : Fin n) :
    r ∈ columnArc (G.relabelColumns κ) c ↔ r ∈ columnArc G (κ.symm c) := by
  rw [columnArc_relabelColumns]

/-- A column swap renames the column whose vertical arc is being read. -/
@[simp]
theorem columnArc_swapColumns (a b c : Fin n) :
    columnArc (G.swapColumns a b) c = columnArc G (Equiv.swap a b c) := by
  simp [swapColumns]

/-- Membership in a column arc after a column swap is membership in the old arc with the swapped
column label. -/
@[simp]
theorem mem_columnArc_swapColumns (a b c r : Fin n) :
    r ∈ columnArc (G.swapColumns a b) c ↔ r ∈ columnArc G (Equiv.swap a b c) := by
  rw [columnArc_swapColumns]

/-- Column non-interleaving is transported by column relabeling through the inverse labels. -/
@[simp]
theorem columnsNoninterleaving_relabelColumns (κ : Equiv.Perm (Fin n)) (a b : Fin n) :
    ColumnsNoninterleaving (G.relabelColumns κ) a b ↔
      ColumnsNoninterleaving G (κ.symm a) (κ.symm b) := by
  rfl

/-- Column non-interleaving is transported by a column swap through the swapped labels. -/
@[simp]
theorem columnsNoninterleaving_swapColumns (a b c d : Fin n) :
    ColumnsNoninterleaving (G.swapColumns a b) c d ↔
      ColumnsNoninterleaving G (Equiv.swap a b c) (Equiv.swap a b d) := by
  simp [swapColumns]

/-- Row relabeling only renames the row whose horizontal arc is being read. -/
@[simp]
theorem rowArc_relabelRows (ρ : Equiv.Perm (Fin n)) (r : Fin n) :
    rowArc (G.relabelRows ρ) r = rowArc G (ρ.symm r) := by
  simp [rowArc]

/-- Membership in a row arc after row relabeling is membership in the old arc with the inverse
row label. -/
@[simp]
theorem mem_rowArc_relabelRows (ρ : Equiv.Perm (Fin n)) (r c : Fin n) :
    c ∈ rowArc (G.relabelRows ρ) r ↔ c ∈ rowArc G (ρ.symm r) := by
  rw [rowArc_relabelRows]

/-- A row swap renames the row whose horizontal arc is being read. -/
@[simp]
theorem rowArc_swapRows (a b r : Fin n) :
    rowArc (G.swapRows a b) r = rowArc G (Equiv.swap a b r) := by
  simp [swapRows]

/-- Membership in a row arc after a row swap is membership in the old arc with the swapped row
label. -/
@[simp]
theorem mem_rowArc_swapRows (a b r c : Fin n) :
    c ∈ rowArc (G.swapRows a b) r ↔ c ∈ rowArc G (Equiv.swap a b r) := by
  rw [rowArc_swapRows]

/-- Row non-interleaving is transported by row relabeling through the inverse labels. -/
@[simp]
theorem rowsNoninterleaving_relabelRows (ρ : Equiv.Perm (Fin n)) (a b : Fin n) :
    RowsNoninterleaving (G.relabelRows ρ) a b ↔
      RowsNoninterleaving G (ρ.symm a) (ρ.symm b) := by
  rfl

/-- Row non-interleaving is transported by a row swap through the swapped labels. -/
@[simp]
theorem rowsNoninterleaving_swapRows (a b c d : Fin n) :
    RowsNoninterleaving (G.swapRows a b) c d ↔
      RowsNoninterleaving G (Equiv.swap a b c) (Equiv.swap a b d) := by
  simp [swapRows]

end GridDiagram

end TauCeti
