/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Basic

/-!
# The squares a toroidal rectangle covers

A toroidal grid rectangle has two different finite domains, and the grid gradings need both.
Its corners are grid points, that is, intersections of grid lines, and the grid points strictly
inside it are `GridRectangle.interior`, the product of the two open cyclic intervals: this is the
domain against which a grid state is tested for emptiness. The `O`- and `X`-markings, however,
sit at the centres of squares, so a marked square lies inside the rectangle exactly when its
index lies in the **half-open** cyclic interval in each direction. That domain is
`GridRectangle.coveredSquares`, the product of the two half-open arcs
`Grid.cIco left right` and `Grid.cIco bottom top`.

When the vertical sides differ, `coveredSquares` includes the initial column in addition to the
open column interval; when they coincide, both column sets are empty. The analogous statement
holds for rows. `GridRectangle.interior_subset_coveredSquares` records the resulting inclusion
without a nondegeneracy hypothesis.

The convention that markings sit at the centres of their squares is the one the Maslov and
Alexander gradings already use (`JFunction/Center.lean`); this file supplies the matching
rectangle domain, which `Grading/MarkingCount.lean` then uses to turn the Maslov and Alexander
grading changes across a rectangle move into marking counts. The marking-avoidance predicate of
the grid differential, `GridRectangle.AvoidsMarkings`, tests that same square-centred region under
its other name `GridRectangle.squares`; `GridRectangle.squares_eq_coveredSquares` identifies the
two.

## Main definitions

* `TauCeti.GridRectangle.coveredColumns`, `TauCeti.GridRectangle.coveredRows`: the columns and
  rows of squares a toroidal rectangle covers.
* `TauCeti.GridRectangle.coveredSquares`: the squares a toroidal rectangle covers.

## Main results

* `TauCeti.GridRectangle.interior_subset_coveredSquares`: every grid point strictly inside a
  rectangle names a square the rectangle covers.
* `TauCeti.GridRectangle.disjoint_coveredSquares_iff`: two covered-square domains are disjoint
  exactly when their covered columns or their covered rows are disjoint.
* `TauCeti.GridRectangle.card_coveredSquares`: the number of covered squares is the product of the
  two arc lengths.
* `TauCeti.GridRectangle.squares_eq_coveredSquares`: the covered squares are the region
  `GridRectangle.squares` that the marking-avoidance predicate tests.
* `TauCeti.GridDiagram.disjoint_coveredSquares_XSet_swapColumns_of_subinterval`: X-avoidance
  transfers across a column swap to a rectangle whose covered columns are contained in an
  X-avoiding rectangle's covered columns and whose rows are contained in its rows.
* `TauCeti.GridDiagram.X_not_mem_coveredRows_of_disjoint`: the X-marking of a covered column
  avoids an X-avoiding rectangle's covered rows.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2,
"Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas
across a rectangle." The placement of the markings at the centres of their squares, and hence the
half-open shape of the domain they are counted in, follows Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapters 3.1--3.2 and 4.1.
-/

public section

namespace TauCeti

namespace GridRectangle

variable {n : ℕ} (R : GridRectangle n)

/-- The columns of squares covered by a toroidal grid rectangle: the clockwise half-open arc
from the initial vertical side to the terminal one. -/
noncomputable def coveredColumns : Finset (Fin n) :=
  Grid.cIco R.left R.right

/-- The covered columns are the half-open cyclic interval between the vertical sides. -/
theorem coveredColumns_def : R.coveredColumns = Grid.cIco R.left R.right :=
  (rfl)

/-- The rows of squares covered by a toroidal grid rectangle: the clockwise half-open arc from
the initial horizontal side to the terminal one. -/
noncomputable def coveredRows : Finset (Fin n) :=
  Grid.cIco R.bottom R.top

/-- The covered rows are the half-open cyclic interval between the horizontal sides. -/
theorem coveredRows_def : R.coveredRows = Grid.cIco R.bottom R.top :=
  (rfl)

/-- Membership in the covered columns is membership in the corresponding half-open circular
interval. -/
@[simp]
theorem mem_coveredColumns (c : Fin n) : c ∈ R.coveredColumns ↔ c ∈ Grid.cIco R.left R.right :=
  Iff.rfl

/-- Membership in the covered rows is membership in the corresponding half-open circular
interval. -/
@[simp]
theorem mem_coveredRows (r : Fin n) : r ∈ R.coveredRows ↔ r ∈ Grid.cIco R.bottom R.top :=
  Iff.rfl

/-- Every interior column is a covered column. For distinct vertical sides the covered columns
also contain the initial column; for coincident sides both sets are empty. -/
theorem columnInterior_subset_coveredColumns : R.columnInterior ⊆ R.coveredColumns :=
  Grid.cIoo_subset_cIco R.left R.right

/-- Every interior row is a covered row. For distinct horizontal sides the covered rows also
contain the initial row; for coincident sides both sets are empty. -/
theorem rowInterior_subset_coveredRows : R.rowInterior ⊆ R.coveredRows :=
  Grid.cIoo_subset_cIco R.bottom R.top

/-- The number of covered columns, expressed in the standard representatives of the sides. -/
@[simp]
theorem card_coveredColumns :
    R.coveredColumns.card =
      if R.left = R.right then 0
      else if R.left.val < R.right.val then R.right.val - R.left.val
      else n - R.left.val + R.right.val := by
  rw [coveredColumns, Grid.card_cIco]

/-- The number of covered rows, expressed in the standard representatives of the sides. -/
@[simp]
theorem card_coveredRows :
    R.coveredRows.card =
      if R.bottom = R.top then 0
      else if R.bottom.val < R.top.val then R.top.val - R.bottom.val
      else n - R.bottom.val + R.top.val := by
  rw [coveredRows, Grid.card_cIco]

/-- The finite set of squares a toroidal grid rectangle covers.

A marking sits at the centre of its square, so it lies inside the rectangle exactly when its
column and row indices lie in the two half-open arcs. -/
noncomputable def coveredSquares : Finset (Fin n × Fin n) :=
  R.coveredColumns ×ˢ R.coveredRows

/-- The covered squares are the product of the covered columns and rows. -/
theorem coveredSquares_def : R.coveredSquares = R.coveredColumns ×ˢ R.coveredRows :=
  (rfl)

/-- Membership in the covered squares is membership in both one-dimensional half-open arcs. -/
@[simp]
theorem mem_coveredSquares (p : Fin n × Fin n) :
    p ∈ R.coveredSquares ↔ p.1 ∈ R.coveredColumns ∧ p.2 ∈ R.coveredRows := by
  simp [coveredSquares]

/-- Swapping two columns preserves a rectangle's covered squares when the rectangle either
covers both columns or covers neither. -/
theorem mem_coveredSquares_swap_iff_of_coveredColumns {a b : Fin n}
    (h : a ∈ R.coveredColumns ↔ b ∈ R.coveredColumns) (p : Fin n × Fin n) :
    (Equiv.swap a b p.1, p.2) ∈ R.coveredSquares ↔ p ∈ R.coveredSquares := by
  have hcolumn (c : Fin n) : Equiv.swap a b c ∈ R.coveredColumns ↔ c ∈ R.coveredColumns := by
    by_cases hca : c = a
    · rw [hca, Equiv.swap_apply_left]
      exact h.symm
    · by_cases hcb : c = b
      · rw [hcb, Equiv.swap_apply_right]
        exact h
      · rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
  simp only [mem_coveredSquares, hcolumn]

/-- Two rectangles have disjoint covered-square domains exactly when their covered columns or
their covered rows are disjoint. -/
theorem disjoint_coveredSquares_iff (R S : GridRectangle n) :
    Disjoint R.coveredSquares S.coveredSquares ↔
      Disjoint R.coveredColumns S.coveredColumns ∨ Disjoint R.coveredRows S.coveredRows := by
  rw [coveredSquares_def, coveredSquares_def]
  exact Finset.disjoint_product

/-- Every grid point strictly inside a rectangle names a square that the rectangle covers. -/
theorem interior_subset_coveredSquares : R.interior ⊆ R.coveredSquares :=
  Finset.product_subset_product R.columnInterior_subset_coveredColumns
    R.rowInterior_subset_coveredRows

/-- The squares a rectangle covers are the region the marking-avoidance predicate tests: both
`GridRectangle.squares` and `coveredSquares` are the product of the two half-open arcs. -/
theorem squares_eq_coveredSquares : R.squares = R.coveredSquares := by
  ext p
  simp [mem_coveredSquares]

/-- The number of covered squares is the product of the numbers of covered columns and covered
rows. -/
@[simp]
theorem card_coveredSquares :
    R.coveredSquares.card = R.coveredColumns.card * R.coveredRows.card := by
  simp [coveredSquares, Finset.card_product]

end GridRectangle

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- Avoidance of the `X`-markings is unchanged by swapping two columns of the diagram when the
rectangle either covers both columns or covers neither. -/
theorem disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns (R : GridRectangle n)
    {a b : Fin n} (h : a ∈ R.coveredColumns ↔ b ∈ R.coveredColumns) :
    Disjoint R.coveredSquares (G.swapColumns a b).XSet ↔ Disjoint R.coveredSquares G.XSet := by
  rw [Finset.disjoint_left, Finset.disjoint_left]
  constructor
  · intro hdisjoint p hp hpX
    apply hdisjoint
    · exact (R.mem_coveredSquares_swap_iff_of_coveredColumns h p).mpr hp
    · rw [G.mem_XSet_swapColumns]
      simpa only [Equiv.swap_apply_self] using hpX
  · intro hdisjoint p hp hpX
    rw [G.mem_XSet_swapColumns] at hpX
    apply hdisjoint
    · exact (R.mem_coveredSquares_swap_iff_of_coveredColumns h p).mpr hp
    · exact hpX

/-- X-avoidance transfers across a column swap to a rectangle whose covered columns are
contained in an X-avoiding rectangle's covered columns (with rows contained in the
original's), provided the swapped-out column is covered by the original rectangle but not
by the new one. -/
theorem disjoint_coveredSquares_XSet_swapColumns_of_subinterval
    (R R' : GridRectangle n) {a b : Fin n}
    (hR'row : R'.coveredRows ⊆ R.coveredRows)
    (hX : Disjoint R.coveredSquares G.XSet)
    (ha : a ∈ R.coveredColumns)
    (ha_not : a ∉ R'.coveredColumns)
    (hsub : R'.coveredColumns ⊆ R.coveredColumns) :
    Disjoint R'.coveredSquares (G.swapColumns a b).XSet := by
  rw [Finset.disjoint_left]
  rintro ⟨c, r'⟩ hc hx
  -- For `(c, r')` in `R'`'s squares with `(c, r')` in the swapped X-set: if `c = b`, the
  -- swap sends it to `(a, r')`, which lies in `R`'s squares and contradicts `R`'s
  -- X-avoidance; otherwise the swap fixes `c` (as `c ≠ a` and `c ≠ b`), and `(c, r')`
  -- lies in `R`'s squares via the column subset, again contradicting `R`'s X-avoidance.
  rw [GridRectangle.mem_coveredSquares] at hc
  obtain ⟨hc_col, hc_row⟩ := hc
  rw [G.mem_XSet_swapColumns] at hx
  by_cases hcb : c = b
  · subst hcb
    rw [Equiv.swap_apply_right] at hx
    have hmem : (a, r') ∈ R.coveredSquares := by
      rw [GridRectangle.mem_coveredSquares]
      exact ⟨ha, hR'row hc_row⟩
    exact (Finset.disjoint_left.mp hX) hmem hx
  · have hca : c ≠ a := fun h => ha_not (h ▸ hc_col)
    have hswap : Equiv.swap a b c = c := Equiv.swap_apply_of_ne_of_ne hca hcb
    rw [hswap] at hx
    have hmem : (c, r') ∈ R.coveredSquares := by
      rw [GridRectangle.mem_coveredSquares]
      exact ⟨hsub hc_col, hR'row hc_row⟩
    exact (Finset.disjoint_left.mp hX) hmem hx

/-- The X-marking of a covered column avoids an X-avoiding rectangle's covered rows: if
`G.X b` were in the row interval, `(b, G.X b)` would be a covered square carrying an
X-marking. -/
theorem X_not_mem_coveredRows_of_disjoint (R : GridRectangle n) {b : Fin n}
    (hX : Disjoint R.coveredSquares G.XSet)
    (hb : b ∈ R.coveredColumns) :
    G.X b ∉ R.coveredRows := by
  intro hmem
  have hmem_sq : (b, G.X b) ∈ R.coveredSquares := by
    rw [GridRectangle.mem_coveredSquares]
    exact ⟨hb, hmem⟩
  have hXmem : (b, G.X b) ∈ G.XSet := by simp [GridDiagram.XSet]
  exact (Finset.disjoint_left.mp hX) hmem_sq hXmem

end GridDiagram

end TauCeti
