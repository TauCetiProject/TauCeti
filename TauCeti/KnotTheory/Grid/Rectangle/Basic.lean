/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import TauCeti.KnotTheory.Grid.CyclicInterval
public import TauCeti.KnotTheory.Grid.Diagram.Basic

/-!
# Rectangles in grid diagrams

The grid lives on a torus, so the basic one-dimensional ingredient of a rectangle is the circular
interval in `Fin n`. A grid rectangle carries two finite coordinate sets built from such intervals:
its `interior`, the product of two open intervals, records the grid points strictly inside and
is what a grid state must avoid for the rectangle to be empty; its `coveredSquares`, the product
of two half-open intervals, records the region the rectangle covers and is what must avoid the
`O` and `X` markings.

The final section packages an oriented rectangle from one grid state to another: two columns
where the states exchange rows, and agreement everywhere else. This is the shape counted by
the grid differential; the `IsEmptyFor` and `AvoidsMarkings` predicates record the two
finite-set disjointness conditions used for empty rectangles and marking-avoiding rectangles.

`AvoidsMarkings` tests `coveredSquares`, so a marking counts as covered exactly when its square
lies under the rectangle: marking indices are the southwest corners of square-centred markings,
the convention the Maslov and Alexander gradings use. `Rectangle/Squares.lean` develops the
covered squares further for the gradings.

## Main definitions

* `TauCeti.GridRectangle`: a toroidal rectangle, represented by its four cyclic sides.
* `TauCeti.GridRectangle.transpose`: the diagonal reflection of a toroidal rectangle, exchanging
  the column and row sides.
* `TauCeti.GridRectangle.interior`: the finite set of grid points strictly inside the rectangle.
* `TauCeti.GridRectangle.coveredSquares`: the finite set of squares the rectangle covers, each
  named by its lower-left grid point.
* `TauCeti.GridRectangleBetween`: an oriented rectangle from one grid state to another.
* `TauCeti.GridRectangleBetween.swapSides`: the other oriented rectangle from `x` to `y` on the same
  two side columns, which runs along the complementary column arc and the complementary row arc.
* `TauCeti.GridRectangleBetween.transpose`: the diagonal reflection of an oriented rectangle, from
  `x.transpose` to `y.transpose`.
* `TauCeti.GridRectangleBetween.transposeEquiv`: the diagonal reflection packaged as an involutive
  equivalence with oriented rectangles from `x.transpose` to `y.transpose`.
* `TauCeti.GridRectangleBetween.emptyRectangles`: the empty rectangles from `x` to `y`.

## Main results

* `TauCeti.GridRectangle.isEmptyFor_iff_forall_notMem_cIoo`: emptiness of a toroidal rectangle
  for a grid state, quantified over the columns strictly inside it, and
  `TauCeti.GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo`, its form for an oriented
  rectangle and its source state, with
  `TauCeti.GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo_target` the same test read through
  the target state.
* `TauCeti.GridRectangleBetween.isEmpty_of_right_eq_finRotate`: a rectangle one column wide is
  empty.
* `TauCeti.GridRectangle.avoidsMarkings_iff_forall`: marking avoidance tested column by column.
* `TauCeti.GridRectangleBetween.toGridRectangle_eq`: the toroidal rectangle underlying an
  oriented rectangle, in terms of its two side columns.

## References

The encoding follows the toroidal grid-diagram convention from Ozsváth--Stipsicz--Szabó, *Grid
Homology for Knots and Links*, Chapter 3; the marking-avoidance condition defining the fully
blocked complex is in Chapter 4, Section 4.4.
-/

@[expose] public section

namespace TauCeti

/-- A toroidal grid rectangle, represented by its oriented column and row sides.

The interior is the product of the clockwise open interval from `left` to `right` with the
clockwise open interval from `bottom` to `top`. Degenerate side choices are allowed at this
level; their interiors are empty in the degenerate direction. -/
@[ext]
structure GridRectangle (n : ℕ) where
  /-- The initial vertical side of the rectangle. -/
  left : Fin n
  /-- The terminal vertical side of the rectangle. -/
  right : Fin n
  /-- The initial horizontal side of the rectangle. -/
  bottom : Fin n
  /-- The terminal horizontal side of the rectangle. -/
  top : Fin n

namespace GridRectangle

variable {n : ℕ} (R : GridRectangle n)

/-- The columns strictly inside a toroidal grid rectangle. -/
noncomputable def columnInterior : Finset (Fin n) :=
  Grid.cIoo R.left R.right

/-- The rows strictly inside a toroidal grid rectangle. -/
noncomputable def rowInterior : Finset (Fin n) :=
  Grid.cIoo R.bottom R.top

/-- Membership in the interior columns is membership in the corresponding open-open circular
interval. -/
@[simp]
theorem mem_columnInterior (c : Fin n) :
    c ∈ R.columnInterior ↔ c ∈ Grid.cIoo R.left R.right := by
  rfl

/-- Membership in the interior rows is membership in the corresponding open-open circular
interval. -/
@[simp]
theorem mem_rowInterior (r : Fin n) :
    r ∈ R.rowInterior ↔ r ∈ Grid.cIoo R.bottom R.top := by
  rfl

/-- The left side is not an interior column. -/
theorem left_notMem_columnInterior : R.left ∉ R.columnInterior := by
  simp [columnInterior]

/-- The right side is not an interior column. -/
theorem right_notMem_columnInterior : R.right ∉ R.columnInterior := by
  simp [columnInterior]

/-- The bottom side is not an interior row. -/
theorem bottom_notMem_rowInterior : R.bottom ∉ R.rowInterior := by
  simp [rowInterior]

/-- The top side is not an interior row. -/
theorem top_notMem_rowInterior : R.top ∉ R.rowInterior := by
  simp [rowInterior]

/-- The finite set of grid points strictly inside a toroidal grid rectangle. -/
noncomputable def interior : Finset (Fin n × Fin n) :=
  R.columnInterior ×ˢ R.rowInterior

/-- Membership in a rectangle interior is membership in both one-dimensional open intervals. -/
@[simp]
theorem mem_interior (p : Fin n × Fin n) :
    p ∈ R.interior ↔ p.1 ∈ R.columnInterior ∧ p.2 ∈ R.rowInterior := by
  simp [interior]

/-- A point on the initial side column is not in the interior. -/
theorem notMem_interior_of_fst_eq_left {p : Fin n × Fin n} (hp : p.1 = R.left) :
    p ∉ R.interior :=
  fun h ↦ R.left_notMem_columnInterior (hp ▸ ((R.mem_interior p).1 h).1)

/-- A point on the terminal side column is not in the interior. -/
theorem notMem_interior_of_fst_eq_right {p : Fin n × Fin n} (hp : p.1 = R.right) :
    p ∉ R.interior :=
  fun h ↦ R.right_notMem_columnInterior (hp ▸ ((R.mem_interior p).1 h).1)

/-- A rectangle has empty interior if its two column sides coincide. -/
@[simp]
theorem interior_eq_empty_of_left_eq_right (h : R.left = R.right) : R.interior = ∅ := by
  ext p
  simp [interior, columnInterior, h]

/-- A rectangle has empty interior if its two row sides coincide. -/
@[simp]
theorem interior_eq_empty_of_bottom_eq_top (h : R.bottom = R.top) : R.interior = ∅ := by
  ext p
  simp [interior, rowInterior, h]

/-- The number of interior grid points is the product of the numbers of interior columns and
interior rows. -/
@[simp]
theorem card_interior :
    R.interior.card = R.columnInterior.card * R.rowInterior.card := by
  simp [interior, Finset.card_product]

/-- In a grid of size at most two, every toroidal rectangle has empty interior. -/
theorem interior_eq_empty_of_le_two (hn : n ≤ 2) (R : GridRectangle n) : R.interior = ∅ := by
  ext p
  simp [interior, columnInterior, Grid.cIoo_eq_empty_of_le_two hn R.left R.right]

/-- The columns of squares a toroidal grid rectangle covers: the clockwise half-open arc from the
initial vertical side to the terminal one. For distinct sides this is the initial side together
with the strictly interior columns, each column of squares named by its initial grid line; for
coincident sides it is empty. -/
noncomputable def coveredColumns : Finset (Fin n) :=
  Grid.cIco R.left R.right

/-- The covered columns are the half-open cyclic interval between the vertical sides. -/
theorem coveredColumns_def : R.coveredColumns = Grid.cIco R.left R.right :=
  (rfl)

/-- The rows of squares a toroidal grid rectangle covers: the clockwise half-open arc from the
initial horizontal side to the terminal one. For distinct sides this is the initial side together
with the strictly interior rows, each row of squares named by its initial grid line; for
coincident sides it is empty. -/
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

/-- The finite set of squares a toroidal grid rectangle covers, each square named by its
lower-left grid point, following the marking-coordinate convention documented with
`GridDiagram.OSet` and `GridDiagram.XSet`.

Where `interior` records the grid points strictly inside the rectangle — what a grid state must
avoid for the rectangle to be empty — `coveredSquares` records the region the rectangle covers,
which is what contains or avoids the `O` and `X` markings placed in the squares of a grid
diagram: a marking sits at the centre of its square, so it lies inside the rectangle exactly when
its column and row indices lie in the two half-open arcs. If either pair of sides coincides, the
covered set is empty. -/
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

/-- A rectangle is empty for a grid state when the state has no point in its interior. -/
def IsEmptyFor (x : GridState n) : Prop :=
  Disjoint R.interior x.pointSet

/-- A rectangle is empty for a grid state exactly when no point of the state lies in its
interior. -/
theorem isEmptyFor_iff (x : GridState n) :
    R.IsEmptyFor x ↔ ∀ p ∈ x.pointSet, p ∉ R.interior :=
  Finset.disjoint_right

/-- A rectangle is empty for a grid state exactly when the state sends every column strictly
between its two side columns to a row outside the open arc between its two side rows.

This is the one-dimensional form of emptiness that the rectangle-pairing arguments for the grid
differential use: it quantifies over columns rather than over grid points. -/
theorem isEmptyFor_iff_forall_notMem_cIoo (x : GridState n) :
    R.IsEmptyFor x ↔ ∀ c ∈ Grid.cIoo R.left R.right, x c ∉ Grid.cIoo R.bottom R.top := by
  rw [isEmptyFor_iff]
  simp only [GridState.mem_pointSet, mem_interior, mem_columnInterior, mem_rowInterior, not_and]
  constructor
  · intro h c hc
    exact h (c, x c) rfl hc
  · intro h p hp hc
    exact hp ▸ h p.1 hc

/-- A rectangle whose terminal side is the cyclic successor of its initial side is empty for every
grid state: no column lies strictly between two cyclically consecutive ones. -/
theorem isEmptyFor_of_right_eq_finRotate (x : GridState n) (h : R.right = finRotate n R.left) :
    R.IsEmptyFor x := by
  rw [isEmptyFor_iff_forall_notMem_cIoo, h, Grid.cIoo_finRotate_eq_empty]
  exact fun c hc => absurd hc (Finset.notMem_empty c)

/-- In a grid of size at most two, every toroidal rectangle is empty for every grid state. -/
theorem isEmptyFor_of_le_two (hn : n ≤ 2) (R : GridRectangle n) (x : GridState n) :
    R.IsEmptyFor x := by
  rw [IsEmptyFor, R.interior_eq_empty_of_le_two hn]
  simp

/-- Emptiness transfers between two grid states that agree away from two columns, once the two
points of the first state on those columns are known to lie outside the rectangle: every other
point of the first state is a point of the second. -/
theorem isEmptyFor_of_eq_away {u v : GridState n} (a b : Fin n)
    (ha : (a, u a) ∉ R.interior) (hb : (b, u b) ∉ R.interior)
    (haway : ∀ p : Fin n × Fin n, p.1 ≠ a → p.1 ≠ b → p ∈ u.pointSet → p ∈ v.pointSet)
    (hv : R.IsEmptyFor v) : R.IsEmptyFor u := by
  rw [R.isEmptyFor_iff]
  intro p hp hmem
  have hpu : u p.1 = p.2 := (u.mem_pointSet p).mp hp
  by_cases hpa : p.1 = a
  · apply ha
    simpa [hpa, ← hpu] using hmem
  by_cases hpb : p.1 = b
  · apply hb
    simpa [hpb, ← hpu] using hmem
  exact (R.isEmptyFor_iff v).mp hv p (haway p hpa hpb hp) hmem

/-- A rectangle avoids the markings of a grid diagram when none of the squares it covers
carries an `O` or `X` marking. -/
def AvoidsMarkings (G : GridDiagram n) : Prop :=
  Disjoint R.coveredSquares (G.OSet ∪ G.XSet)

/-- A marking-avoiding rectangle covers no square carrying an `O` marking. -/
theorem disjoint_coveredSquares_OSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.coveredSquares G.OSet :=
  h.mono_right Finset.subset_union_left

/-- A marking-avoiding rectangle covers no square carrying an `X` marking. -/
theorem disjoint_coveredSquares_XSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.coveredSquares G.XSet :=
  h.mono_right Finset.subset_union_right

/-- A rectangle avoids markings exactly when neither the `O` nor the `X` marking set meets
the squares it covers. -/
theorem avoidsMarkings_iff (G : GridDiagram n) :
    R.AvoidsMarkings G ↔
      Disjoint R.coveredSquares G.OSet ∧ Disjoint R.coveredSquares G.XSet := by
  rw [AvoidsMarkings, Finset.disjoint_union_right]

/-- A rectangle avoids markings exactly when, in each column of squares it covers, neither the
`O` marking nor the `X` marking of that column lies in a covered row. -/
theorem avoidsMarkings_iff_forall (G : GridDiagram n) :
    R.AvoidsMarkings G ↔
      ∀ c ∈ R.coveredColumns, G.O c ∉ R.coveredRows ∧ G.X c ∉ R.coveredRows := by
  simp only [AvoidsMarkings, Finset.disjoint_left, Finset.mem_union, not_or, Prod.forall,
    mem_coveredSquares, GridDiagram.mem_OSet, GridDiagram.mem_XSet]
  constructor
  · intro h c hc
    exact ⟨fun hO => (h c (G.O c) ⟨hc, hO⟩).1 rfl, fun hX => (h c (G.X c) ⟨hc, hX⟩).2 rfl⟩
  · rintro h c r ⟨hc, hr⟩
    exact ⟨fun hO => (h c hc).1 (hO ▸ hr), fun hX => (h c hc).2 (hX ▸ hr)⟩

/-- Marking avoidance is unchanged by swapping the `O` and `X` markings, since it only refers to
the union of the two marking sets. -/
@[simp]
theorem avoidsMarkings_swapMarkings (G : GridDiagram n) :
    R.AvoidsMarkings G.swapMarkings ↔ R.AvoidsMarkings G := by
  rw [avoidsMarkings_iff, avoidsMarkings_iff, GridDiagram.swapMarkings_OSet,
    GridDiagram.swapMarkings_XSet]
  exact and_comm

/-- The diagonal reflection of a toroidal rectangle, exchanging the two vertical sides with the
two horizontal sides.

Reflecting across the main diagonal turns columns into rows and rows into columns, so the
interior is reflected by `Prod.swap`. -/
def transpose : GridRectangle n where
  left := R.bottom
  right := R.top
  bottom := R.left
  top := R.right

/-- The reflected rectangle's left side is the original bottom side. -/
@[simp]
theorem transpose_left : R.transpose.left = R.bottom :=
  rfl

/-- The reflected rectangle's right side is the original top side. -/
@[simp]
theorem transpose_right : R.transpose.right = R.top :=
  rfl

/-- The reflected rectangle's bottom side is the original left side. -/
@[simp]
theorem transpose_bottom : R.transpose.bottom = R.left :=
  rfl

/-- The reflected rectangle's top side is the original right side. -/
@[simp]
theorem transpose_top : R.transpose.top = R.right :=
  rfl

/-- Reflecting a toroidal rectangle twice gives the original rectangle. -/
@[simp]
theorem transpose_transpose : R.transpose.transpose = R := by
  cases R
  rfl

/-- The interior of the reflected rectangle is the diagonal reflection of the original
interior. -/
theorem interior_transpose : R.transpose.interior = R.interior.image Prod.swap :=
  (Finset.image_swap_product _ _).symm

/-- The squares covered by the reflected rectangle are the diagonal reflections of the squares
covered by the original rectangle. -/
theorem coveredSquares_transpose : R.transpose.coveredSquares = R.coveredSquares.image Prod.swap :=
  (Finset.image_swap_product _ _).symm

/-- The diagonal reflection preserves emptiness: the reflected rectangle is empty for the reflected
state exactly when the rectangle is empty for the state. -/
@[simp]
theorem isEmptyFor_transpose (x : GridState n) :
    R.transpose.IsEmptyFor x.transpose ↔ R.IsEmptyFor x := by
  rw [IsEmptyFor, IsEmptyFor, R.interior_transpose, x.transpose_pointSet,
    Finset.disjoint_image Prod.swap_injective]

/-- The diagonal reflection preserves marking avoidance: the reflected rectangle avoids the
markings of the reflected diagram exactly when the rectangle avoids those of the diagram. -/
@[simp]
theorem avoidsMarkings_transpose (G : GridDiagram n) :
    R.transpose.AvoidsMarkings G.transpose ↔ R.AvoidsMarkings G := by
  rw [AvoidsMarkings, AvoidsMarkings, R.coveredSquares_transpose, G.transpose_OSet,
    G.transpose_XSet, ← Finset.image_union, Finset.disjoint_image Prod.swap_injective]

end GridRectangle

/-- An oriented toroidal rectangle from one grid state to another.

The two states agree outside the two side columns, and in those side columns they exchange the
two rows. Swapping `left` and `right` gives the other oriented rectangle from `x` to `y` on the
same side columns (`GridRectangleBetween.swapSides`). The two side columns determine the rectangle
(`GridRectangleBetween.ext`). -/
@[ext]
structure GridRectangleBetween {n : ℕ} (x y : GridState n) where
  /-- The initial vertical side. -/
  left : Fin n
  /-- The terminal vertical side. -/
  right : Fin n
  /-- The two side columns are distinct. -/
  left_ne_right : left ≠ right
  /-- At the initial side, `y` uses the row that `x` uses at the terminal side. -/
  map_left : y left = x right
  /-- At the terminal side, `y` uses the row that `x` uses at the initial side. -/
  map_right : y right = x left
  /-- Away from the side columns, the two states agree. -/
  map_of_ne : ∀ c : Fin n, c ≠ left → c ≠ right → y c = x c

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- The unordered finite set of side columns of an oriented grid rectangle. -/
def sideColumns (R : GridRectangleBetween x y) : Finset (Fin n) :=
  {R.left, R.right}

/-- Membership in the side-column set of an oriented grid rectangle. -/
@[simp]
theorem mem_sideColumns (R : GridRectangleBetween x y) (c : Fin n) :
    c ∈ R.sideColumns ↔ c = R.left ∨ c = R.right := by
  simp [sideColumns]

/-- An oriented grid rectangle has exactly two side columns. -/
@[simp]
theorem card_sideColumns (R : GridRectangleBetween x y) : R.sideColumns.card = 2 := by
  simp [sideColumns, R.left_ne_right]

/-- A rectangle between two grid states is determined by its two side columns. -/
theorem sidePair_injective :
    Function.Injective fun R : GridRectangleBetween x y => (R.left, R.right) :=
  fun _ _ h ↦ GridRectangleBetween.ext (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 h).2

/-- A rectangle between two fixed grid states is determined by its initial side column alone: the
exchange condition `y R.left = x R.right` fixes the terminal one. -/
theorem left_injective : Function.Injective fun R : GridRectangleBetween x y => R.left :=
  fun R S h ↦ GridRectangleBetween.ext h
    (x.toPerm.injective (R.map_left.symm.trans ((congrArg y h).trans S.map_left)))

/-- An oriented rectangle between two grid states has decidable equality: it is determined by its
ordered pair of side columns, which has decidable equality. -/
instance : DecidableEq (GridRectangleBetween x y) :=
  sidePair_injective.decidableEq

/-- For fixed source and target grid states, the oriented rectangles between them form a
finite type: a rectangle is its ordered pair of side columns, and the pairs that occur form a
decidable subset of `Fin n × Fin n`. The instance is computable, so `decide` can count
rectangles on a concrete grid. -/
instance : Fintype (GridRectangleBetween x y) :=
  Fintype.ofEquiv {p : Fin n × Fin n // p.1 ≠ p.2 ∧ y p.1 = x p.2 ∧ y p.2 = x p.1 ∧
      ∀ c, c ≠ p.1 → c ≠ p.2 → y c = x c}
    { toFun p := ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
      invFun R := ⟨(R.left, R.right), R.left_ne_right, R.map_left, R.map_right, R.map_of_ne⟩
      left_inv _ := rfl
      right_inv _ := rfl }

variable (R : GridRectangleBetween x y)

/-- The row of `x` on the initial side. -/
def bottom : Fin n :=
  x R.left

/-- The row of `x` on the terminal side. -/
def top : Fin n :=
  x R.right

/-- The initial horizontal side is the row occupied by the source state in the initial column. -/
theorem bottom_def : R.bottom = x R.left :=
  rfl

/-- The terminal horizontal side is the row occupied by the source state in the terminal column. -/
theorem top_def : R.top = x R.right :=
  rfl

/-- The associated toroidal rectangle. -/
def toGridRectangle : GridRectangle n where
  left := R.left
  right := R.right
  bottom := R.bottom
  top := R.top

/-- The associated toroidal rectangle has the same initial vertical side. -/
@[simp]
theorem toGridRectangle_left : R.toGridRectangle.left = R.left :=
  rfl

/-- The associated toroidal rectangle has the same terminal vertical side. -/
@[simp]
theorem toGridRectangle_right : R.toGridRectangle.right = R.right :=
  rfl

/-- The associated toroidal rectangle has the same initial horizontal side. -/
@[simp]
theorem toGridRectangle_bottom : R.toGridRectangle.bottom = R.bottom :=
  rfl

/-- The associated toroidal rectangle has the same terminal horizontal side. -/
@[simp]
theorem toGridRectangle_top : R.toGridRectangle.top = R.top :=
  rfl

/-- The associated toroidal rectangle in terms of the two side columns: its two horizontal
sides are the rows the source state assigns to them. -/
theorem toGridRectangle_eq :
    R.toGridRectangle =
      { left := R.left, right := R.right, bottom := x R.left, top := x R.right } :=
  rfl

/-- Membership in the interior of an oriented rectangle is membership in the open cyclic
intervals between its side columns and the corresponding source-state rows. -/
theorem mem_toGridRectangle_interior (p : Fin n × Fin n) :
    p ∈ R.toGridRectangle.interior ↔
      p.1 ∈ Grid.cIoo R.left R.right ∧ p.2 ∈ Grid.cIoo (x R.left) (x R.right) := by
  simp [bottom, top]

/-- Membership in the covered squares of an oriented rectangle is membership in the half-open
cyclic intervals between its side columns and the corresponding source-state rows. -/
theorem mem_toGridRectangle_coveredSquares (p : Fin n × Fin n) :
    p ∈ R.toGridRectangle.coveredSquares ↔
      p.1 ∈ Grid.cIco R.left R.right ∧ p.2 ∈ Grid.cIco (x R.left) (x R.right) := by
  simp [bottom, top]

/-- The covered squares of an oriented rectangle, read through its target state: the rows it
covers run from the target-state row at its terminal side to the target-state row at its initial
side. -/
theorem mem_toGridRectangle_coveredSquares_target (p : Fin n × Fin n) :
    p ∈ R.toGridRectangle.coveredSquares ↔
      p.1 ∈ Grid.cIco R.left R.right ∧ p.2 ∈ Grid.cIco (y R.right) (y R.left) := by
  rw [mem_toGridRectangle_coveredSquares, R.map_left, R.map_right]

/-- The two side rows of a rectangle between states are distinct. -/
theorem bottom_ne_top : R.bottom ≠ R.top := by
  intro h
  exact R.left_ne_right (x.toPerm.injective (by simpa [bottom, top] using h))

/-- A rectangle between grid states has distinct source and target states. A self-rectangle
would force the source state's permutation to take the same value on the two distinct side
columns. -/
theorem source_ne_target (R : GridRectangleBetween x y) : x ≠ y := by
  intro hxy
  cases hxy
  exact R.left_ne_right (x.toPerm.injective (by simpa [bottom, top] using R.map_left))

/-- There are no rectangles from a grid state to itself. -/
instance (x : GridState n) : IsEmpty (GridRectangleBetween x x) :=
  ⟨fun R => R.source_ne_target rfl⟩

/-- The initial lower corner is a point of the source state. -/
theorem left_bottom_mem_source : (R.left, R.bottom) ∈ x.pointSet := by
  simp [bottom]

/-- The associated rectangle covers its initial lower square. -/
theorem left_bottom_mem_coveredSquares :
    (R.left, R.bottom) ∈ R.toGridRectangle.coveredSquares := by
  rw [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
    GridRectangle.mem_coveredRows]
  exact ⟨Grid.left_mem_cIco R.left_ne_right, Grid.left_mem_cIco R.bottom_ne_top⟩

/-- The terminal upper corner is a point of the source state. -/
theorem right_top_mem_source : (R.right, R.top) ∈ x.pointSet := by
  simp [top]

/-- The initial upper corner is a point of the target state. -/
theorem left_top_mem_target : (R.left, R.top) ∈ y.pointSet := by
  simp [top, R.map_left]

/-- The terminal lower corner is a point of the target state. -/
theorem right_bottom_mem_target : (R.right, R.bottom) ∈ y.pointSet := by
  simp [bottom, R.map_right]

/-- Away from the two side columns, membership in the source and target states is identical. -/
theorem mem_target_pointSet_iff_of_ne {p : Fin n × Fin n}
    (hleft : p.1 ≠ R.left) (hright : p.1 ≠ R.right) :
    p ∈ y.pointSet ↔ p ∈ x.pointSet := by
  simp [R.map_of_ne p.1 hleft hright]

/-- The associated rectangle is empty for the source state when no source-state point lies in
its interior. -/
protected def IsEmpty : Prop :=
  R.toGridRectangle.IsEmptyFor x

/-- Emptiness of an oriented rectangle is emptiness of its underlying toroidal rectangle for the
source state. -/
theorem isEmpty_iff_toGridRectangle_isEmptyFor :
    R.IsEmpty ↔ R.toGridRectangle.IsEmptyFor x := Iff.rfl

/-- The finite set of empty oriented rectangles from `x` to `y`. -/
noncomputable def emptyRectangles (x y : GridState n) : Finset (GridRectangleBetween x y) := by
  classical
  exact Finset.univ.filter fun R => R.IsEmpty

/-- Membership in the finite set of empty rectangles is exactly the emptiness predicate. -/
@[simp]
theorem mem_emptyRectangles (R : GridRectangleBetween x y) :
    R ∈ emptyRectangles x y ↔ R.IsEmpty := by
  classical
  simp [emptyRectangles]

/-- In grid size at most two, every oriented rectangle between grid states is empty. -/
theorem isEmpty_of_le_two (hn : n ≤ 2) (R : GridRectangleBetween x y) : R.IsEmpty :=
  R.toGridRectangle.isEmptyFor_of_le_two hn x

/-- In grid size at most two, the empty rectangles are all oriented rectangles. -/
theorem emptyRectangles_eq_univ_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    emptyRectangles x y = Finset.univ := by
  ext R
  simp only [mem_emptyRectangles, Finset.mem_univ, iff_true]
  exact isEmpty_of_le_two hn R

/-- There are no empty rectangles from a grid state to itself. -/
@[simp]
theorem emptyRectangles_self (x : GridState n) : emptyRectangles x x = ∅ := by
  classical
  simp [emptyRectangles]

/-- The associated rectangle avoids a grid diagram's markings when none of the squares it
covers carries a marking. -/
def AvoidsMarkings (G : GridDiagram n) : Prop :=
  R.toGridRectangle.AvoidsMarkings G

/-- The source state has no point in the interior of an empty rectangle between states. -/
theorem notMem_interior_of_isEmpty (h : R.IsEmpty) {p : Fin n × Fin n}
    (hp : p ∈ x.pointSet) : p ∉ R.toGridRectangle.interior :=
  (R.toGridRectangle.isEmptyFor_iff x).mp h p hp

/-- A rectangle between states is empty exactly when no source-state point lies in its
interior. -/
protected theorem isEmpty_iff :
    R.IsEmpty ↔ ∀ p ∈ x.pointSet, p ∉ R.toGridRectangle.interior :=
  R.toGridRectangle.isEmptyFor_iff x

/-- A rectangle between states is empty exactly when the source state sends every column strictly
between its two side columns to a row outside the open arc between its two side rows.

This is the one-dimensional form of emptiness that the rectangle-pairing arguments for the grid
differential use: it quantifies over columns rather than over grid points. -/
theorem isEmpty_iff_forall_notMem_cIoo :
    R.IsEmpty ↔ ∀ c ∈ Grid.cIoo R.left R.right, x c ∉ Grid.cIoo R.bottom R.top :=
  R.toGridRectangle.isEmptyFor_iff_forall_notMem_cIoo x

/-- A rectangle between states whose terminal side is the cyclic successor of its initial side
is empty: no column lies strictly between two cyclically consecutive ones. -/
theorem isEmpty_of_right_eq_finRotate (h : R.right = finRotate n R.left) : R.IsEmpty :=
  R.toGridRectangle.isEmptyFor_of_right_eq_finRotate x h

/-- A rectangle between states is empty exactly when no target-state point lies in its
interior. -/
theorem isEmpty_iff_target :
    R.IsEmpty ↔ ∀ p ∈ y.pointSet, p ∉ R.toGridRectangle.interior := by
  have hl (c : Fin n) : (R.left, c) ∉ R.toGridRectangle.interior :=
    R.toGridRectangle.notMem_interior_of_fst_eq_left rfl
  have hr (c : Fin n) : (R.right, c) ∉ R.toGridRectangle.interior :=
    R.toGridRectangle.notMem_interior_of_fst_eq_right rfl
  rw [← GridRectangle.isEmptyFor_iff]
  exact ⟨R.toGridRectangle.isEmptyFor_of_eq_away R.left R.right (hl _) (hr _)
      fun _ hleft hright => (R.mem_target_pointSet_iff_of_ne hleft hright).mp,
    R.toGridRectangle.isEmptyFor_of_eq_away R.left R.right (hl _) (hr _)
      fun _ hleft hright => (R.mem_target_pointSet_iff_of_ne hleft hright).mpr⟩

/-- The target state has no point in the interior of an empty rectangle between states. -/
theorem notMem_interior_target_of_isEmpty (h : R.IsEmpty) {p : Fin n × Fin n}
    (hp : p ∈ y.pointSet) : p ∉ R.toGridRectangle.interior :=
  (R.isEmpty_iff_target).mp h p hp

/-- A rectangle between states is empty exactly when the target state sends every column strictly
between its two side columns to a row outside the open arc between its two side rows, read
through the target state: from its row at the terminal side to its row at the initial side.

This is `isEmpty_iff_forall_notMem_cIoo` for rectangles into a distinguished target state. -/
theorem isEmpty_iff_forall_notMem_cIoo_target :
    R.IsEmpty ↔ ∀ c ∈ Grid.cIoo R.left R.right, y c ∉ Grid.cIoo (y R.right) (y R.left) := by
  rw [isEmpty_iff_forall_notMem_cIoo, bottom_def, top_def, R.map_left, R.map_right]
  exact forall₂_congr fun c hc => by
    rw [R.map_of_ne c (Grid.ne_left_of_mem_cIoo hc) (Grid.ne_right_of_mem_cIoo hc)]

/-- A rectangle between states avoids markings exactly when neither marking set meets the
squares it covers. -/
theorem avoidsMarkings_iff (G : GridDiagram n) :
    R.AvoidsMarkings G ↔
      Disjoint R.toGridRectangle.coveredSquares G.OSet ∧
        Disjoint R.toGridRectangle.coveredSquares G.XSet :=
  R.toGridRectangle.avoidsMarkings_iff G

/-- A marking-avoiding rectangle between states covers no square carrying an `O` marking. -/
theorem disjoint_coveredSquares_OSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.toGridRectangle.coveredSquares G.OSet :=
  R.toGridRectangle.disjoint_coveredSquares_OSet_of_avoidsMarkings h

/-- A marking-avoiding rectangle between states covers no square carrying an `X` marking. -/
theorem disjoint_coveredSquares_XSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.toGridRectangle.coveredSquares G.XSet :=
  R.toGridRectangle.disjoint_coveredSquares_XSet_of_avoidsMarkings h

/-- The diagonal reflection of an oriented rectangle from `x` to `y`, an oriented rectangle from
`x.transpose` to `y.transpose`.

Reflecting across the main diagonal exchanges the side columns with the side rows: the new side
columns are the two rows `x R.left` and `x R.right` that `R` connects. -/
def transpose (R : GridRectangleBetween x y) :
    GridRectangleBetween x.transpose y.transpose where
  left := R.bottom
  right := R.top
  left_ne_right := R.bottom_ne_top
  map_left := by
    simp only [GridRectangleBetween.bottom, GridRectangleBetween.top]
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_eq]
    exact R.map_right.symm
  map_right := by
    simp only [GridRectangleBetween.bottom, GridRectangleBetween.top]
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_eq]
    exact R.map_left.symm
  map_of_ne c hl hr := by
    have hsymm : x (x.toPerm.symm c) = c := Equiv.apply_symm_apply _ _
    have hd_left : x.toPerm.symm c ≠ R.left := by
      intro h; rw [h] at hsymm; exact hl hsymm.symm
    have hd_right : x.toPerm.symm c ≠ R.right := by
      intro h; rw [h] at hsymm; exact hr hsymm.symm
    rw [GridState.transpose_apply, GridState.transpose_apply, Equiv.symm_apply_eq,
      R.map_of_ne _ hd_left hd_right]
    exact hsymm.symm

/-- The reflected rectangle's initial side column is the original initial side row. -/
@[simp]
theorem transpose_left (R : GridRectangleBetween x y) : R.transpose.left = R.bottom :=
  rfl

/-- The reflected rectangle's terminal side column is the original terminal side row. -/
@[simp]
theorem transpose_right (R : GridRectangleBetween x y) : R.transpose.right = R.top :=
  rfl

/-- The reflected rectangle's initial side row is the original initial side column. -/
@[simp]
theorem transpose_bottom (R : GridRectangleBetween x y) : R.transpose.bottom = R.left := by
  simp only [GridRectangleBetween.bottom, transpose_left, GridState.transpose_apply,
    Equiv.symm_apply_apply]

/-- The reflected rectangle's terminal side row is the original terminal side column. -/
@[simp]
theorem transpose_top (R : GridRectangleBetween x y) : R.transpose.top = R.right := by
  simp only [GridRectangleBetween.top, transpose_right, GridState.transpose_apply,
    Equiv.symm_apply_apply]

/-- The associated toroidal rectangle of the reflected oriented rectangle is the reflection of the
associated toroidal rectangle. -/
@[simp]
theorem transpose_toGridRectangle (R : GridRectangleBetween x y) :
    R.transpose.toGridRectangle = R.toGridRectangle.transpose := by
  ext <;> simp

end GridRectangleBetween

end TauCeti

end

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- The oriented rectangle from `x` to `y` obtained by exchanging the two side columns.

It connects the same two states `x` and `y` -- the two states still exchange rows at the two
side columns and agree elsewhere -- but runs along the complementary column arc and the
complementary row arc. Cutting the torus along the two side columns and the two side rows, `R` and
`R.swapSides` are diagonally opposite pieces; the other two pieces lie in neither. This is not the
opposite rectangle `symm`, which runs from `y` back to `x`. -/
def swapSides (R : GridRectangleBetween x y) : GridRectangleBetween x y where
  left := R.right
  right := R.left
  left_ne_right := R.left_ne_right.symm
  map_left := R.map_right
  map_right := R.map_left
  map_of_ne c hl hr := R.map_of_ne c hr hl

/-- The side-swapped rectangle's initial side column is the original terminal side column. -/
@[simp]
theorem swapSides_left (R : GridRectangleBetween x y) : R.swapSides.left = R.right :=
  (rfl)

/-- The side-swapped rectangle's terminal side column is the original initial side column. -/
@[simp]
theorem swapSides_right (R : GridRectangleBetween x y) : R.swapSides.right = R.left :=
  (rfl)

/-- The side-swapped rectangle's bottom row is the original top row. -/
@[simp]
theorem swapSides_bottom (R : GridRectangleBetween x y) : R.swapSides.bottom = R.top :=
  (rfl)

/-- The side-swapped rectangle's top row is the original bottom row. -/
@[simp]
theorem swapSides_top (R : GridRectangleBetween x y) : R.swapSides.top = R.bottom :=
  (rfl)

/-- The toroidal rectangle of the side-swapped oriented rectangle, written out by its four
sides. -/
@[simp]
theorem swapSides_toGridRectangle (R : GridRectangleBetween x y) :
    R.swapSides.toGridRectangle =
      { left := R.right, right := R.left, bottom := R.top, top := R.bottom } :=
  (rfl)

/-- Exchanging the two side columns twice gives the original rectangle. -/
@[simp]
theorem swapSides_swapSides (R : GridRectangleBetween x y) : R.swapSides.swapSides = R :=
  GridRectangleBetween.ext (swapSides_right R) (swapSides_left R)

/-- Exchanging the two side columns gives a genuinely different rectangle, since the two side
columns are distinct. -/
theorem swapSides_ne_self (R : GridRectangleBetween x y) : R.swapSides ≠ R := by
  intro h
  have hleft : R.swapSides.left = R.left := congrArg GridRectangleBetween.left h
  rw [swapSides_left] at hleft
  exact R.left_ne_right hleft.symm

end GridRectangleBetween

end TauCeti

end

@[expose] public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- Reflecting an oriented rectangle twice gives the original rectangle. -/
@[simp]
theorem transpose_transpose (R : GridRectangleBetween x y) : R.transpose.transpose = R :=
  GridRectangleBetween.ext (transpose_bottom R) (transpose_top R)

/-- The diagonal reflection as an equivalence between oriented rectangles from `x` to `y` and
oriented rectangles from `x.transpose` to `y.transpose`. Since reflecting twice is the identity,
`transpose` is its own inverse. -/
def transposeEquiv (x y : GridState n) :
    GridRectangleBetween x y ≃ GridRectangleBetween x.transpose y.transpose where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose

/-- The transpose equivalence applies a rectangle by reflecting it. -/
@[simp]
theorem transposeEquiv_apply (R : GridRectangleBetween x y) :
    transposeEquiv x y R = R.transpose :=
  rfl

/-- The inverse of the transpose equivalence is again reflection. -/
@[simp]
theorem transposeEquiv_symm_apply (R : GridRectangleBetween x.transpose y.transpose) :
    (transposeEquiv x y).symm R = R.transpose :=
  rfl

/-- The diagonal reflection is injective on oriented rectangles. -/
theorem transpose_injective :
    Function.Injective
      (transpose : GridRectangleBetween x y → GridRectangleBetween x.transpose y.transpose) :=
  (transposeEquiv x y).injective

/-- Two oriented rectangles have equal diagonal reflections exactly when they are equal. -/
@[simp]
theorem transpose_inj {R S : GridRectangleBetween x y} :
    R.transpose = S.transpose ↔ R = S :=
  (transposeEquiv x y).apply_eq_iff_eq

/-- The diagonal reflection preserves emptiness of a rectangle between grid states. -/
@[simp]
theorem isEmpty_transpose (R : GridRectangleBetween x y) :
    R.transpose.IsEmpty ↔ R.IsEmpty := by
  rw [isEmpty_iff_toGridRectangle_isEmptyFor, isEmpty_iff_toGridRectangle_isEmptyFor,
    transpose_toGridRectangle]
  exact R.toGridRectangle.isEmptyFor_transpose x

/-- The diagonal reflection preserves marking avoidance of a rectangle between grid states. -/
@[simp]
theorem avoidsMarkings_transpose (G : GridDiagram n) (R : GridRectangleBetween x y) :
    R.transpose.AvoidsMarkings G.transpose ↔ R.AvoidsMarkings G := by
  unfold GridRectangleBetween.AvoidsMarkings
  rw [transpose_toGridRectangle]
  exact R.toGridRectangle.avoidsMarkings_transpose G

/-- Swapping the `O` and `X` markings preserves marking avoidance of a rectangle between grid
states. -/
@[simp]
theorem avoidsMarkings_swapMarkings (G : GridDiagram n) (R : GridRectangleBetween x y) :
    R.AvoidsMarkings G.swapMarkings ↔ R.AvoidsMarkings G :=
  R.toGridRectangle.avoidsMarkings_swapMarkings G

end GridRectangleBetween

end TauCeti
