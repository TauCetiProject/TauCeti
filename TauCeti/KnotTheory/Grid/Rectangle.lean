/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import TauCeti.KnotTheory.Grid.CyclicInterval
import TauCeti.KnotTheory.Grid.Diagram

/-!
# Rectangles in grid diagrams

This file adds the first rectangle API for the grid-combinatorial lane of the Heegaard Floer
roadmap. The grid lives on a torus, so the basic one-dimensional ingredient is the open-open
circular interval in `Fin n`. A grid rectangle is then the product of two such intervals,
recorded as the finite set of squares in its interior.

The final section packages an oriented rectangle from one grid state to another: two columns
where the states exchange rows, and agreement everywhere else. This is the shape counted by
the grid differential; the `IsEmptyFor` and `AvoidsMarkings` predicates record the two
finite-set disjointness conditions used for empty rectangles and marking-avoiding rectangles.

## Main definitions

* `TauCeti.GridRectangle`: a toroidal rectangle, represented by its four cyclic sides.
* `TauCeti.GridRectangle.interior`: the finite set of squares strictly inside the rectangle.
* `TauCeti.GridRectangleBetween`: an oriented rectangle from one grid state to another.
* `TauCeti.GridRectangleBetween.all`: all oriented rectangles from `x` to `y`.
* `TauCeti.GridRectangleBetween.emptyRectangles`: the empty rectangles from `x` to `y`.

## References

This supplies a prerequisite for the Tau Ceti Heegaard Floer roadmap,
`HeegaardFloer/README.md` in TauCetiRoadmap, Lane G.1, "Grid diagrams and grid states",
specifically the next objects named there: rectangles and empty rectangles `Rect°(x, y)`.
The encoding follows the toroidal grid-diagram convention from Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 3.
-/

namespace TauCeti

/-- A toroidal grid rectangle, represented by its oriented column and row sides.

The interior is the product of the clockwise open interval from `left` to `right` with the
clockwise open interval from `bottom` to `top`. Degenerate side choices are allowed at this
level; their interiors are empty in the degenerate direction. -/
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
@[simp]
theorem left_notMem_columnInterior : R.left ∉ R.columnInterior := by
  simp [columnInterior]

/-- The right side is not an interior column. -/
@[simp]
theorem right_notMem_columnInterior : R.right ∉ R.columnInterior := by
  simp [columnInterior]

/-- The bottom side is not an interior row. -/
@[simp]
theorem bottom_notMem_rowInterior : R.bottom ∉ R.rowInterior := by
  simp [rowInterior]

/-- The top side is not an interior row. -/
@[simp]
theorem top_notMem_rowInterior : R.top ∉ R.rowInterior := by
  simp [rowInterior]

/-- The finite set of squares strictly inside a toroidal grid rectangle. -/
noncomputable def interior : Finset (Fin n × Fin n) :=
  R.columnInterior ×ˢ R.rowInterior

/-- Membership in a rectangle interior is membership in both one-dimensional open intervals. -/
@[simp]
theorem mem_interior (p : Fin n × Fin n) :
    p ∈ R.interior ↔ p.1 ∈ R.columnInterior ∧ p.2 ∈ R.rowInterior := by
  simp [interior]

/-- A coordinate pair lies in the rectangle interior exactly when its column and row lie in
the corresponding open cyclic intervals. -/
@[simp]
theorem mk_mem_interior (c r : Fin n) :
    (c, r) ∈ R.interior ↔ c ∈ R.columnInterior ∧ r ∈ R.rowInterior := by
  simp

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

/-- The number of interior squares is the product of the numbers of interior columns and
interior rows. -/
@[simp]
theorem card_interior :
    R.interior.card = R.columnInterior.card * R.rowInterior.card := by
  simp [interior, Finset.card_product]

/-- A rectangle is empty for a grid state when the state has no point in its interior. -/
def IsEmptyFor (x : GridState n) : Prop :=
  Disjoint R.interior x.pointSet

/-- A rectangle is empty for a grid state exactly when no point of the state lies in its
interior. -/
theorem isEmptyFor_iff (x : GridState n) :
    R.IsEmptyFor x ↔ ∀ p ∈ x.pointSet, p ∉ R.interior := by
  rw [IsEmptyFor, disjoint_comm, Finset.disjoint_iff_ne]
  constructor
  · intro h p hp hpR
    exact h p hp p hpR rfl
  · intro h p hp q hq hpq
    subst hpq
    exact h p hp hq

/-- A rectangle avoids the markings of a grid diagram when its interior contains no `O` or
`X` marking. -/
def AvoidsMarkings (G : GridDiagram n) : Prop :=
  Disjoint R.interior (G.OSet ∪ G.XSet)

/-- A marking-avoiding rectangle has no `O` marking in its interior. -/
theorem disjoint_interior_OSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.interior G.OSet :=
  h.mono_right Finset.subset_union_left

/-- A marking-avoiding rectangle has no `X` marking in its interior. -/
theorem disjoint_interior_XSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.interior G.XSet :=
  h.mono_right Finset.subset_union_right

/-- A rectangle avoids markings exactly when neither the `O` nor the `X` marking set meets
its interior. -/
theorem avoidsMarkings_iff (G : GridDiagram n) :
    R.AvoidsMarkings G ↔
      Disjoint R.interior G.OSet ∧ Disjoint R.interior G.XSet := by
  rw [AvoidsMarkings, Finset.disjoint_union_right]

end GridRectangle

/-- An oriented toroidal rectangle from one grid state to another.

The two states agree outside the two side columns, and in those side columns they exchange the
two rows. Swapping `left` and `right` gives the complementary oriented rectangle. -/
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

/-- A rectangle between two grid states is determined by its two side columns. -/
private theorem sidePair_injective :
    Function.Injective fun R : GridRectangleBetween x y => (R.left, R.right) := by
  intro R S h
  cases R
  cases S
  simp only at h
  obtain ⟨hleft, hright⟩ := Prod.ext_iff.mp h
  cases hleft
  cases hright
  rfl

/-- For fixed source and target grid states, the oriented rectangles between them form a
finite type. Each rectangle is determined by its two side columns. -/
noncomputable instance : Fintype (GridRectangleBetween x y) :=
  Fintype.ofInjective (fun R : GridRectangleBetween x y => (R.left, R.right))
    sidePair_injective

/-- The finite set of all oriented rectangles from `x` to `y`. -/
noncomputable def all (x y : GridState n) : Finset (GridRectangleBetween x y) := by
  classical
  exact Finset.univ

/-- Membership in `GridRectangleBetween.all` is automatic. -/
@[simp]
theorem mem_all (R : GridRectangleBetween x y) : R ∈ all x y := by
  classical
  simp [all]

variable (R : GridRectangleBetween x y)

/-- The row of `x` on the initial side. -/
def bottom : Fin n :=
  x R.left

/-- The row of `x` on the terminal side. -/
def top : Fin n :=
  x R.right

/-- The associated toroidal rectangle. -/
def toGridRectangle : GridRectangle n where
  left := R.left
  right := R.right
  bottom := R.bottom
  top := R.top

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
@[simp]
theorem all_self (x : GridState n) : all x x = ∅ := by
  classical
  ext R
  exact R.source_ne_target rfl |>.elim

/-- The initial lower corner is a point of the source state. -/
@[simp]
theorem left_bottom_mem_source : (R.left, R.bottom) ∈ x.pointSet := by
  simp [bottom]

/-- The terminal upper corner is a point of the source state. -/
@[simp]
theorem right_top_mem_source : (R.right, R.top) ∈ x.pointSet := by
  simp [top]

/-- The initial upper corner is a point of the target state. -/
@[simp]
theorem left_top_mem_target : (R.left, R.top) ∈ y.pointSet := by
  simp [top, R.map_left]

/-- The terminal lower corner is a point of the target state. -/
@[simp]
theorem right_bottom_mem_target : (R.right, R.bottom) ∈ y.pointSet := by
  simp [bottom, R.map_right]

/-- Away from the two side columns, membership in the source and target states is identical. -/
theorem mem_target_pointSet_iff_of_ne {p : Fin n × Fin n}
    (hleft : p.1 ≠ R.left) (hright : p.1 ≠ R.right) :
    p ∈ y.pointSet ↔ p ∈ x.pointSet := by
  simp [R.map_of_ne p.1 hleft hright]

/-- The associated rectangle is empty for the source state when no source-state point lies in
its interior. -/
def IsEmpty : Prop :=
  R.toGridRectangle.IsEmptyFor x

/-- The finite set of empty oriented rectangles from `x` to `y`. -/
noncomputable def emptyRectangles (x y : GridState n) : Finset (GridRectangleBetween x y) := by
  classical
  exact (all x y).filter fun R => R.IsEmpty

/-- Membership in the finite set of empty rectangles is exactly the emptiness predicate. -/
@[simp]
theorem mem_emptyRectangles (R : GridRectangleBetween x y) :
    R ∈ emptyRectangles x y ↔ R.IsEmpty := by
  classical
  simp [emptyRectangles]

/-- Every rectangle in `emptyRectangles` is empty. -/
theorem isEmpty_of_mem_emptyRectangles {R : GridRectangleBetween x y}
    (hR : R ∈ emptyRectangles x y) : R.IsEmpty :=
  (mem_emptyRectangles R).mp hR

/-- Empty rectangles are a subset of all rectangles between the same two states. -/
theorem emptyRectangles_subset_all (x y : GridState n) :
    emptyRectangles x y ⊆ all x y := by
  classical
  intro R hR
  simp [emptyRectangles] at hR ⊢

/-- There are no empty rectangles from a grid state to itself. -/
@[simp]
theorem emptyRectangles_self (x : GridState n) : emptyRectangles x x = ∅ := by
  classical
  simp [emptyRectangles]

/-- The associated rectangle avoids a grid diagram's markings when no marking lies in its
interior. -/
def AvoidsMarkings (G : GridDiagram n) : Prop :=
  R.toGridRectangle.AvoidsMarkings G

/-- The source state has no point in the interior of an empty rectangle between states. -/
theorem not_mem_interior_of_isEmpty (h : R.IsEmpty) {p : Fin n × Fin n}
    (hp : p ∈ x.pointSet) : p ∉ R.toGridRectangle.interior :=
  (R.toGridRectangle.isEmptyFor_iff x).mp h p hp

/-- A rectangle between states is empty exactly when no source-state point lies in its
interior. -/
theorem isEmpty_iff :
    R.IsEmpty ↔ ∀ p ∈ x.pointSet, p ∉ R.toGridRectangle.interior :=
  R.toGridRectangle.isEmptyFor_iff x

/-- If a target-state point lies on a side column, then it is not in the associated
rectangle's interior. -/
theorem not_mem_interior_of_fst_eq_left {p : Fin n × Fin n} (hp : p.1 = R.left) :
    p ∉ R.toGridRectangle.interior := by
  intro hpR
  have hpcol := (R.toGridRectangle.mem_interior p).mp hpR |>.1
  rw [hp] at hpcol
  exact R.toGridRectangle.left_notMem_columnInterior hpcol

/-- If a target-state point lies on the other side column, then it is not in the associated
rectangle's interior. -/
theorem not_mem_interior_of_fst_eq_right {p : Fin n × Fin n} (hp : p.1 = R.right) :
    p ∉ R.toGridRectangle.interior := by
  intro hpR
  have hpcol := (R.toGridRectangle.mem_interior p).mp hpR |>.1
  rw [hp] at hpcol
  exact R.toGridRectangle.right_notMem_columnInterior hpcol

/-- A rectangle between states is empty exactly when no target-state point lies in its
interior. -/
theorem isEmpty_iff_target :
    R.IsEmpty ↔ ∀ p ∈ y.pointSet, p ∉ R.toGridRectangle.interior := by
  rw [isEmpty_iff]
  constructor
  · intro h p hp
    by_cases hleft : p.1 = R.left
    · exact R.not_mem_interior_of_fst_eq_left hleft
    by_cases hright : p.1 = R.right
    · exact R.not_mem_interior_of_fst_eq_right hright
    exact h p ((R.mem_target_pointSet_iff_of_ne hleft hright).mp hp)
  · intro h p hp hpR
    have hleft : p.1 ≠ R.left := by
      intro hcol
      exact R.not_mem_interior_of_fst_eq_left hcol hpR
    have hright : p.1 ≠ R.right := by
      intro hcol
      exact R.not_mem_interior_of_fst_eq_right hcol hpR
    exact h p ((R.mem_target_pointSet_iff_of_ne hleft hright).mpr hp) hpR

/-- The target state has no point in the interior of an empty rectangle between states. -/
theorem not_mem_interior_target_of_isEmpty (h : R.IsEmpty) {p : Fin n × Fin n}
    (hp : p ∈ y.pointSet) : p ∉ R.toGridRectangle.interior :=
  (R.isEmpty_iff_target).mp h p hp

/-- A rectangle between states avoids markings exactly when neither marking set meets its
interior. -/
theorem avoidsMarkings_iff (G : GridDiagram n) :
    R.AvoidsMarkings G ↔
      Disjoint R.toGridRectangle.interior G.OSet ∧
        Disjoint R.toGridRectangle.interior G.XSet :=
  R.toGridRectangle.avoidsMarkings_iff G

/-- A marking-avoiding rectangle between states has no `O` marking in its interior. -/
theorem disjoint_interior_OSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.toGridRectangle.interior G.OSet :=
  R.toGridRectangle.disjoint_interior_OSet_of_avoidsMarkings h

/-- A marking-avoiding rectangle between states has no `X` marking in its interior. -/
theorem disjoint_interior_XSet_of_avoidsMarkings {G : GridDiagram n}
    (h : R.AvoidsMarkings G) : Disjoint R.toGridRectangle.interior G.XSet :=
  R.toGridRectangle.disjoint_interior_XSet_of_avoidsMarkings h

end GridRectangleBetween

end TauCeti
