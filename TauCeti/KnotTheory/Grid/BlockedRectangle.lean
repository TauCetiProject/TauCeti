/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import TauCeti.KnotTheory.Grid.Rectangle

/-!
# Fully blocked empty rectangles in grid diagrams

This file packages the finite rectangle counts used by the fully blocked grid differential.
For grid states `x` and `y`, the already-defined `GridRectangleBetween x y` records an
oriented toroidal rectangle from `x` to `y`. Here we collect these rectangles into finite
sets, filter to empty rectangles, then filter further to rectangles whose interiors avoid all
`O` and `X` markings of a grid diagram.

The final count is valued in `ZMod 2`, matching the first coefficient system used in the grid
homology roadmap.

## Main definitions

* `TauCeti.GridRectangleBetween.all`: all oriented rectangles from `x` to `y`.
* `TauCeti.GridRectangleBetween.emptyRectangles`: the empty rectangles from `x` to `y`.
* `TauCeti.GridDiagram.fullyBlockedRectangles`: empty rectangles avoiding all markings.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount`: the corresponding count in `ZMod 2`.

## References

This supplies a prerequisite for the Tau Ceti Heegaard Floer roadmap,
`HeegaardFloer/README.md` in TauCetiRoadmap, Lane G.3, "The complexes and `∂² = 0`",
where the fully blocked grid complex over `𝔽₂` counts rectangles avoiding all markings. The
objects and terminology follow Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3.
-/

namespace TauCeti

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

noncomputable instance : Fintype (GridRectangleBetween x y) :=
  Fintype.ofInjective (fun R : GridRectangleBetween x y => (R.left, R.right))
    sidePair_injective

/-- There is no rectangle from a grid state to itself. A rectangle would have to swap the two
distinct side columns, forcing the state's permutation to take the same value on both. -/
theorem false_of_source_eq_target (R : GridRectangleBetween x x) : False := by
  exact R.left_ne_right (x.toPerm.injective (by simpa [bottom, top] using R.map_left))

/-- The finite set of all oriented rectangles from `x` to `y`. -/
noncomputable def all (x y : GridState n) : Finset (GridRectangleBetween x y) := by
  classical
  exact Finset.univ

/-- Membership in `GridRectangleBetween.all` is automatic. -/
@[simp]
theorem mem_all (R : GridRectangleBetween x y) : R ∈ all x y := by
  classical
  simp [all]

/-- There are no rectangles from a grid state to itself. -/
@[simp]
theorem all_self (x : GridState n) : all x x = ∅ := by
  classical
  ext R
  exact false_of_source_eq_target R |>.elim

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

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (x y : GridState n)

/-- The finite set of fully blocked empty rectangles from `x` to `y` in a grid diagram.

"Fully blocked" means that the rectangle is empty for the source grid state and its interior
avoids every `O` and `X` marking. This is the rectangle set whose parity gives the coefficient
of `y` in the fully blocked grid differential applied to `x`. -/
noncomputable def fullyBlockedRectangles : Finset (GridRectangleBetween x y) := by
  classical
  exact (GridRectangleBetween.emptyRectangles x y).filter fun R => R.AvoidsMarkings G

/-- Membership in the fully blocked rectangle set is emptiness together with marking
avoidance. -/
@[simp]
theorem mem_fullyBlockedRectangles (R : GridRectangleBetween x y) :
    R ∈ G.fullyBlockedRectangles x y ↔ R.IsEmpty ∧ R.AvoidsMarkings G := by
  classical
  simp [fullyBlockedRectangles]

/-- Every fully blocked rectangle is empty. -/
theorem isEmpty_of_mem_fullyBlockedRectangles {R : GridRectangleBetween x y}
    (hR : R ∈ G.fullyBlockedRectangles x y) : R.IsEmpty :=
  (G.mem_fullyBlockedRectangles x y R).mp hR |>.1

/-- Every fully blocked rectangle avoids the `O` and `X` markings. -/
theorem avoidsMarkings_of_mem_fullyBlockedRectangles {R : GridRectangleBetween x y}
    (hR : R ∈ G.fullyBlockedRectangles x y) : R.AvoidsMarkings G :=
  (G.mem_fullyBlockedRectangles x y R).mp hR |>.2

/-- Fully blocked rectangles are a subset of the empty rectangles between the same states. -/
theorem fullyBlockedRectangles_subset_emptyRectangles :
    G.fullyBlockedRectangles x y ⊆ GridRectangleBetween.emptyRectangles x y := by
  classical
  intro R hR
  exact (GridRectangleBetween.mem_emptyRectangles R).mpr
    ((G.mem_fullyBlockedRectangles x y R).mp hR |>.1)

/-- Fully blocked rectangles are a subset of all rectangles between the same states. -/
theorem fullyBlockedRectangles_subset_all :
    G.fullyBlockedRectangles x y ⊆ GridRectangleBetween.all x y :=
  G.fullyBlockedRectangles_subset_emptyRectangles x y |>.trans
    (GridRectangleBetween.emptyRectangles_subset_all x y)

/-- A fully blocked rectangle has no source-state point in its interior. -/
theorem not_mem_interior_source_of_mem_fullyBlockedRectangles
    {R : GridRectangleBetween x y} (hR : R ∈ G.fullyBlockedRectangles x y)
    {p : Fin n × Fin n} (hp : p ∈ x.pointSet) : p ∉ R.toGridRectangle.interior :=
  R.not_mem_interior_of_isEmpty (G.isEmpty_of_mem_fullyBlockedRectangles x y hR) hp

/-- A fully blocked rectangle has no target-state point in its interior. -/
theorem not_mem_interior_target_of_mem_fullyBlockedRectangles
    {R : GridRectangleBetween x y} (hR : R ∈ G.fullyBlockedRectangles x y)
    {p : Fin n × Fin n} (hp : p ∈ y.pointSet) : p ∉ R.toGridRectangle.interior :=
  R.not_mem_interior_target_of_isEmpty (G.isEmpty_of_mem_fullyBlockedRectangles x y hR) hp

/-- A fully blocked rectangle has no `O` marking in its interior. -/
theorem disjoint_interior_OSet_of_mem_fullyBlockedRectangles
    {R : GridRectangleBetween x y} (hR : R ∈ G.fullyBlockedRectangles x y) :
    Disjoint R.toGridRectangle.interior G.OSet :=
  R.disjoint_interior_OSet_of_avoidsMarkings
    (G.avoidsMarkings_of_mem_fullyBlockedRectangles x y hR)

/-- A fully blocked rectangle has no `X` marking in its interior. -/
theorem disjoint_interior_XSet_of_mem_fullyBlockedRectangles
    {R : GridRectangleBetween x y} (hR : R ∈ G.fullyBlockedRectangles x y) :
    Disjoint R.toGridRectangle.interior G.XSet :=
  R.disjoint_interior_XSet_of_avoidsMarkings
    (G.avoidsMarkings_of_mem_fullyBlockedRectangles x y hR)

/-- The number of fully blocked empty rectangles from `x` to `y`, reduced modulo `2`. -/
noncomputable def fullyBlockedRectangleCount : ZMod 2 :=
  (G.fullyBlockedRectangles x y).card

/-- The fully blocked rectangle count is the cardinality of `fullyBlockedRectangles`, coerced
to `ZMod 2`. -/
theorem fullyBlockedRectangleCount_def :
    G.fullyBlockedRectangleCount x y = ((G.fullyBlockedRectangles x y).card : ZMod 2) :=
  rfl

/-- The set of fully blocked rectangles from a grid state to itself is empty. -/
@[simp]
theorem fullyBlockedRectangles_self (x : GridState n) : G.fullyBlockedRectangles x x = ∅ := by
  classical
  simp [fullyBlockedRectangles]

/-- The fully blocked rectangle count from a grid state to itself is zero. -/
@[simp]
theorem fullyBlockedRectangleCount_self (x : GridState n) :
    G.fullyBlockedRectangleCount x x = 0 := by
  simp [fullyBlockedRectangleCount]

end GridDiagram

end TauCeti
