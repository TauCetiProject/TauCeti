/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.DifferentialSupportCardinality
import Mathlib.Tactic
import TauCeti.KnotTheory.Grid.RectangleCount

/-!
# The fully blocked grid differential on grids of size at most two

This file records the first small-grid computation for the fully blocked grid differential.
In an `n × n` grid with `n ≤ 2`, every open cyclic interval in `Fin n` is empty. Consequently
every toroidal rectangle has empty interior, so every oriented rectangle is empty and avoids all
markings. Between two distinct grid states the two oriented rectangles therefore both contribute
to the fully blocked count, and their total is zero in `ZMod 2`; between a state and itself there
are no rectangles. Thus the whole fully blocked differential vanishes.

The cases `n = 0` and `n = 1` already follow from the column-swap support bound. The new content
here is the size-two cancellation, which is the first nontrivial sanity check for the rectangle
count defining the fully blocked grid complex.

## Main results

* `TauCeti.Grid.cIoo_eq_empty_of_le_two`: open cyclic intervals in grids of size at most two
  are empty.
* `TauCeti.GridDiagram.fullyBlockedRectangleCount_eq_zero_of_le_two`: every fully blocked
  rectangle coefficient vanishes in grid size at most two.
* `TauCeti.GridDiagram.fullyBlockedDifferential_eq_zero_of_le_two`: the fully blocked
  differential is the zero linear map in grid size at most two.
* `TauCeti.GridDiagram.fullyBlockedDifferential_eq_zero_of_two`: the explicit `2 × 2` form.

## References

This supplies a prerequisite for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`",
and for the standing convention that the grid complexes compute on explicit small grids. The
rectangle-count convention follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and
Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace Grid

variable {n : ℕ}

/-- In a grid of size at most two, every open cyclic interval is empty. There are no grid points
strictly between two endpoints on either of the two complementary arcs. -/
theorem cIoo_eq_empty_of_le_two (hn : n ≤ 2) (a b : Fin n) : cIoo a b = ∅ := by
  by_cases hab : a = b
  · simp [hab]
  · apply Finset.card_eq_zero.mp
    have hsum := card_cIoo_add_card_cIoo_swap hab
    have hcard : (cIoo a b).card = 0 := by omega
    exact hcard

end Grid

namespace GridRectangle

variable {n : ℕ}

/-- In a grid of size at most two, every toroidal rectangle has empty interior. -/
theorem interior_eq_empty_of_le_two (hn : n ≤ 2) (R : GridRectangle n) : R.interior = ∅ := by
  ext p
  simp [interior, columnInterior, Grid.cIoo_eq_empty_of_le_two hn R.left R.right]

/-- In a grid of size at most two, every toroidal rectangle is empty for every grid state. -/
theorem isEmptyFor_of_le_two (hn : n ≤ 2) (R : GridRectangle n) (x : GridState n) :
    R.IsEmptyFor x := by
  rw [IsEmptyFor, R.interior_eq_empty_of_le_two hn]
  simp

/-- In a grid of size at most two, every toroidal rectangle avoids every diagram's markings. -/
theorem avoidsMarkings_of_le_two (hn : n ≤ 2) (R : GridRectangle n) (G : GridDiagram n) :
    R.AvoidsMarkings G := by
  rw [AvoidsMarkings, R.interior_eq_empty_of_le_two hn]
  simp

end GridRectangle

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n}

/-- In grid size at most two, every oriented rectangle between grid states is empty. -/
theorem isEmpty_of_le_two (hn : n ≤ 2) (R : GridRectangleBetween x y) : R.IsEmpty :=
  R.toGridRectangle.isEmptyFor_of_le_two hn x

/-- In grid size at most two, the empty rectangles are all oriented rectangles. -/
theorem emptyRectangles_eq_all_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    emptyRectangles x y = all x y := by
  ext R
  simp [isEmpty_of_le_two hn R]

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- In grid size at most two, the fully blocked rectangles are exactly all oriented rectangles:
all rectangle interiors are empty, so emptiness and marking avoidance impose no extra condition. -/
theorem fullyBlockedRectangles_eq_all_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    G.fullyBlockedRectangles x y = GridRectangleBetween.all x y := by
  ext R
  rw [mem_fullyBlockedRectangles]
  constructor
  · intro _
    exact GridRectangleBetween.mem_all R
  · intro _
    exact ⟨GridRectangleBetween.isEmpty_of_le_two hn R,
      R.toGridRectangle.avoidsMarkings_of_le_two hn G⟩

/-- Every fully blocked rectangle coefficient vanishes in grid size at most two. If there are no
rectangles the count is zero; otherwise there are exactly two oriented rectangles, which cancel
over `ZMod 2`. -/
theorem fullyBlockedRectangleCount_eq_zero_of_le_two (hn : n ≤ 2) (x y : GridState n) :
    G.fullyBlockedRectangleCount x y = 0 := by
  rw [fullyBlockedRectangleCount_def, G.fullyBlockedRectangles_eq_all_of_le_two hn]
  rcases (GridRectangleBetween.all x y).eq_empty_or_nonempty with h | h
  · simp [h]
  · rw [GridRectangleBetween.card_all_eq_two_of_nonempty h]
    exact ZMod.natCast_self 2

/-- The fully blocked differential of one generator vanishes in grid size at most two. -/
theorem fullyBlockedDifferentialOnGenerator_eq_zero_of_le_two
    (hn : n ≤ 2) (x : GridState n) :
    G.fullyBlockedDifferentialOnGenerator x = 0 := by
  ext y
  simp [fullyBlockedRectangleCount_eq_zero_of_le_two G hn x y]

/-- The fully blocked differential is zero on every chain in grid size at most two. -/
theorem fullyBlockedDifferential_eq_zero_of_le_two (hn : n ≤ 2) :
    G.fullyBlockedDifferential = (0 : GridChain (ZMod 2) n →ₗ[ZMod 2] GridChain (ZMod 2) n) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  simp [fullyBlockedDifferentialOnGenerator_eq_zero_of_le_two G hn x]

/-- The fully blocked differential is zero on every `2 × 2` grid. This is the first
nontrivial cancellation sanity check for the rectangle-count definition. -/
theorem fullyBlockedDifferential_eq_zero_of_two (G : GridDiagram 2) :
    G.fullyBlockedDifferential =
      (0 : GridChain (ZMod 2) 2 →ₗ[ZMod 2] GridChain (ZMod 2) 2) :=
  G.fullyBlockedDifferential_eq_zero_of_le_two le_rfl

end GridDiagram

end TauCeti
