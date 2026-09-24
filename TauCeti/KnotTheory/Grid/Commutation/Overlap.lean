/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Pairing

/-!
# Overlapping domains in the grid commutation map

The chain-map equation for a column commutation pairs a rectangle followed by a pentagon with a
pentagon followed by a rectangle. When the two domains share exactly one vertical side, forgetting
the pentagon's turn point produces the same L-shaped rectangle domain that occurs in the proof
that the grid differential squares to zero. This file begins transporting that generic recut back
to the commutation setting.

When the rectangle and pentagon share their initial side, the generic recut has its first
rectangle terminate on the replaced grid line. The cyclic row order forced by emptiness also
shows that this new terminal side still contains the original turn point. Thus the first recut
rectangle canonically promotes to a pentagon, producing a pentagon--rectangle decomposition.
Forgetting the turn point recovers exactly the generic recut, so its emptiness and covered-square
repartition data remain available without duplicating the rectangle geometry.

This module treats the common-initial-side orientation and preserves the underlying rectangle
repartition and its rectangle weights. It also records the two possible cuts in the
common-terminal-side orientation. In that orientation exactly one recut rectangle ends on the
replaced grid line; which one it is is part of the finite geometry, and later turn-row transports
must distinguish the two cases.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.recutLeftEqLeft`: promote the one-common-side
  rectangle recut to a pentagon--rectangle decomposition when the common side is initial for both
  original domains.
* `TauCeti.GridRectanglePentagonDecomposition.recutLeftEqLeft_toRectangleDecomposition`:
  forgetting the promoted turn point gives the generic recut.
* `TauCeti.GridRectanglePentagonDecomposition.isRecut_recutLeftEqLeft`: the promoted
  decomposition retains the generic recut relation, including its covered-square repartition.
* `TauCeti.GridRectanglePentagonDecomposition.OMonomial_mul_OMonomial_recutLeftEqLeft`: the
  product of the two underlying rectangle weights is preserved.
* `TauCeti.GridRectanglePentagonDecomposition.isRecutOfRightEqRight_recut`: the generic recut
  has the common-terminal-side orientation when the original rectangle and pentagon do.
* `TauCeti.GridRectanglePentagonDecomposition.recut_first_or_second_right_eq_pentagon_right`:
  exactly one of the two new rectangles has the original pentagon's terminal side.

## References

These are two overlap orientations in the pentagon--rectangle juxtaposition argument of
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

private theorem right_ne_right_of_left_eq_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide) :
    D.toRectangleDecomposition.first.right ≠ D.toRectangleDecomposition.second.right := by
  have hcommon' : D.toRectangleDecomposition.first.left =
      D.toRectangleDecomposition.second.left := by
    simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left] using
      hcommon
  intro hright
  apply D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hone
  rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon', hright]

/-- Emptiness of the two typed domains remains emptiness after forgetting the pentagon turn row. -/
private theorem isRecutOfLeftEqLeft_recut
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.IsRecutOfLeftEqLeft
      (D.toRectangleDecomposition.recut hone
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)) := by
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  have hcommon' : D.toRectangleDecomposition.first.left =
      D.toRectangleDecomposition.second.left := by
    simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left] using
      hcommon
  have hright := D.right_ne_right_of_left_eq_left hcommon hone
  have hrecut := D.toRectangleDecomposition.isRecut_recut hone hempty.1 hempty.2
  rcases hrecut.orientation with hdata | hdata | hdata | hdata
  · exact hdata
  · exact (hright hdata.side_eq).elim
  · exact (D.toRectangleDecomposition.second.left_ne_right
      (hcommon'.symm.trans hdata.side_eq)).elim
  · exact (D.toRectangleDecomposition.first.left_ne_right
      (hcommon'.trans hdata.side_eq.symm)).elim

/-- In the common-initial-side overlap, the first rectangle of the recut terminates on the
replaced grid line and hence has the required terminal side of a commutation pentagon. -/
theorem recut_first_right_of_left_eq_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    ((D.toRectangleDecomposition.recut hone
      (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).first).right =
        finRotate n a := by
  have hdata := D.isRecutOfLeftEqLeft_recut hcommon hone hrectangle hpentagon
  calc
    _ = D.toRectangleDecomposition.second.right := hdata.recut_sides.1
    _ = D.pentagon.right := toRectangleDecomposition_second_right D
    _ = finRotate n a := D.pentagon.right_eq

/-- In the common-initial-side overlap, the first rectangle of the recut still contains the
pentagon's turn row on its terminal side. -/
theorem turn_mem_recut_first_of_left_eq_left
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    s ∈ Grid.cIco
      (D.toRectangleDecomposition.recut hone
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).first.bottom
      (D.toRectangleDecomposition.recut hone
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).first.top := by
  -- Work in the forgotten rectangle decomposition to use its emptiness and cyclic-order facts.
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  have hcommon' : D.toRectangleDecomposition.first.left =
      D.toRectangleDecomposition.second.left := by
    simpa only [toRectangleDecomposition_first_left, toRectangleDecomposition_second_left] using
      hcommon
  have hright := D.right_ne_right_of_left_eq_left hcommon hone
  have hrow := (D.toRectangleDecomposition.cyclicOrder_of_isEmpty_of_left_eq_left
    hcommon' hright hempty.1 hempty.2).2
  -- Convert the cyclic row order and pentagon turn interval to the original corner rows.
  have hfirstBottom : D.toRectangleDecomposition.first.bottom =
      x D.toRectangleDecomposition.first.left :=
    D.toRectangleDecomposition.first.bottom_def
  have hfirstTop : D.toRectangleDecomposition.first.top =
      x D.toRectangleDecomposition.first.right :=
    D.toRectangleDecomposition.first.top_def
  have hsecondBottom : D.toRectangleDecomposition.second.bottom =
      x D.toRectangleDecomposition.first.right := by
    rw [GridRectangleBetween.bottom_def, ← hcommon',
      D.toRectangleDecomposition.first.map_left]
  have hsecondRight_ne_firstLeft : D.toRectangleDecomposition.second.right ≠
      D.toRectangleDecomposition.first.left := by
    intro h
    exact D.toRectangleDecomposition.second.left_ne_right
      (hcommon'.symm.trans h.symm)
  have hsecondTop : D.toRectangleDecomposition.second.top =
      x D.toRectangleDecomposition.second.right := by
    rw [GridRectangleBetween.top_def]
    exact D.toRectangleDecomposition.first.map_of_ne _ hsecondRight_ne_firstLeft hright.symm
  have hturn : s ∈ Grid.cIco D.toRectangleDecomposition.second.bottom
      D.toRectangleDecomposition.second.top := by
    simpa only [toRectangleDecomposition_middle, GridRectangleBetween.bottom_def,
      GridRectangleBetween.top_def,
      toRectangleDecomposition_second_left, toRectangleDecomposition_second_right] using
      D.pentagon.turn_mem
  have hdata := D.isRecutOfLeftEqLeft_recut hcommon hone hrectangle hpentagon
  -- The first recut branch preserves the full interval; the second splits it at the middle row.
  have hrecutRight := hdata.recut_sides.1
  have hbranch := hdata.recut_branch
  rcases hbranch with ⟨-, -, hrecutLeft, -⟩ | ⟨-, -, hrecutLeft, -⟩
  · rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hrecutLeft,
      hrecutRight, ← hsecondBottom, ← hsecondTop]
    exact hturn
  · have hrow' : x D.toRectangleDecomposition.first.right ∈
        Grid.cIoo (x D.toRectangleDecomposition.first.left)
          (x D.toRectangleDecomposition.second.right) := by
      simpa only [hfirstBottom, hfirstTop, hsecondTop] using hrow
    have hturn' : s ∈ Grid.cIco (x D.toRectangleDecomposition.first.right)
        (x D.toRectangleDecomposition.second.right) := by
      simpa only [hsecondBottom, hsecondTop] using hturn
    rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hrecutLeft,
      hrecutRight, ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow']
    exact Finset.mem_union.mpr (Or.inr hturn')

/-- Recut a rectangle followed by a pentagon when their unique common side is initial for both,
then promote the first new rectangle to a pentagon using the transported turn point. -/
noncomputable def recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    GridPentagonRectangleDecomposition a s x z := by
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  let E := D.toRectangleDecomposition.recut hone hempty.1 hempty.2
  exact {
    middle := E.middle
    pentagon := GridPentagonBetween.ofRightEq E.first
      (D.recut_first_right_of_left_eq_left hcommon hone hrectangle hpentagon)
      (D.turn_mem_recut_first_of_left_eq_left hcommon hone hrectangle hpentagon)
    rectangle := E.second }

/-- Forgetting the turn point after the common-initial-side overlap construction recovers the
generic one-common-side rectangle recut. -/
@[simp]
theorem recutLeftEqLeft_toRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).toRectangleDecomposition =
      D.toRectangleDecomposition.recut hone
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon) := by
  have hempty : D.toRectangleDecomposition.first.IsEmpty ∧
      D.toRectangleDecomposition.second.IsEmpty :=
    ⟨by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle,
      by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon⟩
  let E := D.toRectangleDecomposition.recut hone hempty.1 hempty.2
  have hpentagon := GridPentagonBetween.ofRightEq_toGridRectangleBetween E.first
    (D.recut_first_right_of_left_eq_left hcommon hone hrectangle hpentagon)
    (D.turn_mem_recut_first_of_left_eq_left hcommon hone hrectangle hpentagon)
  apply GridRectangleDecomposition.ext
  · simpa only [recutLeftEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_left, E] using
        congrArg GridRectangleBetween.left hpentagon
  · simpa only [recutLeftEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_first_right, E] using
        congrArg GridRectangleBetween.right hpentagon
  · simp only [recutLeftEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_left]
  · simp only [recutLeftEqLeft,
      GridPentagonRectangleDecomposition.toRectangleDecomposition_second_right]

/-- The promoted pentagon--rectangle decomposition carries the generic recut relation. In
particular, the two new underlying rectangles are empty and repartition the same covered squares
as the original rectangle and underlying rectangle of the pentagon. -/
theorem isRecut_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.IsRecut
      (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).toRectangleDecomposition := by
  rw [D.recutLeftEqLeft_toRectangleDecomposition hcommon hone hrectangle hpentagon]
  exact D.toRectangleDecomposition.isRecut_recut hone
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)

/-- The promoted pentagon in the overlap recut is empty. -/
@[simp]
theorem isEmpty_pentagon_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.IsEmpty := by
  simpa only [recutLeftEqLeft, GridPentagonBetween.ofRightEq_toGridRectangleBetween] using
    (D.toRectangleDecomposition.isRecut_recut hone
      (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).isEmpty_first

/-- The rectangle in the overlap recut is empty. -/
@[simp]
theorem isEmpty_rectangle_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).rectangle.IsEmpty := by
  simpa only [recutLeftEqLeft] using
    (D.toRectangleDecomposition.isRecut_recut hone
      (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)).isEmpty_second

/-- The underlying rectangles of the promoted overlap recut cover the same squares as the
original rectangle and the rectangle underlying the original pentagon. -/
theorem coveredSquares_union_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    (D.recutLeftEqLeft hcommon hone hrectangle
          hpentagon).pentagon.toGridRectangle.coveredSquares ∪
    (D.recutLeftEqLeft hcommon hone hrectangle
          hpentagon).rectangle.toGridRectangle.coveredSquares =
      D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.toGridRectangle.coveredSquares := by
  have h := (D.isRecut_recutLeftEqLeft hcommon hone hrectangle
    hpentagon).isRepartition.coveredSquares_union_eq
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using h

/-- The promoted overlap recut preserves the product of the `O`-monomials of its two underlying
rectangles. This is the rectangle-weight consequence of the generic covered-square repartition;
the correction from an underlying rectangle to the commutation pentagon weight is separate. -/
theorem OMonomial_mul_OMonomial_recutLeftEqLeft
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (G : GridDiagram n) (R : Type*) [CommSemiring R] :
    G.OMonomial R
          (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).pentagon.toGridRectangle *
        G.OMonomial R
          (D.recutLeftEqLeft hcommon hone hrectangle hpentagon).rectangle.toGridRectangle =
      G.OMonomial R D.rectangle.toGridRectangle *
        G.OMonomial R D.pentagon.toGridRectangle := by
  have h := (D.isRecut_recutLeftEqLeft hcommon hone hrectangle
    hpentagon).isRepartition.OMonomial_mul_OMonomial G R
  simpa only [GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridRectanglePentagonDecomposition.toRectangleDecomposition_second_toGridRectangle] using h

end GridRectanglePentagonDecomposition

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The generic recut retains the common-terminal-side orientation when the rectangle and
pentagon of a rectangle--pentagon decomposition share their terminal side. -/
theorem isRecutOfRightEqRight_recut
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.IsRecutOfRightEqRight
      (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)) := by
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  exact D.toRectangleDecomposition.isRecutOfRightEqRight_recut hcommon' hone
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)

/-- In a common-terminal-side overlap, the generic recut places the terminal side of the
original pentagon on one of its two new rectangles. The alternatives are disjoint because those
rectangles have different terminal sides. -/
theorem recut_first_or_second_right_eq_pentagon_right
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty) :
    let E := D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)
    (E.first.right = D.pentagon.right ∧ E.second.right ≠ D.pentagon.right) ∨
      (E.first.right ≠ D.pentagon.right ∧ E.second.right = D.pentagon.right) := by
  let E := D.toRectangleDecomposition.recut hone
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
    (by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        D.toRectangleDecomposition_middle,
        D.toRectangleDecomposition_second_toGridRectangle] using hpentagon)
  dsimp only
  have hcommon' : D.toRectangleDecomposition.first.right =
      D.toRectangleDecomposition.second.right := by
    simpa only [toRectangleDecomposition_first_right,
      toRectangleDecomposition_second_right] using hcommon
  have hdata := D.isRecutOfRightEqRight_recut hcommon hone hrectangle hpentagon
  have hbranches :
      (E.first.right = D.toRectangleDecomposition.second.right ∧
        E.second.right ≠ D.toRectangleDecomposition.second.right) ∨
        (E.first.right ≠ D.toRectangleDecomposition.second.right ∧
          E.second.right = D.toRectangleDecomposition.second.right) := by
    rcases hdata.recut_branch with ⟨-, -, hfirst, hsecond⟩ | ⟨-, -, hfirst, hsecond⟩
    · right
      refine ⟨?_, hsecond.trans hcommon'⟩
      intro h
      rw [hfirst, ← hcommon'] at h
      exact D.toRectangleDecomposition.first.left_ne_right h
    · left
      refine ⟨hfirst.trans hcommon', ?_⟩
      intro h
      rw [hsecond] at h
      exact D.toRectangleDecomposition.second.left_ne_right h
  simpa only [D.toRectangleDecomposition_second_right] using hbranches

end GridRectanglePentagonDecomposition

end TauCeti
