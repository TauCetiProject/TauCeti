/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap

/-!
# Terminal-side overlap promotion for the grid commutation map

This file constructs the pentagon--rectangle (and rectangle--pentagon) promotions for the
common-terminal-side overlap orientation, complementing the common-initial-side promotion
`TauCeti.GridRectanglePentagonDecomposition.recutLeftEqLeft` in
`TauCeti.KnotTheory.Grid.Commutation.Overlap`.

When the rectangle and pentagon share their terminal side, the generic recut places the
original pentagon's terminal side on exactly one of its two new rectangles
(`recut_first_or_second_right_eq_pentagon_right`). Whichever rectangle inherits that side
promotes to a pentagon via `GridPentagonBetween.ofRightEq`, once the turn row is transported
to its row interval.

The two subcases give different decomposition shapes:
* if the first recut rectangle inherits the terminal side, promoting it yields a
  pentagon--rectangle decomposition (`recutRightEqRight_first`);
* if the second recut rectangle inherits the terminal side, promoting it yields a
  rectangle--pentagon decomposition (`recutRightEqRight_second`).

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRight_first`: promote the
  terminal-side recut to a pentagon--rectangle decomposition when the first new rectangle
  carries the original pentagon's terminal side.
* `TauCeti.GridRectanglePentagonDecomposition.recutRightEqRight_second`: promote the
  terminal-side recut to a rectangle--pentagon decomposition when the second new rectangle
  carries the original pentagon's terminal side.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Recut a rectangle followed by a pentagon when their unique common side is terminal for
both, then promote the first new rectangle to a pentagon. This applies when the first recut
rectangle inherits the original pentagon's terminal side; the turn-row membership is supplied
as a hypothesis. -/
noncomputable def recutRightEqRight_first
    (D : GridRectanglePentagonDecomposition a s x z)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).first.right = D.pentagon.right)
    (hturn : s ∈ Grid.cIco (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).first.bottom
      (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).first.top) :
    GridPentagonRectangleDecomposition a s x z :=
  { middle := (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).middle
    pentagon := GridPentagonBetween.ofRightEq
      (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).first
      (hfirst.trans D.pentagon.right_eq)
      hturn
    rectangle := (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).second }

/-- Recut a rectangle followed by a pentagon when their unique common side is terminal for
both, then promote the second new rectangle to a pentagon. This applies when the second recut
rectangle inherits the original pentagon's terminal side; the turn-row membership is supplied
as a hypothesis. The result is a rectangle--pentagon decomposition. -/
noncomputable def recutRightEqRight_second
    (D : GridRectanglePentagonDecomposition a s x z)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).second.right = D.pentagon.right)
    (hturn : s ∈ Grid.cIco (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).second.bottom
      (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).second.top) :
    GridRectanglePentagonDecomposition a s x z :=
  { middle := (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).middle
    rectangle := (D.toRectangleDecomposition.recut hone
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
      (by
        simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
          D.toRectangleDecomposition_middle,
          D.toRectangleDecomposition_second_toGridRectangle] using
        hpentagon)).first
    pentagon := GridPentagonBetween.ofRightEq
      (D.toRectangleDecomposition.recut hone
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_first_toGridRectangle] using hrectangle)
        (by
          simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
            D.toRectangleDecomposition_middle,
            D.toRectangleDecomposition_second_toGridRectangle] using
          hpentagon)).second
      (hsecond.trans D.pentagon.right_eq)
      hturn }

end GridRectanglePentagonDecomposition

end TauCeti
