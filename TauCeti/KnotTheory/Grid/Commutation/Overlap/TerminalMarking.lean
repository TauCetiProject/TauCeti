/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Right

/-!
# The promoted pentagons of a common-terminal-side overlap carry no new marking

Let `D` be a two-step domain of a column commutation made of a rectangle followed by a pentagon,
and let the two share their terminal side: the common-terminal-side overlap. The pentagon's
terminal side is the replaced grid line, so the rectangle ends on that line too, and the two
domains are stacked, the pentagon below the rectangle.
`TauCeti.KnotTheory.Grid.Commutation.Overlap.Right` recuts the L-shaped union the other way and
promotes to a pentagon whichever new rectangle inherits the replaced grid line, so that the two
contributions of the chain-map equation can be paired.

Pairing also needs the promoted pentagon to be a pentagon of the same kind as the original one,
that is to carry no `X`-marking. The covered-square repartition proved in `Overlap/Right.lean`
concerns the two *underlying rectangles*, and a pentagon covers only part of its underlying
rectangle: in the two columns next to the replaced grid line its turn row cuts the covered arc.
The pentagon-level statement is therefore its own, and it does follow from the geometry: the
promoted pentagon spans the rows of the original pentagon together with those of the original
rectangle, and its column arc is contained in both of theirs, so the general containment
`GridPentagonBetween.coveredSquares_subset_union_of_stacked` applies and an `X`-marking avoided
by both original domains is avoided by it.

Which of the two new rectangles inherits the replaced grid line is read off the column geometry.
If the first one does, the original pentagon's initial side lies strictly inside the original
rectangle's column arc and the promoted pentagon has that initial side; if the second one does,
the original rectangle's initial side lies strictly inside the original pentagon's column arc and
the promoted pentagon has *that* initial side. Either way the promoted pentagon starts at the
later of the two initial sides, hence inside both column arcs.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.coveredSquares_pentagon_subset_recutRightEqRightFirst`
  and `...Second`: the squares covered by the promoted pentagon are covered by the original
  pentagon or by the original rectangle.
* `TauCeti.GridRectanglePentagonDecomposition.
  disjoint_coveredSquares_XSet_pentagon_recutRightEqRightFirst` and `...Second`: the promoted
  pentagon carries no `X`-marking when neither of the two original domains does.

## References

The pairing of the two contributions in the chain-map equation of a column commutation is that of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1. The recut hexagon is
cut the other way, and the pentagon of the new pairing must be one of the empty pentagons carrying
no `X`-marking that the pentagon map of `TauCeti.KnotTheory.Grid.Commutation.Pentagon` counts.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- At a common terminal side the original pentagon sits directly below the original rectangle:
its top row is the rectangle's bottom row. -/
private theorem pentagon_top_eq_rectangle_bottom (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right) :
    D.pentagon.top = D.rectangle.bottom := by
  rw [GridRectangleBetween.top_def, ← hcommon, D.rectangle.map_right,
    ← GridRectangleBetween.bottom_def]

/-- The bottom row of the original pentagon, read in the source state: away from the two side
columns of the original rectangle the intermediate state agrees with the source state. -/
private theorem pentagon_bottom_eq (D : GridRectanglePentagonDecomposition a s x z)
    (hleft : D.pentagon.left ≠ D.rectangle.left)
    (hright : D.pentagon.left ≠ D.rectangle.right) :
    D.pentagon.bottom = x D.pentagon.left :=
  (GridRectangleBetween.bottom_def D.pentagon.toGridRectangleBetween).trans
    (D.rectangle.map_of_ne _ hleft hright)

/-- The squares covered by the promoted pentagon of the common-terminal-side overlap recut, in
the branch where the first new rectangle inherits the replaced grid line, are covered by the
original pentagon or by the original rectangle. -/
theorem coveredSquares_pentagon_subset_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right = D.pentagon.right) :
    (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).pentagon.coveredSquares ⊆
      D.pentagon.coveredSquares ∪ D.rectangle.toGridRectangle.coveredSquares := by
  obtain ⟨hcol, hEright, hEleft⟩ :=
    D.first_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hfirst
  simp only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left] at hcol hEright hEleft
  have hbottom := D.pentagon_bottom_eq (Grid.ne_left_of_mem_cIoo hcol)
    (Grid.ne_right_of_mem_cIoo hcol)
  have hb : D.rectangle.right = finRotate n a := hcommon.trans D.pentagon.right_eq
  refine GridPentagonBetween.coveredSquares_subset_union_of_stacked _ D.pentagon
    D.rectangle.toGridRectangle ?_ ?_ ?_ ?_ ?_
  · rw [D.recutRightEqRightFirst_pentagon_bottom hcommon hone hrectangle hpentagon hfirst,
      GridRectangleBetween.bottom_def, hEleft, hbottom]
  · rw [D.recutRightEqRightFirst_pentagon_top hcommon hone hrectangle hpentagon hfirst,
      GridRectangleBetween.top_def, hEright, GridRectangleBetween.toGridRectangle_top,
      GridRectangleBetween.top_def]
  · rw [GridRectangleBetween.toGridRectangle_bottom]
    exact D.pentagon_top_eq_rectangle_bottom hcommon
  · rw [D.recutRightEqRightFirst_pentagon_left hcommon hone hrectangle hpentagon hfirst, hEleft]
  · rw [D.recutRightEqRightFirst_pentagon_left hcommon hone hrectangle hpentagon hfirst, hEleft,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right, ← hb]
    exact Grid.cIco_subset_of_mem_cIoo hcol

/-- The promoted pentagon of the common-terminal-side overlap recut carries no `X`-marking, in
the branch where the first new rectangle inherits the replaced grid line, as soon as neither the
original pentagon nor the original rectangle does. -/
theorem disjoint_coveredSquares_XSet_pentagon_recutRightEqRightFirst
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirst : (D.recutOfIsEmpty hone hrectangle hpentagon).first.right = D.pentagon.right)
    (G : GridDiagram n) (hX : Disjoint D.pentagon.coveredSquares G.XSet)
    (hrectX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet) :
    Disjoint
      (D.recutRightEqRightFirst hcommon hone hrectangle hpentagon hfirst).pentagon.coveredSquares
      G.XSet :=
  (Finset.disjoint_union_left.mpr ⟨hX, hrectX⟩).mono_left
    (D.coveredSquares_pentagon_subset_recutRightEqRightFirst hcommon hone hrectangle hpentagon
      hfirst)

/-- The squares covered by the promoted pentagon of the common-terminal-side overlap recut, in
the branch where the second new rectangle inherits the replaced grid line, are covered by the
original pentagon or by the original rectangle. -/
theorem coveredSquares_pentagon_subset_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right = D.pentagon.right) :
    (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).pentagon.coveredSquares ⊆
      D.pentagon.coveredSquares ∪ D.rectangle.toGridRectangle.coveredSquares := by
  obtain ⟨hcol, hEright, hEleft, hEmiddle⟩ :=
    D.second_recut_branch_data_of_right_eq_right hcommon hone hrectangle hpentagon hsecond
  simp only [toRectangleDecomposition_first_left, toRectangleDecomposition_first_right,
    toRectangleDecomposition_second_left] at hcol hEright hEleft hEmiddle
  have hne : D.pentagon.left ≠ D.rectangle.right :=
    ((Grid.mem_cIoo D.pentagon.left D.rectangle.right D.rectangle.left).mp hcol).1
  have hbottom := D.pentagon_bottom_eq (Grid.ne_left_of_mem_cIoo hcol).symm hne
  have hb : D.rectangle.right = finRotate n a := hcommon.trans D.pentagon.right_eq
  refine GridPentagonBetween.coveredSquares_subset_union_of_stacked _ D.pentagon
    D.rectangle.toGridRectangle ?_ ?_ ?_ ?_ ?_
  · rw [D.recutRightEqRightSecond_pentagon_bottom hcommon hone hrectangle hpentagon hsecond,
      GridRectangleBetween.bottom_def, hEleft, hEmiddle, GridState.swapColumns_apply,
      Equiv.swap_apply_right, hbottom]
  · rw [D.recutRightEqRightSecond_pentagon_top hcommon hone hrectangle hpentagon hsecond,
      GridRectangleBetween.top_def, hEright, hEmiddle, GridState.swapColumns_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hne) (Ne.symm D.rectangle.left_ne_right),
      GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.top_def]
  · rw [GridRectangleBetween.toGridRectangle_bottom]
    exact D.pentagon_top_eq_rectangle_bottom hcommon
  · rw [D.recutRightEqRightSecond_pentagon_left hcommon hone hrectangle hpentagon hsecond, hEleft,
      ← hb]
    exact Grid.cIco_subset_of_mem_cIoo hcol
  · rw [D.recutRightEqRightSecond_pentagon_left hcommon hone hrectangle hpentagon hsecond, hEleft,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right, ← hb]

/-- The promoted pentagon of the common-terminal-side overlap recut carries no `X`-marking, in
the branch where the second new rectangle inherits the replaced grid line, as soon as neither the
original pentagon nor the original rectangle does. -/
theorem disjoint_coveredSquares_XSet_pentagon_recutRightEqRightSecond
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.right = D.pentagon.right)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hsecond : (D.recutOfIsEmpty hone hrectangle hpentagon).second.right = D.pentagon.right)
    (G : GridDiagram n) (hX : Disjoint D.pentagon.coveredSquares G.XSet)
    (hrectX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet) :
    Disjoint
      (D.recutRightEqRightSecond hcommon hone hrectangle hpentagon hsecond).pentagon.coveredSquares
      G.XSet :=
  (Finset.disjoint_union_left.mpr ⟨hX, hrectX⟩).mono_left
    (D.coveredSquares_pentagon_subset_recutRightEqRightSecond hcommon hone hrectangle hpentagon
      hsecond)

end GridRectanglePentagonDecomposition

end TauCeti
