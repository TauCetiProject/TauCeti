/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Initial
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Terminal

/-!
# Recutting two-step grid rectangle decompositions with a mixed common side

Two composable empty rectangles sharing exactly one side column form an L-shaped domain with a
second cut uniquely characterized by its computed side rows and row configuration. The cases where
the common column is initial for both rectangles or terminal for both are handled in
`Recut.Initial` and `Recut.Terminal`. This file treats the two remaining orientations: the common
column is initial for one rectangle and terminal for the other.

Diagonal reflection turns either mixed column orientation into one of the same-side orientations.
Reflecting its recut back gives the required second decomposition. Accordingly, its side *rows*
rather than its side columns are computed explicitly. The reflected domain is still a repartition,
so the new rectangles cover the same squares as the old ones.

## Main results

* `TauCeti.GridRectangleDecomposition.exists_isRepartition_of_isEmpty_of_left_eq_right` and
  `exists_isRepartition_of_isEmpty_of_right_eq_left`: the two mixed common-side configurations
  admit recuts through different intermediate states, uniquely characterized by their computed
  side rows and row configurations, with both new rectangles empty.

## References

The recut is the overlapping-rectangle case of Ozsváth--Stipsicz--Szabó, *Grid Homology for
Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- The reflection of a state is a column swap of the reflected source exactly when the state is
the corresponding row swap of the source. -/
private theorem transpose_eq_swapColumns_iff (m : GridState n) (a b : Fin n) :
    m.transpose = x.transpose.swapColumns a b ↔ m = x.swapRows a b := by
  rw [← GridState.swapRows_transpose, GridState.transpose_inj]

/-! ### Initial side of the first rectangle equals terminal side of the second -/

/-- Two composable empty rectangles whose common column is the initial side of the first and the
terminal side of the second admit a recut through a different intermediate state, unique among
decompositions with the stated side rows and row configuration.

The two alternatives record which of the two noncommon corner rows lies inside the other row
span. They compute all four side rows of the recut and hence determine it uniquely after diagonal
reflection. -/
theorem exists_isRepartition_of_isEmpty_of_left_eq_right
    (D : GridRectangleDecomposition x z)
    (hcommon : D.first.left = D.second.right) (hother : D.first.right ≠ D.second.left)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧ E.first.IsEmpty ∧ E.second.IsEmpty ∧
        E.first.bottom = D.second.bottom ∧ E.second.bottom = D.first.bottom ∧
          ((D.first.bottom ∈ Grid.cIoo D.second.bottom D.first.top ∧
              E.middle = x.swapRows D.second.bottom D.first.bottom ∧
                E.first.top = D.first.bottom ∧ E.second.top = D.first.top) ∨
            (D.second.bottom ∈ Grid.cIoo D.first.bottom D.first.top ∧
              E.middle = x.swapRows D.second.bottom D.first.top ∧
                E.first.top = D.first.top ∧ E.second.top = D.second.bottom)) := by
  have htransRight : D.transpose.first.right = D.transpose.second.right := by
    simpa only [transpose_first_right, transpose_second_right, GridRectangleBetween.top_def,
      hcommon] using D.first.map_left.symm
  have hsecondLeft_ne_firstLeft : D.second.left ≠ D.first.left := fun h =>
    D.second.left_ne_right (h.trans hcommon)
  have hmiddle_secondLeft : D.middle D.second.left = x D.second.left :=
    D.first.map_of_ne D.second.left hsecondLeft_ne_firstLeft hother.symm
  have htransLeft : D.transpose.first.left ≠ D.transpose.second.left := by
    simpa only [transpose_first_left, transpose_second_left, GridRectangleBetween.bottom_def,
      hmiddle_secondLeft] using x.toPerm.injective.ne hsecondLeft_ne_firstLeft.symm
  refine (transposeEquiv x z).existsUnique_congr (fun E => ?_) |>.mpr
    (D.transpose.exists_isRepartition_of_isEmpty_of_right_eq_right htransRight htransLeft
      (D.isEmpty_transpose_first.mpr hfirst) (D.isEmpty_transpose_second.mpr hsecond))
  rw [transposeEquiv_apply]
  simp only [IsRepartition.transpose_iff, transpose_middle, GridState.transpose_inj, ne_eq,
    transpose_eq_swapColumns_iff, isEmpty_transpose_first, isEmpty_transpose_second,
    transpose_first_left, transpose_first_right, transpose_second_left, transpose_second_right]

/-! ### Terminal side of the first rectangle equals initial side of the second -/

/-- Two composable empty rectangles whose common column is the terminal side of the first and the
initial side of the second admit a recut through a different intermediate state, unique among
decompositions with the stated side rows and row configuration.

The two alternatives record which of the two noncommon corner rows lies inside the other row
span. They compute all four side rows of the recut and hence determine it uniquely after diagonal
reflection. -/
theorem exists_isRepartition_of_isEmpty_of_right_eq_left
    (D : GridRectangleDecomposition x z)
    (hcommon : D.first.right = D.second.left) (hother : D.first.left ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧ E.first.IsEmpty ∧ E.second.IsEmpty ∧
        E.first.top = D.second.top ∧ E.second.top = D.first.top ∧
          ((D.first.top ∈ Grid.cIoo D.first.bottom D.second.top ∧
              E.middle = x.swapRows D.first.top D.second.top ∧
                E.first.bottom = D.first.top ∧ E.second.bottom = D.first.bottom) ∨
            (D.second.top ∈ Grid.cIoo D.first.bottom D.first.top ∧
              E.middle = x.swapRows D.first.bottom D.second.top ∧
                E.first.bottom = D.first.bottom ∧ E.second.bottom = D.second.top)) := by
  -- Reflection converts this orientation into the common-initial-side case.
  have htransLeft : D.transpose.first.left = D.transpose.second.left := by
    simpa only [transpose_first_left, transpose_second_left, GridRectangleBetween.bottom_def,
      hcommon] using D.first.map_right.symm
  have htransRight : D.transpose.first.right ≠ D.transpose.second.right := by
    intro h
    apply hother
    apply D.middle.toPerm.injective
    calc
      D.middle D.first.left = x D.first.right := D.first.map_left
      _ = D.first.top := D.first.top_def.symm
      _ = D.second.top := by
        simpa only [transpose_first_right, transpose_second_right] using h
      _ = D.middle D.second.right := D.second.top_def
  refine (transposeEquiv x z).existsUnique_congr (fun E => ?_) |>.mpr
    (D.transpose.exists_isRepartition_of_isEmpty_of_left_eq_left htransLeft htransRight
      (D.isEmpty_transpose_first.mpr hfirst) (D.isEmpty_transpose_second.mpr hsecond))
  rw [transposeEquiv_apply]
  simp only [IsRepartition.transpose_iff, transpose_middle, GridState.transpose_inj, ne_eq,
    transpose_eq_swapColumns_iff, isEmpty_transpose_first, isEmpty_transpose_second,
    transpose_first_left, transpose_first_right, transpose_second_left, transpose_second_right]

end GridRectangleDecomposition

end TauCeti
