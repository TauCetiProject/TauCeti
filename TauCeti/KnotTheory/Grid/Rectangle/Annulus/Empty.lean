/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Rectangle.Annulus.Basic

/-!
# Empty returning rectangles form thin annuli

A pair of oriented rectangles that returns to its source covers either a vertical or a
horizontal toroidal annulus. If both rectangles are empty, that annulus must be thin. Indeed, a
column strictly between the sides of a vertical annulus carries a point of the source grid state,
and that point lies in the interior of exactly one of the two rectangles. The horizontal case is
the transpose of this argument.

This file characterizes the simultaneous emptiness of a returning pair. For the vertical
orientation, the terminal side is the cyclic successor of the initial side. For the horizontal
orientation, the top row is the cyclic successor of the bottom row. The combined characterization
is the empty analogue of `GridRectangleBetween.left_right_eq_cases`.

## Main results

* `TauCeti.GridRectangleBetween.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left`:
  a same-side-order returning pair is empty exactly when it forms a thin vertical annulus.
* `TauCeti.GridRectangleBetween.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right`:
  an opposite-side-order returning pair is empty exactly when it forms a thin horizontal annulus.
* `TauCeti.GridRectangleBetween.isEmpty_and_isEmpty_iff`: every empty returning pair has exactly
  one of these two thin-annulus shapes.

## References

The thin-annulus classification is the returning case of the rectangle juxtaposition argument
in Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Chapters 4.6 and 5.1.
-/

public section

namespace TauCeti

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y)
  (S : GridRectangleBetween y x)

/-- If a returning pair starts on the same side, then both rectangles are empty exactly when
their common terminal side is the cyclic successor of their common initial side. -/
theorem isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left
    (hleft : S.left = R.left) :
    R.IsEmpty ∧ S.IsEmpty ↔ R.right = finRotate n R.left := by
  have hright : S.right = R.right := by
    rcases R.left_right_eq_cases S with hsame | hopposite
    · exact hsame.2
    · exact absurd (hleft.trans hopposite.2.symm) S.left_ne_right
  constructor
  · rintro ⟨hR, hS⟩
    have hinterior : Grid.cIoo R.left R.right = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      have hcl : c ≠ R.left := Grid.ne_left_of_mem_cIoo hc
      have hcr : c ≠ R.right := Grid.ne_right_of_mem_cIoo hc
      have hrowLeft : x c ≠ R.bottom := by
        rw [R.bottom_def]
        exact x.toPerm.injective.ne hcl
      have hrowRight : x c ≠ R.top := by
        rw [R.top_def]
        exact x.toPerm.injective.ne hcr
      have hrow := (Grid.mem_cIoo_or_mem_cIoo_swap_iff R.bottom_ne_top).2
        ⟨hrowLeft, hrowRight⟩
      rcases hrow with hbetween | hbetween
      · exact ((R.isEmpty_iff_forall_notMem_cIoo).1 hR c hc) hbetween
      · have hyc : y c = x c := R.map_of_ne c hcl hcr
        have hSbottom : S.bottom = R.top := by
          rw [S.bottom_def, hleft, R.map_left, R.top_def]
        have hStop : S.top = R.bottom := by
          rw [S.top_def, hright, R.map_right, R.bottom_def]
        exact ((S.isEmpty_iff_forall_notMem_cIoo).1 hS c (by simpa [hleft, hright] using hc))
          (by simpa [hyc, hSbottom, hStop] using hbetween)
    have hcIco : Grid.cIco R.left R.right = {R.left} := by
      rw [Grid.cIco_of_ne R.left_ne_right, hinterior]
      simp
    exact ((Grid.cIco_eq_singleton_iff).1 hcIco).2.1
  · intro hnext
    refine ⟨R.isEmpty_of_right_eq_finRotate hnext, S.isEmpty_of_right_eq_finRotate ?_⟩
    rw [hleft, hright, hnext]

/-- If a returning pair starts on opposite sides, then both rectangles are empty exactly when
their common top row is the cyclic successor of their common bottom row. -/
theorem isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right
    (hleft : S.left = R.right) :
    R.IsEmpty ∧ S.IsEmpty ↔ R.top = finRotate n R.bottom := by
  have hbottom : S.bottom = R.bottom := by
    rw [S.bottom_def, hleft, R.map_right, R.bottom_def]
  simpa only [isEmpty_transpose, transpose_right, transpose_left] using
    R.transpose.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left S.transpose hbottom

/-- Two returning rectangles are both empty exactly when they form a thin vertical annulus in
the same-side-order case or a thin horizontal annulus in the opposite-side-order case. -/
theorem isEmpty_and_isEmpty_iff :
    R.IsEmpty ∧ S.IsEmpty ↔
      (S.left = R.left ∧ R.right = finRotate n R.left) ∨
        (S.left = R.right ∧ R.top = finRotate n R.bottom) := by
  rcases R.left_right_eq_cases S with hsame | hopposite
  · constructor
    · intro hempty
      exact Or.inl ⟨hsame.1,
        (R.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left S hsame.1).1 hempty⟩
    · rintro (⟨-, hnext⟩ | ⟨hleft, -⟩)
      · exact (R.isEmpty_and_isEmpty_iff_right_eq_finRotate_of_left_eq_left S hsame.1).2 hnext
      · exact absurd (hsame.1.symm.trans hleft) R.left_ne_right
  · constructor
    · intro hempty
      exact Or.inr ⟨hopposite.1,
        (R.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right S hopposite.1).1 hempty⟩
    · rintro (⟨hleft, -⟩ | ⟨-, hnext⟩)
      · exact absurd (hopposite.1.symm.trans hleft) R.left_ne_right.symm
      · exact
          (R.isEmpty_and_isEmpty_iff_top_eq_finRotate_of_left_eq_right S hopposite.1).2 hnext

end GridRectangleBetween

end TauCeti
