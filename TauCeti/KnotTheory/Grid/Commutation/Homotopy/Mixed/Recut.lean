/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Geometry

/-!
# Hexagon shapes in a mixed-side recut

Consider two rectangles whose common grid line is terminal for the first and initial for the
second, or initial for the first and terminal for the second, as for a pentagon turning on one
side of the replaced grid line followed by a pentagon turning on the other side. Off the
diagonal this line is their only common side. When both rectangles are empty, the recut from the
proof of `∂² = 0` cuts their union the other way. If the turn rows are placed as for such a
pentagon pair, no hexagon composite has this recut as its underlying rectangle decomposition: one
recut rectangle has no side on the replaced grid line, and the other misses one of the two turn
rows. This is the mixed-side counterpart of `SameSideRecut.lean`, and it serves the homotopy
equations of a column commutation and of a crossing change alike.

## Main results

* `toRectangleDecomposition_ne_recut_of_right_eq_left` and
  `toRectangleDecomposition_ne_recut_of_left_eq_right`, in the namespace
  `TauCeti.GridHexagonCompositeDecomposition`: the recut of two empty rectangles sharing the
  replaced grid line with opposite orientations, with the two turn rows placed as for a mixed-side
  pentagon pair, underlies no hexagon composite.

## References

This is the mixed-side case of the hexagon--rectangle juxtaposition argument of
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1,
Proposition 3.2 (arXiv:math/0610559).
-/

public section

namespace TauCeti.GridHexagonCompositeDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- One of the two rectangles under a hexagon composite has the replaced grid line as a side and
both turn rows among its rows. -/
private theorem side_turns (F : GridHexagonCompositeDecomposition a s s' x z) :
    ((F.toRectangleDecomposition.first.left = finRotate n a ∨
          F.toRectangleDecomposition.first.right = finRotate n a) ∧
        s ∈ Grid.cIco F.toRectangleDecomposition.first.bottom
          F.toRectangleDecomposition.first.top ∧
        s' ∈ Grid.cIco F.toRectangleDecomposition.first.bottom
          F.toRectangleDecomposition.first.top) ∨
      ((F.toRectangleDecomposition.second.left = finRotate n a ∨
          F.toRectangleDecomposition.second.right = finRotate n a) ∧
        s ∈ Grid.cIco F.toRectangleDecomposition.second.bottom
          F.toRectangleDecomposition.second.top ∧
        s' ∈ Grid.cIco F.toRectangleDecomposition.second.bottom
          F.toRectangleDecomposition.second.top) := by
  have key {u v : GridState n} (H : GridCommutationHexagonBetween a s s' u v) :=
    And.intro H.left_eq_or_right_eq <| And.intro
      (H.pair_subset_cIco_bottom_top (Finset.mem_insert_self _ _))
      (H.pair_subset_cIco_bottom_top (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  cases F with
  | inl F =>
    rw [toRectangleDecomposition_inl]
    exact Or.inl (key F.hexagon)
  | inr F =>
    rw [toRectangleDecomposition_inr]
    exact Or.inr (key F.hexagon)

/-- Let the empty rectangles of an off-diagonal decomposition `D` share the grid line
`finRotate n a`, terminal for the first and initial for the second, as the rectangles of a
terminal-side pentagon followed by an initial-side one do. If the first rectangle contains the row
`s` and the rows from its bottom up to the top of the second contain `s'`, then the recut of `D`
underlies no hexagon composite with turn rows `s` and `s'`: one recut rectangle has no side on the
grid line, and the other misses one of the two rows. -/
theorem toRectangleDecomposition_ne_recut_of_right_eq_left {D : GridRectangleDecomposition x z}
    (hright : D.first.right = finRotate n a) (hleft : D.second.left = finRotate n a)
    (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hs : s ∈ Grid.cIco D.first.bottom D.first.top)
    (hs' : s' ∈ Grid.cIco D.first.bottom D.second.top)
    (F : GridHexagonCompositeDecomposition a s s' x z) :
    F.toRectangleDecomposition ≠ D.recut hone hfirst hsecond := by
  intro hF
  have hdata := D.isRecutOfRightEqLeft_recut (hright.trans hleft.symm) hone hfirst hsecond
  rw [← hF] at hdata
  have hl : D.first.left ≠ finRotate n a := fun h => D.first.left_ne_right (h.trans hright.symm)
  have hr : D.second.right ≠ finRotate n a := fun h => D.second.left_ne_right (hleft.trans h.symm)
  rcases hdata.recut_geometry hone with
      ⟨hrow, h1l, h1r, h2l, h2r, h1b, h1t, -, -⟩ | ⟨hrow, h1l, h1r, h2l, h2r, -, -, h2b, h2t⟩ <;>
    rcases F.side_turns with ⟨hside, hturn, hturn'⟩ | ⟨hside, hturn, hturn'⟩
  · rw [h1b, h1t] at hturn
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hs hturn
  · rw [h2l, h2r] at hside
    exact hside.elim hl hr
  · rw [h1l, h1r] at hside
    exact hside.elim hl hr
  · rw [h2b, h2t] at hturn'
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hs' hturn'

/-- Let the empty rectangles of an off-diagonal decomposition `D` share the grid line
`finRotate n a`, initial for the first and terminal for the second, as the rectangles of an
initial-side pentagon followed by a terminal-side one do. If the first rectangle contains the row
`s` and the rows from the bottom of the second up to the top of the first contain `s'`, then the
recut of `D` underlies no hexagon composite with turn rows `s` and `s'`: one recut rectangle has
no side on the grid line, and the other misses one of the two rows. -/
theorem toRectangleDecomposition_ne_recut_of_left_eq_right {D : GridRectangleDecomposition x z}
    (hleft : D.first.left = finRotate n a) (hright : D.second.right = finRotate n a)
    (hone : D.HasOneCommonSide) (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty)
    (hs : s ∈ Grid.cIco D.first.bottom D.first.top)
    (hs' : s' ∈ Grid.cIco D.second.bottom D.first.top)
    (F : GridHexagonCompositeDecomposition a s s' x z) :
    F.toRectangleDecomposition ≠ D.recut hone hfirst hsecond := by
  intro hF
  have hdata := D.isRecutOfLeftEqRight_recut (hleft.trans hright.symm) hone hfirst hsecond
  rw [← hF] at hdata
  have hl : D.second.left ≠ finRotate n a := fun h => D.second.left_ne_right (h.trans hright.symm)
  have hr : D.first.right ≠ finRotate n a := fun h => D.first.left_ne_right (hleft.trans h.symm)
  rcases hdata.recut_geometry hone with
      ⟨hrow, h1l, h1r, h2l, h2r, h1b, h1t, -, -⟩ | ⟨hrow, h1l, h1r, h2l, h2r, -, -, h2b, h2t⟩ <;>
    rcases F.side_turns with ⟨hside, hturn, hturn'⟩ | ⟨hside, hturn, hturn'⟩
  · rw [h1b, h1t] at hturn
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hturn hs
  · rw [h2l, h2r] at hside
    exact hside.elim hl hr
  · rw [h1l, h1r] at hside
    exact hside.elim hl hr
  · rw [h2b, h2t] at hturn'
    exact Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow) hturn' hs'

end TauCeti.GridHexagonCompositeDecomposition

