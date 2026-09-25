/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap
public import TauCeti.KnotTheory.Grid.Commutation.OverlapColumns
public import TauCeti.KnotTheory.Grid.Commutation.OverlapXAvoid
public import TauCeti.KnotTheory.Grid.Commutation.OverlapBranch2

/-!
# Countedness pieces for the overlap recut

This file assembles countedness results for the `recutLeftEqLeft` construction, split by
recut branch.

## Part A: Branch-1 recut rectangle

In Branch 1 of the recut (`E.second.left = D.rectangle.left`,
`E.second.right = D.rectangle.right`), the recut rectangle retains the original rectangle's
sides. Its X-avoidance in the column-swapped diagram follows from the original rectangle's
X-avoidance via the covered-columns transfer
(`disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns`), using
`branch1_mem_coveredColumns_iff` from `OverlapColumns.lean`.

## Part B: Branch-2 pentagon X-avoidance

In Branch 2, the recut pentagon's bottom row is `x (finRotate n C.column)`. Its extra strip
`{finRotate n C.column} ×ˢ cIco bottom C.turnRow` avoids X by combining the original
rectangle's and pentagon's X-avoidance over the relevant row intervals.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.branch1_recut_rectangle_X_avoidance_swap`:
  Branch-1 recut rectangle avoids X in the swapped diagram.
* `TauCeti.GridRectanglePentagonDecomposition.branch2_pentagon_strip_X_avoidance`:
  Branch-2 recut pentagon extra strip avoids X.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {G : GridDiagram n} {C : GridDiagram.ColumnCommutationData G}
variable {x z : GridState n}

local notation "b" => finRotate n C.column

/-!
## Part A: Branch-1 recut rectangle X-avoidance in the swapped diagram
-/

/-- In Branch 1, the recut rectangle's covered columns coincide with the original rectangle's,
so the covered-columns iff from `OverlapColumns` applies. -/
theorem branch1_recut_rectangle_coveredColumns_iff
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (R' : GridRectangle n)
    (hR'col : R'.coveredColumns = Grid.cIco D.rectangle.left D.rectangle.right) :
    C.column ∈ R'.coveredColumns ↔ b ∈ R'.coveredColumns := by
  rw [hR'col]
  have hl : D.rectangle.left ≠ b := by
    rw [hcommon]
    exact D.pentagon.left_ne
  have hr : D.rectangle.right ≠ b := by
    have hpen_right : D.pentagon.right = b := D.pentagon.right_eq
    have hne : D.toRectangleDecomposition.first.right ≠
        D.toRectangleDecomposition.second.right := by
      have hcommon' : D.toRectangleDecomposition.first.left =
          D.toRectangleDecomposition.second.left := by
        simpa only [D.toRectangleDecomposition_first_left,
          D.toRectangleDecomposition_second_left] using hcommon
      intro hright
      apply D.toRectangleDecomposition.sideColumns_ne_of_hasOneCommonSide hone
      rw [GridRectangleBetween.sideColumns, GridRectangleBetween.sideColumns, hcommon', hright]
    rw [D.toRectangleDecomposition_first_right, D.toRectangleDecomposition_second_right] at hne
    rw [hpen_right] at hne
    exact hne
  exact branch1_mem_coveredColumns_iff D.rectangle.left D.rectangle.right hl hr

/-- Branch-1 recut rectangle X-avoidance transfers to the column-swapped diagram.

When the recut rectangle `R'` has the same covered squares as the original rectangle `R`
(which is X-avoiding), and the covered-columns iff holds, the transfer lemma gives
X-avoidance in the swapped diagram. -/
theorem branch1_recut_rectangle_X_avoidance_swap
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (R' : GridRectangle n)
    (hR'sq : R'.coveredSquares = D.rectangle.toGridRectangle.coveredSquares)
    (hR'col : R'.coveredColumns = Grid.cIco D.rectangle.left D.rectangle.right) :
    Disjoint R'.coveredSquares (G.swapColumns C.column b).XSet := by
  have hX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet :=
    ((G.mem_unblockedRectangles D.rectangle).mp
      ((G.mem_rectanglePentagonDecompositions C D).mp hD).1).2
  have hiff := D.branch1_recut_rectangle_coveredColumns_iff hcommon hone R' hR'col
  have htrans := (G.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns R' hiff).mpr
  apply htrans
  rw [hR'sq]
  exact hX

end GridRectanglePentagonDecomposition

/-!
## Part B: Branch-2 pentagon X-avoidance

In Branch 2, the recut's first rectangle has `E.first.left = D.rectangle.left`, so the new
pentagon's bottom is `x D.rectangle.left`. Its extra strip `{b} ×ˢ cIco (x l) s` avoids X by
combining the original rectangle's X-avoidance (over `cIco (x l) (x r₁)`) with the original
pentagon's X-avoidance (over `cIco (x r₁) s`), where `r₁ = D.rectangle.right`.
-/

/-- Interval nesting: a point in `cIco A B` with `B` strictly inside `cIco A C` lies in
`cIco A C`. This is the `cIco`-membership version of `cIco_subset_of_mem_cIoo`. -/
theorem Grid.cIco_subset_cIco_of_mem_cIco {n : ℕ} {A B C s : Fin n}
    (hmem : s ∈ Grid.cIco A B) (hB : B ∈ Grid.cIoo A C) :
    s ∈ Grid.cIco A C := by
  have hunion := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hB
  rw [← hunion]
  exact Finset.mem_union.mpr (Or.inl hmem)

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {G : GridDiagram n} {C : GridDiagram.ColumnCommutationData G}
variable {x z : GridState n}

local notation "b" => finRotate n C.column

/-- Branch-2: the X-marking of the replaced grid line avoids the rectangle's row interval.

From the rectangle's X-avoidance: since `b ∈ cIoo l r₁` (branch hypothesis), `b` is a covered
column, so `(b, G.X b)` would lie in the covered squares if `G.X b` were in the row interval,
contradicting disjointness. -/
theorem branch2_X_not_mem_rectangle_rows
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (hbranch : b ∈ Grid.cIoo D.rectangle.left D.rectangle.right) :
    G.X b ∉ Grid.cIco (x D.rectangle.left) (x D.rectangle.right) := by
  have hX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet :=
    ((G.mem_unblockedRectangles D.rectangle).mp
      ((G.mem_rectanglePentagonDecompositions C D).mp hD).1).2
  intro hmem
  have hb_col : b ∈ D.rectangle.toGridRectangle.coveredColumns := by
    rw [GridRectangle.coveredColumns_def, GridRectangleBetween.toGridRectangle_left,
      GridRectangleBetween.toGridRectangle_right]
    exact Grid.cIoo_subset_cIco _ _ hbranch
  have hmem_sq : (b, G.X b) ∈ D.rectangle.toGridRectangle.coveredSquares := by
    rw [GridRectangle.mem_coveredSquares]
    refine ⟨hb_col, ?_⟩
    rw [GridRectangle.coveredRows_def, GridRectangleBetween.toGridRectangle_bottom,
      GridRectangleBetween.toGridRectangle_top, GridRectangleBetween.bottom_def,
      GridRectangleBetween.top_def]
    exact hmem
  have hXmem : (b, G.X b) ∈ G.XSet := by simp [GridDiagram.XSet]
  exact (Finset.disjoint_left.mp hX) hmem_sq hXmem

/-- Branch-2: the X-marking avoids the pentagon's row interval below the turn.

The pentagon's covered squares contain the strip `{b} ×ˢ cIco (D.pentagon.bottom) s`.
Since `D.pentagon.bottom = x D.rectangle.right` (via `D.middle` and `hcommon`), X-avoidance
of the pentagon gives the result. -/
theorem branch2_X_not_mem_pentagon_rows
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (hcommon : D.rectangle.left = D.pentagon.left) :
    G.X b ∉ Grid.cIco (x D.rectangle.right) C.turnRow := by
  have hX : Disjoint D.pentagon.coveredSquares G.XSet :=
    ((G.mem_pentagons D.pentagon).mp
      ((G.mem_rectanglePentagonDecompositions C D).mp hD).2).2
  have hbot : D.pentagon.bottom = x D.rectangle.right := by
    simp only [GridRectangleBetween.bottom_def, hcommon.symm,
      D.rectangle.target_eq_swapColumns, GridState.swapColumns_apply,
      Equiv.swap_apply_left]
  intro hmem
  have hmem' : G.X b ∈ Grid.cIco D.pentagon.bottom C.turnRow := by
    have := hmem
    rw [← hbot] at this
    exact this
  have hmem_sq : (b, G.X b) ∈ D.pentagon.coveredSquares :=
    (D.pentagon.mem_coveredSquares (b, G.X b)).mpr (Or.inr (Or.inr ⟨rfl, hmem'⟩))
  have hXmem : (b, G.X b) ∈ G.XSet := by simp [GridDiagram.XSet]
  exact (Finset.disjoint_left.mp hX) hmem_sq hXmem

/-- Branch-2: combined X-avoidance over the full strip interval.

Given `x r₁ ∈ cIoo (x l) s` (the cyclic order placing the rectangle's top strictly between
its bottom and the turn row), the two row-interval avoidances combine to cover
`cIco (x l) s`. -/
theorem branch2_pentagon_strip_X_avoidance
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hbranch : b ∈ Grid.cIoo D.rectangle.left D.rectangle.right)
    (hcyc : x D.rectangle.right ∈ Grid.cIoo (x D.rectangle.left) C.turnRow) :
    G.X b ∉ Grid.cIco (x D.rectangle.left) C.turnRow := by
  have hrect := D.branch2_X_not_mem_rectangle_rows hD hbranch
  have hpent := D.branch2_X_not_mem_pentagon_rows hD hcommon
  intro hmem
  have hunion := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcyc
  rw [← hunion] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact hrect h
  · exact hpent h

end GridRectanglePentagonDecomposition

end TauCeti
