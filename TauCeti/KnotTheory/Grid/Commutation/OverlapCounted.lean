/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap

/-!
# Countedness pieces for the overlap recut

This file assembles countedness results for the `recutLeftEqLeft` construction, split by
recut branch.

## Part A: Branch-1 recut rectangle

In Branch 1 of the recut (`E.second.left = D.rectangle.left`,
`E.second.right = D.rectangle.right`), the recut rectangle retains the original rectangle's
column sides. Its X-avoidance in the column-swapped diagram is not yet established: the
recut rectangle's row span differs from the original's, so its covered squares are not
contained in the original rectangle's, and the naive subset transfer does not apply.
This remains an open piece of the branch-1 countedness argument.

## Part B: Branch-2 pentagon X-avoidance

In Branch 2, the recut pentagon's bottom row is `x (finRotate n C.column)`. Its extra strip
`{finRotate n C.column} ×ˢ cIco bottom C.turnRow` avoids X by combining the original
rectangle's and pentagon's X-avoidance over the relevant row intervals.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.branch2_X_not_mem_rectangle_rows`: the
  X-marking of the replaced grid line avoids the original rectangle's row interval.
* `TauCeti.GridRectanglePentagonDecomposition.branch2_X_not_mem_pentagon_rows`: the
  X-marking avoids the original pentagon's row interval below the turn.
* `TauCeti.GridRectanglePentagonDecomposition.branch2_pentagon_strip_X_avoidance`:
  Branch-2 recut pentagon extra strip avoids X.

Each transfer lemma takes only the component membership its proof uses (the rectangle's
or the pentagon's X-avoidance), not the full counted decomposition.

Roadmap target: Lane G, milestone 5 ("Invariance over 𝔽₂") of
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`: the pentagon-counting commutation
chain map.
-/

public section

namespace TauCeti

/-!
## Part B: Branch-2 pentagon X-avoidance

In Branch 2, the recut's first rectangle has `E.first.left = D.rectangle.left`, so the new
pentagon's bottom is `x D.rectangle.left`. Its extra strip `{b} ×ˢ cIco (x l) s` avoids X by
combining the original rectangle's X-avoidance (over `cIco (x l) (x r₁)`) with the original
pentagon's X-avoidance (over `cIco (x r₁) s`), where `r₁ = D.rectangle.right`.
-/

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
    (hrect : D.rectangle ∈ G.unblockedRectangles x D.middle)
    (hbranch : b ∈ Grid.cIoo D.rectangle.left D.rectangle.right) :
    G.X b ∉ Grid.cIco (x D.rectangle.left) (x D.rectangle.right) := by
  have hX : Disjoint D.rectangle.toGridRectangle.coveredSquares G.XSet :=
    ((G.mem_unblockedRectangles D.rectangle).mp hrect).2
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
    (hpent : D.pentagon ∈ G.pentagons C D.middle z)
    (hcommon : D.rectangle.left = D.pentagon.left) :
    G.X b ∉ Grid.cIco (x D.rectangle.right) C.turnRow := by
  have hX : Disjoint D.pentagon.coveredSquares G.XSet :=
    ((G.mem_pentagons D.pentagon).mp hpent).2
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
    (hrect : D.rectangle ∈ G.unblockedRectangles x D.middle)
    (hpent : D.pentagon ∈ G.pentagons C D.middle z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hbranch : b ∈ Grid.cIoo D.rectangle.left D.rectangle.right)
    (hcyc : x D.rectangle.right ∈ Grid.cIoo (x D.rectangle.left) C.turnRow) :
    G.X b ∉ Grid.cIco (x D.rectangle.left) C.turnRow := by
  have hrect_avoid := D.branch2_X_not_mem_rectangle_rows hrect hbranch
  have hpent_avoid := D.branch2_X_not_mem_pentagon_rows hpent hcommon
  intro hmem
  have hunion := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcyc
  rw [← hunion] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact hrect_avoid h
  · exact hpent_avoid h

end GridRectanglePentagonDecomposition

end TauCeti
