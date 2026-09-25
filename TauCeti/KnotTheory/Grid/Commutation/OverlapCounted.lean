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
  X-marking of a covered column avoids an X-avoiding rectangle's row interval.
* `TauCeti.GridRectanglePentagonDecomposition.branch2_X_not_mem_pentagon_rows`: the
  X-marking of the `finRotate` column avoids a pentagon's strip below the turn row, from
  the pentagon's X-avoidance. This is the shared strip argument also used for the
  branch-1 recut (`recut_X_not_mem_of_branch1` in `OverlapXAvoid`).
* `TauCeti.GridRectanglePentagonDecomposition.branch2_pentagon_strip_X_avoidance`:
  two row-interval X-avoidances combine over a cyclic-ordered interval union.

Each transfer lemma takes only what its proof uses: X-avoidance of the relevant
component (never counted membership) plus the interval data, not the full counted
decomposition.

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

/-- Branch-2: the X-marking of a covered column avoids an X-avoiding rectangle's rows.

If `b` is a covered column of an X-avoiding rectangle `R`, then `(b, G.X b)` would lie
in the covered squares if `G.X b` were in the row interval, contradicting disjointness.
Only the rectangle's X-avoidance is used. -/
theorem branch2_X_not_mem_rectangle_rows
    (R : GridRectangle n)
    (hX : Disjoint R.coveredSquares G.XSet)
    (hb : b ∈ R.coveredColumns) :
    G.X b ∉ R.coveredRows := by
  intro hmem
  have hmem_sq : (b, G.X b) ∈ R.coveredSquares := by
    rw [GridRectangle.mem_coveredSquares]
    exact ⟨hb, hmem⟩
  have hXmem : (b, G.X b) ∈ G.XSet := by simp [GridDiagram.XSet]
  exact (Finset.disjoint_left.mp hX) hmem_sq hXmem

/-- Branch-2: the X-marking avoids the pentagon's strip below the turn row.

The `X`-avoidance equivalence `GridPentagonBetween.disjoint_coveredSquares_XSet_iff`
exposes the strip clause `G.X (finRotate n a) ∉ cIco P.bottom s` directly. Only the
pentagon's X-avoidance is used.

This is the shared strip argument: the branch-1 recut strip
(`recut_X_not_mem_of_branch1` in `OverlapXAvoid`) is the same statement with the recut's
first rectangle's bottom in place of `bot`. -/
theorem branch2_X_not_mem_pentagon_rows
    {a s : Fin n} {u v : GridState n}
    (P : GridPentagonBetween a s u v)
    (hX : Disjoint P.coveredSquares G.XSet)
    (bot : Fin n)
    (hbot : P.bottom = bot) :
    G.X (finRotate n a) ∉ Grid.cIco bot s := by
  -- The pentagon disjointness equivalence exposes the strip clause directly.
  rw [GridPentagonBetween.disjoint_coveredSquares_XSet_iff] at hX
  obtain ⟨_, _, hXb⟩ := hX
  rw [← hbot]
  exact hXb

/-- Branch-2: combined X-avoidance over the full strip interval.

Given `r₁ ∈ cIoo r₀ s` (the cyclic order placing the split point strictly between the
interval ends), the two row-interval avoidances combine to cover `cIco r₀ s`. -/
theorem branch2_pentagon_strip_X_avoidance
    (r₀ r₁ s : Fin n)
    (hrect_avoid : G.X b ∉ Grid.cIco r₀ r₁)
    (hpent_avoid : G.X b ∉ Grid.cIco r₁ s)
    (hcyc : r₁ ∈ Grid.cIoo r₀ s) :
    G.X b ∉ Grid.cIco r₀ s := by
  intro hmem
  have hunion := Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcyc
  rw [← hunion] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact hrect_avoid h
  · exact hpent_avoid h

end GridRectanglePentagonDecomposition

end TauCeti
