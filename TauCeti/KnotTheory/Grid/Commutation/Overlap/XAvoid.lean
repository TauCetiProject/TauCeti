/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Basic
public import TauCeti.KnotTheory.Grid.Commutation.Pentagon

/-!
# X-avoidance pieces for the overlap recut

When `recutLeftEqLeft` promotes the first recut rectangle to a pentagon via `ofRightEq`, the
new pentagon's `coveredSquares` include an extra strip `{finRotate n a} ×ˢ cIco bottom s`
beyond its underlying rectangle, where `bottom` is the recut's first rectangle's bottom row.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.recut_first_bottom_eq_pentagon_bottom_of_branch1`:
  in the first recut branch, the recut's first rectangle's bottom row equals the original
  pentagon's bottom row.
* `TauCeti.GridRectanglePentagonDecomposition.recut_X_not_mem_of_branch1`: X-avoidance for
  the `finRotate` strip in the first recut branch, from the original pentagon's X-avoidance.

-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {G : GridDiagram n}
variable {x z : GridState n}

/-- In the first recut branch, the recut's first rectangle's bottom row equals the original
pentagon's bottom row. -/
public theorem recut_first_bottom_eq_pentagon_bottom_of_branch1
    {a s : Fin n}
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hfirstLeft : (D.recutOfIsEmpty hone hrectangle hpentagon).first.left =
      D.toRectangleDecomposition.first.right) :
    (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom = D.pentagon.bottom := by
  have hnew : (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom =
      x D.toRectangleDecomposition.first.right := by
    have h1 : (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom =
        x ((D.recutOfIsEmpty hone hrectangle hpentagon).first.left) :=
      GridRectangleBetween.bottom_def _
    rw [h1, hfirstLeft]
  have hold : D.pentagon.bottom = x D.toRectangleDecomposition.first.right := by
    have h1 : D.pentagon.bottom = D.middle D.pentagon.left := rfl
    rw [h1, ← hcommon, D.rectangle.map_left, D.toRectangleDecomposition_first_right]
  rw [hnew, hold]

/-- X-avoidance for the `finRotate` strip in the first recut branch. -/
public theorem recut_X_not_mem_of_branch1
    {a s : Fin n}
    (D : GridRectanglePentagonDecomposition a s x z)
    (hcommon : D.rectangle.left = D.pentagon.left)
    (hone : D.toRectangleDecomposition.HasOneCommonSide)
    (hrectangle : D.rectangle.IsEmpty) (hpentagon : D.pentagon.IsEmpty)
    (hdisjoint : Disjoint D.pentagon.coveredSquares G.XSet)
    (hfirstLeft : (D.recutOfIsEmpty hone hrectangle hpentagon).first.left =
      D.toRectangleDecomposition.first.right) :
    G.X (finRotate n a) ∉
      Grid.cIco (D.recutOfIsEmpty hone hrectangle hpentagon).first.bottom s := by
  -- The bottoms coincide, so the pentagon's X-avoidance gives the strip avoidance directly
  -- via `disjoint_coveredSquares_XSet_iff`.
  have hbot := D.recut_first_bottom_eq_pentagon_bottom_of_branch1 hcommon hone
    hrectangle hpentagon hfirstLeft
  have hX' := hdisjoint
  rw [GridPentagonBetween.disjoint_coveredSquares_XSet_iff] at hX'
  obtain ⟨_, _, hXb⟩ := hX'
  rwa [hbot.symm] at hXb

/-
Application note (branch 1):

To show the `recutLeftEqLeft`-promoted pentagon is counted, apply
`GridPentagonBetween.disjoint_coveredSquares_XSet_iff` to both the original pentagon
(`Q := D.pentagon`, with `hX` from the pentagon's counted membership
(`((G.mem_pentagons D.pentagon).mp hpent).2`)) and the promoted pentagon `P`:
- `hcol`: from `Grid.cIco_subset_of_mem_cIoo hbranch` after rewriting the recut
  first rectangle's `left` via the branch-1 side equation and `hcommon`;
- `hbot`: `D.recut_first_bottom_eq_pentagon_bottom_of_branch1`;
- `htop`: both sides are the source state at `finRotate n C.column`, via
  `GridRectangleBetween.top_def`, `D.pentagon.right_eq`, and the fact that the
  column transposition defining `D.middle` fixes `finRotate n C.column`
  (`Equiv.swap_apply_of_ne_of_ne` with `D.pentagon.left_ne_right` and
  `Grid.ne_right_of_mem_cIoo hbranch`).

The promoted pentagon's `left`/`bottom`/`top` agree with the recut first
rectangle's by definition (`recutLeftEqLeft.eq_1` and `ofRightEq_toGridRectangleBetween`);
emptiness is `D.isEmpty_pentagon_recutLeftEqLeft`.  The final membership then follows
from `G.mem_pentagons`.
-/

end GridRectanglePentagonDecomposition

end TauCeti
