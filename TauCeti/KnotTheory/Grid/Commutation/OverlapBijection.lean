/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap

/-!
# Branch-1 pentagon X-avoidance transfer

Given an X-avoiding pentagon `Q`, a pentagon `P` whose column interval sits inside `Q`'s
column interval, and whose bottom and top rows agree with `Q`'s, inherits `Q`'s
X-avoidance.

## Mathematical context

The overlap-case chain map needs a bijection between counted rectangle-pentagon
decompositions `D` (with `HasOneCommonSide` on the left) and counted pentagon-rectangle
decompositions `E` in the swapped diagram. The forward map is `D.recutLeftEqLeft`, which
repartitions the union of the old rectangle and old pentagon into a new rectangle
`E.rectangle` and a new pentagon `E.pentagon`.

This module proves the branch-1 pentagon piece: in recut branch 1, the new pentagon
`E.pentagon` is X-avoiding. (Countedness additionally needs emptiness, proved as
`D.isEmpty_pentagon_recutLeftEqLeft` in `Overlap`.) The proof applies
`GridPentagonBetween.disjoint_coveredSquares_XSet_iff` on both sides: the side-column clause
transfers through the column inclusion, while the column-`a` and column-`b` clauses are
literally the old ones once the rows agree.

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.pentagon_disjoint_XSet_of_branch1_data`: the
  branch-1 pentagon X-avoidance transfer, from an old pentagon's X-avoidance alone.

-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {G : GridDiagram n} {C : GridDiagram.ColumnCommutationData G}
variable {x y z : GridState n}

open Grid

/-- Branch-1 `X`-avoidance transfer for a pentagon built on a recut first rectangle.

This is the geometric core of counted-ness in branch 1.  If `P` is a pentagon
whose column interval sits inside an `X`-avoiding pentagon `Q`'s (`hcol`), and whose
bottom and top rows agree with `Q`'s (`hbot`, `htop`), then `P` inherits `X`-avoidance
from `Q`.

Only `Q`'s `X`-avoidance is used: neither its counted membership nor any data from the
ambient rectangle-pentagon decomposition.

The proof applies `GridPentagonBetween.disjoint_coveredSquares_XSet_iff` on both
sides: the side-column clause transfers through the column inclusion, while the
column-`a` and column-`b` clauses are literally the old ones once the rows agree.
-/
public theorem pentagon_disjoint_XSet_of_branch1_data
    {a s : Fin n} {u v : GridState n}
    (Q : GridPentagonBetween a s u v)
    (hX : Disjoint Q.coveredSquares G.XSet)
    (P : GridPentagonBetween a s x y)
    (hcol : cIco P.left (finRotate n a) ⊆ cIco Q.left (finRotate n a))
    (hbot : P.bottom = Q.bottom)
    (htop : P.top = Q.top) :
    Disjoint P.coveredSquares G.XSet := by
  rw [GridPentagonBetween.disjoint_coveredSquares_XSet_iff] at hX ⊢
  rw [hbot, htop]
  obtain ⟨ha, hb, hc⟩ := hX
  exact ⟨fun c hcne hcmem => ha c hcne (hcol hcmem), hb, hc⟩

/-
Application note (branch 1):

To show the `recutLeftEqLeft`-promoted pentagon is counted, apply
`pentagon_disjoint_XSet_of_branch1_data` with `Q := D.pentagon` and `hX` from the
pentagon's counted membership (`((G.mem_pentagons D.pentagon).mp hpent).2`):
- `hcol`: from `Grid.cIco_subset_of_mem_cIoo hbranch` after rewriting the recut
  first rectangle's `left` via the branch-1 side equation and `hcommon`;
- `hbot`: `D.recut_first_bottom_eq_pentagon_bottom_of_branch1` (in `OverlapXAvoid`);
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
