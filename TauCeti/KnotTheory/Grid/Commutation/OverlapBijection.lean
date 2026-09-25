module

public import TauCeti.KnotTheory.Grid.Commutation.OverlapXAvoid
public import TauCeti.KnotTheory.Grid.Commutation.OverlapColumns
public import TauCeti.KnotTheory.Grid.Commutation.OverlapBranch2

/-!
# Overlap bijection: counted-ness assembly for the recut

This module assembles the overlap-side counted-ness: the pentagon produced by
`GridRectanglePentagonDecomposition.recutLeftEqLeft` is counted (empty and
`X`-avoiding) in the original diagram.

## Mathematical context

The overlap-case chain map needs a bijection between counted
rectangle-pentagon decompositions `D` (with `HasOneCommonSide` on the left)
and counted pentagon-rectangle decompositions `E` in the swapped diagram.
The forward map is `D.recutLeftEqLeft`, which repartitions the union of the
old rectangle and old pentagon into a new rectangle `E.rectangle` and a new
pentagon `E.pentagon`.

This module proves the first piece: **in recut branch 1** (the new first
rectangle's initial side is the old rectangle's terminal side), the new
pentagon `E.pentagon` is `X`-avoiding, hence counted.  The proof transfers
`X`-avoidance from the old counted pentagon through three facts:

* the new first rectangle's columns sit strictly inside the old pentagon's
  column interval (`Grid.cIco_subset_of_mem_cIoo`),
* the new first rectangle's bottom row equals the old pentagon's
  (`recut_first_bottom_eq_pentagon_bottom_of_branch1`),
* the new first rectangle's top row equals the old pentagon's (the source
  state is unchanged at the common terminal column `b`, since the column
  transposition fixes `b`).

The key tool is `GridPentagonBetween.disjoint_coveredSquares_XSet_iff`, which
splits pentagon `X`-avoidance into a side-column part (handled by the column
inclusion), a column-`a` part (identical on both sides once the tops agree),
and a column-`b` part (identical on both sides once the bottoms agree).

## Status of the remaining assembly

* Branch-1 rectangle counted-ness: needs `Disjoint` for the new rectangle's
  underlying squares in the original diagram (row containment
  `cIco E.second.bottom E.second.top ⊆ cIco D.rectangle.bottom D.rectangle.top`,
  forced by emptiness), then the covered-columns transfer
  (`branch1_mem_coveredColumns_iff`).
* Branch-2 pentagon `X`-avoidance: needs the two cyclic-interval lemmas
  identified in `OverlapBranch2` (`cIoo` rotation and half-open covering).
* Branch-2 rectangle counted-ness: `branch2_direct_X_avoidance` is proved;
  the covered-columns transfer is unavailable in branch 2 (the iff is false
  there), so the swapped-diagram avoidance must be proved directly.
* Weight preservation: `OverlapWeight` has the added-strip helper; the
  correction-equals-one computation and the final weight identity are open.
* The reverse overlap map / involution and the finite-sum identity are open.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {G : GridDiagram n} {C : GridDiagram.ColumnCommutationData G}
variable {x y z : GridState n}

open Grid

/-- Branch-1 `X`-avoidance transfer for a pentagon built on a recut first rectangle.

This is the geometric core of counted-ness in branch 1.  If `P` is a pentagon
whose column interval sits inside the old pentagon's (`hcol`), and whose bottom
and top rows agree with the old pentagon's (`hbot`, `htop`), then `P` inherits
`X`-avoidance from the old counted pentagon `D.pentagon`.

The proof applies `GridPentagonBetween.disjoint_coveredSquares_XSet_iff` on both
sides: the side-column clause transfers through the column inclusion, while the
column-`a` and column-`b` clauses are literally the old ones once the rows agree.
-/
public theorem pentagon_disjoint_XSet_of_branch1_data
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    (P : GridPentagonBetween C.column C.turnRow x y)
    (hcol : cIco P.left (finRotate n C.column) ⊆
      cIco D.pentagon.left (finRotate n C.column))
    (hbot : P.bottom = D.pentagon.bottom)
    (htop : P.top = D.pentagon.top) :
    Disjoint P.coveredSquares G.XSet := by
  have hDpent : D.pentagon ∈ G.pentagons C D.middle z :=
    ((G.mem_rectanglePentagonDecompositions C D).mp hD).2
  have hdisj : Disjoint D.pentagon.coveredSquares G.XSet :=
    ((G.mem_pentagons D.pentagon).mp hDpent).2
  rw [GridPentagonBetween.disjoint_coveredSquares_XSet_iff] at hdisj ⊢
  rw [hbot, htop]
  obtain ⟨ha, hb, hc⟩ := hdisj
  exact ⟨fun c hcne hcmem => ha c hcne (hcol hcmem), hb, hc⟩

/-
Application note (branch 1):

To show the `recutLeftEqLeft`-promoted pentagon is counted, apply
`pentagon_disjoint_XSet_of_branch1_data` with:
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
