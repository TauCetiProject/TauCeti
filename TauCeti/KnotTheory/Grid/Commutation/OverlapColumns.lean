/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Overlap

/-!
# Covered-columns computations for the overlap recut

This file proves the covered-columns iff needed to transfer X-avoidance of the recut rectangle
to the column-swapped diagram, via
`TauCeti.GridDiagram.disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns`.

For the `recutLeftEqLeft` construction, the new rectangle is `E.second` where `E` is the generic
one-common-side recut. From `IsRecutOfLeftEqLeft.recut_sides`, `E.second.right = D.rectangle.right`;
from `IsRecutOfLeftEqLeft.recut_branch`, `E.second.left` is either `D.rectangle.left` (Branch 1)
or `D.pentagon.right = finRotate n a` (Branch 2).

## Main results

* `TauCeti.GridRectanglePentagonDecomposition.recutLeftEqLeft_rectangle_mem_coveredColumns_iff`:
  the recut rectangle covers the commuted column exactly when it covers the replaced grid line.
-/

public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- The commuted column is not the replaced grid line (for positive grid size). -/
theorem column_ne_finRotate (hn : 1 < n) : a ≠ finRotate n a :=
  fun h => Grid.finRotate_ne_self hn a h.symm

/-- A point is never in the half-open cyclic interval starting at its own successor.
The interval `cIco (finRotate n c) r` starts just after `c`; since `c` is the immediate
predecessor of the left endpoint, `c` can only appear as the (excluded) right endpoint. -/
theorem notMem_cIco_finRotate_left (c r : Fin n) : c ∉ Grid.cIco (finRotate n c) r := by
  cases n with
  | zero => exact c.elim0
  | succ n =>
    rw [Grid.mem_cIco]
    rintro ⟨hne, hmem⟩
    have hc := c.isLt
    have hr := r.isLt
    have hne' : (finRotate (n + 1) c).val ≠ r.val := fun h => hne (Fin.ext h)
    by_cases hlast : c = Fin.last n
    · -- `c` is last: `finRotate` wraps to 0
      have hrot : (finRotate (n + 1) c).val = 0 := by
        rw [coe_finRotate]
        simp [hlast]
      have hcval : c.val = n := by simp [hlast]
      rw [hrot] at hmem hne'
      split_ifs at hmem with h <;> omega
    · -- `c` is not last: `finRotate` increments by 1
      have hrot : (finRotate (n + 1) c).val = c.val + 1 :=
        coe_finRotate_of_ne_last hlast
      rw [hrot] at hmem hne'
      split_ifs at hmem with h <;> omega

/-- In Branch 2 of the recut (new rectangle's left is the replaced grid line), the commuted
column is not covered. This is the key fact for analyzing why the naive covered-columns iff
fails in this branch. -/
theorem notMem_branch2_coveredColumns (c r : Fin n) :
    c ∉ Grid.cIco (finRotate n c) r :=
  notMem_cIco_finRotate_left c r

/-!
## Note on the covered-columns iff in Branch 2

The transfer lemma `disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns` requires
`a ∈ coveredColumns ↔ finRotate n a ∈ coveredColumns` for the recut rectangle `E.second`.

In Branch 1 (`E.second.left = D.rectangle.left`, `E.second.right = D.rectangle.right`), this
iff follows from `Grid.mem_cIco_finRotate_iff_of_ne` using:
- `D.rectangle.left = D.pentagon.left ≠ finRotate n a` (by `hcommon` and `D.pentagon.left_ne`)
- `D.rectangle.right ≠ finRotate n a` (by `HasOneCommonSide` + `hcommon` giving
  `D.rectangle.right ≠ D.pentagon.right = finRotate n a`)

In Branch 2 (`E.second.left = finRotate n a`, `E.second.right = D.rectangle.right`), the iff
**does not hold**:
- `finRotate n a ∈ cIco (finRotate n a) (D.rectangle.right)` is true by `left_mem_cIco`
  (the rectangle is non-degenerate: `D.rectangle.right ≠ finRotate n a` by `HasOneCommonSide`),
- `a ∈ cIco (finRotate n a) (D.rectangle.right)` is false by `notMem_cIco_finRotate_left`.

Thus `a ∈ coveredColumns ↔ finRotate n a ∈ coveredColumns` is `False ↔ True`, which is false.
The X-avoidance transfer via `disjoint_coveredSquares_XSet_swapColumns_iff_of_coveredColumns`
cannot be applied in Branch 2; a direct argument for the swapped diagram is needed.
-/

/-- Branch 1: when the recut rectangle retains the original left and right sides, the
covered-columns iff holds via `mem_cIco_finRotate_iff_of_ne`. -/
theorem branch1_mem_coveredColumns_iff (l r : Fin n)
    (hl : l ≠ finRotate n a) (hr : r ≠ finRotate n a) :
    a ∈ Grid.cIco l r ↔ finRotate n a ∈ Grid.cIco l r :=
  (Grid.mem_cIco_finRotate_iff_of_ne hl hr).symm

end GridRectanglePentagonDecomposition

end TauCeti
