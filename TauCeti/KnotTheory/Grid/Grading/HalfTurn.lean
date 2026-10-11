/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.JFunction.Diagonal
public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
public import TauCeti.KnotTheory.Grid.Grading.Parity
public import TauCeti.KnotTheory.Grid.Rectangle.Relabeling

/-!
# The Alexander grading under the half-turn

The half-turn moves marking squares by `Fin.rev` and grid points by negation modulo the
grid size. These different coordinate maps preserve the absolute Alexander grading.
Consequently the half-turn equivalence on grid homology can be used in grading-sensitive
arguments, such as comparison of the two corner types of stabilization.

Rectangle grading changes are preserved because the half-turn preserves covered marking
counts. The additive constant is fixed at the diagonal state: its marking pairing is
invariant under reversal of the marking coordinates, as are the marking self-pairings.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 5.2.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The half-turn of a diagram and a grid state preserves the absolute Alexander grading. -/
theorem alexander_rotate_halfTurn (x : GridState n) :
    G.rotate.alexander x.halfTurn = G.alexander x := by
  have hdiag (c : Fin n) : (GridState.mk 1 : GridState n) c = c := rfl
  have hhalf : (GridState.mk 1 : GridState n).halfTurn = GridState.mk 1 := by
    ext c
    rw [GridState.halfTurn_apply, hdiag, Fin.finRotate_rev_finRotate_rev]
    rw [hdiag]
  have hbase : G.rotate.alexander (GridState.mk 1).halfTurn =
      G.alexander (GridState.mk 1) := by
    rw [hhalf, alexander_eq, alexander_eq]
    simp only [JO_def, JX_def, OSet_def, XSet_def, rotate_O, rotate_X,
      GridState.JCenter_diagonal_rotate, GridState.J_rotate]
  refine GridState.eq_of_forall_sub_eq (f := fun x => G.rotate.alexander x.halfTurn)
    (GridState.mk 1) hbase (fun u v R => ?_) x
  have hchange := G.rotate.alexander_sub_alexander_eq_card_sub_card
    (GridRectangleBetween.halfTurnEquiv u v R)
  rw [OSet_def, XSet_def, rotate_O, rotate_X,
    GridRectangleBetween.card_pointSet_inter_halfTurnEquiv,
    GridRectangleBetween.card_pointSet_inter_halfTurnEquiv] at hchange
  have horiginal := G.alexander_sub_alexander_eq_card_sub_card R
  rw [OSet_def, XSet_def] at horiginal
  exact hchange.trans horiginal.symm

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-- The half-turn preserves the integer Alexander grading. -/
@[simp]
theorem alexanderℤ_rotate_halfTurn (x : GridState n) :
    G.rotate.alexanderℤ x.halfTurn = G.alexanderℤ x := by
  have h := G.1.alexander_rotate_halfTurn x
  rw [← G.val_rotate, alexander_eq_intCast, alexander_eq_intCast] at h
  exact_mod_cast h

end OddComponentGridDiagram

end TauCeti
