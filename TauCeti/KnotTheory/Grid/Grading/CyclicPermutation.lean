/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.MarkingCount
public import TauCeti.KnotTheory.Grid.Grading.Parity
public import TauCeti.KnotTheory.Grid.Rectangle.Relabeling

/-!
# The gradings under cyclic permutation

A grid diagram lives on a torus, and cyclically permuting its rows or its columns
(`GridDiagram.IsMove.cyclicRows`, `GridDiagram.IsMove.cyclicColumns`) only changes where the
torus is cut open into a square. This file shows that the gradings do not see the cut: relabeling
a grid state and the grid diagram by the same cyclic permutation `finRotate n` of the rows, or of
the columns, preserves both Maslov gradings and the Alexander grading.

The gradings are defined by pairing points in the cut-open square, so no single pairing term is
invariant. The proof instead compares grading differences. Across a rectangle from `x` to `y`, the
Maslov grading changes by `2 #(x ∩ r) - 1 - 2 #(𝕆 ∩ r)`, where `r` is the set of squares the
rectangle covers (`GridDiagram.maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card`).
A cyclic permutation carries rectangles to rectangles and rotates their covered squares together
with the state and the markings, so it preserves this change. Since any two grid states are
joined by rectangles (`GridState.rectangle_induction_on`), the two gradings differ by a constant,
and that constant is zero because the marking state `𝕆` has grading `1 - n` in every diagram
(`GridDiagram.maslovOℤ_O`).

## Main results

* `TauCeti.GridDiagram.maslovO_relabelRows_finRotate`,
  `TauCeti.GridDiagram.maslovX_relabelRows_finRotate`,
  `TauCeti.GridDiagram.alexander_relabelRows_finRotate`: the gradings are invariant under a
  cyclic permutation of the rows.
* `TauCeti.GridDiagram.maslovO_relabelColumns_finRotate`,
  `TauCeti.GridDiagram.maslovX_relabelColumns_finRotate`,
  `TauCeti.GridDiagram.alexander_relabelColumns_finRotate`: the same for the columns.
* `TauCeti.OddComponentGridDiagram.alexanderℤ_relabelRows_finRotate`,
  `TauCeti.OddComponentGridDiagram.alexanderℤ_relabelColumns_finRotate`: the integer Alexander
  grading is invariant under both cyclic permutations.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 4.3, where the gradings
are characterized by their changes across rectangles together with the normalization
`M_O(𝕆) = 1 - n`; the argument above uses exactly that characterization.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### Cyclic permutation of the rows -/

/-- A cyclic permutation of the rows rotates the squares a rectangle covers together with the
grid points of a state, so it preserves their number in common. -/
private theorem card_pointSet_inter_relabelRowsEquiv_finRotate {x y : GridState n}
    (R : GridRectangleBetween x y) (m : GridState n) :
    ((m.relabelRows (finRotate n)).pointSet ∩ (GridRectangleBetween.relabelRowsEquiv
        (finRotate n) x y R).toGridRectangle.coveredSquares).card =
      (m.pointSet ∩ R.toGridRectangle.coveredSquares).card := by
  refine (Finset.card_equiv ((Equiv.refl (Fin n)).prodCongr (finRotate n)) fun p ↦ ?_).symm
  simp only [Finset.mem_inter, GridState.mem_pointSet_relabelRows,
    GridRectangleBetween.mem_coveredSquares_relabelRowsEquiv_finRotate, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id, Equiv.symm_apply_apply]

/-- The `O`-Maslov grading is invariant under a cyclic permutation of the rows. -/
theorem maslovO_relabelRows_finRotate (x : GridState n) :
    (G.relabelRows (finRotate n)).maslovO (x.relabelRows (finRotate n)) = G.maslovO x := by
  refine GridState.eq_of_forall_sub_eq (f := fun x ↦ (G.relabelRows (finRotate n)).maslovO
    (x.relabelRows (finRotate n))) G.O ?_ (fun x y R ↦ ?_) x
  · simp only [← relabelRows_O, maslovO_eq_intCast, maslovOℤ_O]
  · simp only [maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card _
        (GridRectangleBetween.relabelRowsEquiv (finRotate n) x y R),
      maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card _ R, OSet, relabelRows_O,
      card_pointSet_inter_relabelRowsEquiv_finRotate]

/-- The `X`-Maslov grading is invariant under a cyclic permutation of the rows. -/
theorem maslovX_relabelRows_finRotate (x : GridState n) :
    (G.relabelRows (finRotate n)).maslovX (x.relabelRows (finRotate n)) = G.maslovX x := by
  refine GridState.eq_of_forall_sub_eq (f := fun x ↦ (G.relabelRows (finRotate n)).maslovX
    (x.relabelRows (finRotate n))) G.X ?_ (fun x y R ↦ ?_) x
  · simp only [← relabelRows_X, maslovX_eq_intCast, maslovXℤ_X]
  · simp only [maslovX_sub_maslovX_eq_two_mul_card_sub_one_sub_two_mul_card _
        (GridRectangleBetween.relabelRowsEquiv (finRotate n) x y R),
      maslovX_sub_maslovX_eq_two_mul_card_sub_one_sub_two_mul_card _ R, XSet, relabelRows_X,
      card_pointSet_inter_relabelRowsEquiv_finRotate]

/-- The Alexander grading is invariant under a cyclic permutation of the rows. -/
theorem alexander_relabelRows_finRotate (x : GridState n) :
    (G.relabelRows (finRotate n)).alexander (x.relabelRows (finRotate n)) = G.alexander x := by
  rw [alexander_def, alexander_def, maslovO_relabelRows_finRotate, maslovX_relabelRows_finRotate]

/-! ### Cyclic permutation of the columns -/

/-- A cyclic permutation of the columns rotates the squares a rectangle covers together with the
grid points of a state, so it preserves their number in common. -/
private theorem card_pointSet_inter_relabelColumnsEquiv_finRotate {x y : GridState n}
    (R : GridRectangleBetween x y) (m : GridState n) :
    ((m.relabelColumns (finRotate n)).pointSet ∩ (GridRectangleBetween.relabelColumnsEquiv
        (finRotate n) x y R).toGridRectangle.coveredSquares).card =
      (m.pointSet ∩ R.toGridRectangle.coveredSquares).card := by
  refine (Finset.card_equiv ((finRotate n).prodCongr (Equiv.refl (Fin n))) fun p ↦ ?_).symm
  simp only [Finset.mem_inter, GridState.mem_pointSet_relabelColumns,
    GridRectangleBetween.mem_coveredSquares_relabelColumnsEquiv_finRotate, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id, Equiv.symm_apply_apply]

/-- The `O`-Maslov grading is invariant under a cyclic permutation of the columns. -/
theorem maslovO_relabelColumns_finRotate (x : GridState n) :
    (G.relabelColumns (finRotate n)).maslovO (x.relabelColumns (finRotate n)) = G.maslovO x := by
  refine GridState.eq_of_forall_sub_eq (f := fun x ↦ (G.relabelColumns (finRotate n)).maslovO
    (x.relabelColumns (finRotate n))) G.O ?_ (fun x y R ↦ ?_) x
  · simp only [← relabelColumns_O, maslovO_eq_intCast, maslovOℤ_O]
  · simp only [maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card _
        (GridRectangleBetween.relabelColumnsEquiv (finRotate n) x y R),
      maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card _ R, OSet, relabelColumns_O,
      card_pointSet_inter_relabelColumnsEquiv_finRotate]

/-- The `X`-Maslov grading is invariant under a cyclic permutation of the columns. -/
theorem maslovX_relabelColumns_finRotate (x : GridState n) :
    (G.relabelColumns (finRotate n)).maslovX (x.relabelColumns (finRotate n)) = G.maslovX x := by
  refine GridState.eq_of_forall_sub_eq (f := fun x ↦ (G.relabelColumns (finRotate n)).maslovX
    (x.relabelColumns (finRotate n))) G.X ?_ (fun x y R ↦ ?_) x
  · simp only [← relabelColumns_X, maslovX_eq_intCast, maslovXℤ_X]
  · simp only [maslovX_sub_maslovX_eq_two_mul_card_sub_one_sub_two_mul_card _
        (GridRectangleBetween.relabelColumnsEquiv (finRotate n) x y R),
      maslovX_sub_maslovX_eq_two_mul_card_sub_one_sub_two_mul_card _ R, XSet, relabelColumns_X,
      card_pointSet_inter_relabelColumnsEquiv_finRotate]

/-- The Alexander grading is invariant under a cyclic permutation of the columns. -/
theorem alexander_relabelColumns_finRotate (x : GridState n) :
    (G.relabelColumns (finRotate n)).alexander (x.relabelColumns (finRotate n)) =
      G.alexander x := by
  rw [alexander_def, alexander_def, maslovO_relabelColumns_finRotate,
    maslovX_relabelColumns_finRotate]

end GridDiagram

namespace OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-- The integer Alexander grading is invariant under a cyclic permutation of the rows. -/
@[simp]
theorem alexanderℤ_relabelRows_finRotate (x : GridState n) :
    (G.relabelRows (finRotate n)).alexanderℤ (x.relabelRows (finRotate n)) = G.alexanderℤ x := by
  have h := G.1.alexander_relabelRows_finRotate x
  rw [← val_relabelRows, alexander_eq_intCast, alexander_eq_intCast] at h
  exact_mod_cast h

/-- The integer Alexander grading is invariant under a cyclic permutation of the columns. -/
@[simp]
theorem alexanderℤ_relabelColumns_finRotate (x : GridState n) :
    (G.relabelColumns (finRotate n)).alexanderℤ (x.relabelColumns (finRotate n)) =
      G.alexanderℤ x := by
  have h := G.1.alexander_relabelColumns_finRotate x
  rw [← val_relabelColumns, alexander_eq_intCast, alexander_eq_intCast] at h
  exact_mod_cast h

end OddComponentGridDiagram

end TauCeti
