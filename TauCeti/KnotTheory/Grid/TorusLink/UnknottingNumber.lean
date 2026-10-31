/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.TorusLink.FullTwist

/-!
# Unknotting numbers of torus link grids

This file bounds the unknotting number (`GridLink.unknottingNumber`) of the grid links presented
by the standard torus link grids. The Hopf link has unknotting number `⊤`, since it has two
components. Removing a full twist on `P` strands costs at most `P choose 2` crossing changes
(`GridLink.crossingChangeGraph_edist_torusLink_add_le`), so the `(P, k P + 1)` torus knot is
unknotted by `k (P choose 2) = (P - 1) ((k P + 1) - 1) / 2` crossing changes: the upper bound
`u(T_{P,Q}) ≤ (P - 1) (Q - 1) / 2` of the Milnor conjecture for `Q ≡ 1 mod P`. This covers the
`(3, 4)` torus knot, unknotted by three crossing changes.

For two strands a full twist is one explicit crossing change in the standard grid of every
size. Exchanging the first two columns of the standard grid of the `(2, q + 3)` torus link is a
cross-commutation, and the resulting diagram is obtained from the standard grid of the
`(2, q + 1)` torus link by two `X`-stabilizations, up to a cyclic permutation of the columns and
row commutations. The `(2, 2k + 1)` torus knot has unknotting number at most `k`, the case `P = 2`
of the general bound.

The unknotting number of the standard torus link grid is symmetric in the two winding numbers
(`GridLink.unknottingNumber_toGridLink_torusLink_comm`): the standard grids of the `(p + 1, q + 1)`
and `(q + 1, p + 1)` torus links are diagonal reflections of each other
(`GridDiagram.transpose_torusLink`), and the reflection of grid links preserves unknotting numbers
(`GridLink.unknottingNumber_transpose`). So every bound proved here also holds with the two
winding numbers exchanged. In particular the `(2 k + 1, 2)` torus knot has unknotting number at
most `k`.

## Main results

* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_one`: the Hopf link has unknotting
  number `⊤`.
* `TauCeti.GridLink.isCrossingChange_toGridLink_torusLink_one_add_two`: the `(2, q + 3)` and
  `(2, q + 1)` torus links differ by one crossing change.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_add_le`: removing a full twist from a
  torus link grid lowers the unknotting number by at most `P choose 2`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_mul_le`: the `(P, k P + 1)` torus knot
  has unknotting number at most `k (P choose 2)`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_mul_le`: the `(2, 2k + 1)`
  torus knot has unknotting number at most `k`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three_le_three`: the `(3, 4)` torus
  knot has unknotting number at most three.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_comm`: the unknotting number of the
  standard `(p + 1, q + 1)` torus link grid equals that of the `(q + 1, p + 1)` one.
* `TauCeti.GridLink.isCrossingChange_toGridLink_torusLink_add_two_one`: the `(q + 3, 2)` and
  `(q + 1, 2)` torus links differ by one crossing change.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_mul_one_le`: the `(2 k + 1, 2)` torus
  knot has unknotting number at most `k`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6: crossing changes as cross-commutations and the unknotting
  number; Chapter 3: commutation and stabilization moves.
-/

public section

namespace TauCeti

namespace GridDiagram

/-! ### A crossing change between the `(2, q + 3)` and `(2, q + 1)` torus link grids -/

variable (q : ℕ)

/-- In the standard grid of the `(2, q + 1)` torus link the `X`-marking of column `c` sits in row
`c + q + 1` for `c ≤ 1` and in row `c - 2` otherwise. -/
private theorem torusLink_one_X_val (c : Fin (1 + 1 + (q + 1))) :
    ((torusLink 1 q).X c : ℕ) = if (c : ℕ) ≤ 1 then c + (q + 1) else c - 2 := by
  split_ifs with h
  · exact torusLink_X_val_of_le 1 q h
  · exact torusLink_X_val_of_lt 1 q (by omega)

/-- The `O`-markings of the `X`-stabilization of the `(2, q + 1)` torus link grid that splits the
`X`-marking of column `1` with new column `1` and new row `0`: the `O`-markings of the first two
columns are exchanged, and the others stay on the diagonal. -/
private theorem stabilizeX_torusLink_one_O_val (j : Fin (1 + 1 + (q + 1) + 1)) :
    (((torusLink 1 q).stabilizeX 1 0 1).O j : ℕ) =
      if (j : ℕ) = 0 then 1 else if (j : ℕ) = 1 then 0 else j := by
  have h1 := Fin.val_one_of_two_le (m := 1 + 1 + (q + 1) + 1) (by omega)
  rw [stabilizeX_O]
  induction j using Fin.succAboveCases 1 with
  | x => simp
  | p i =>
    rw [GridState.insertPoint_apply_succAbove, torusLink_O_apply]
    simp only [Fin.succAbove, Fin.lt_def, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
      Fin.val_zero, h1]
    split_ifs <;> first | omega | contradiction

/-- The `X`-markings of the same stabilization: the first two columns carry them in the two top
rows, and every other column carries it two rows below the diagonal. -/
private theorem stabilizeX_torusLink_one_X_val (j : Fin (1 + 1 + (q + 1) + 1)) :
    (((torusLink 1 q).stabilizeX 1 0 1).X j : ℕ) =
      if (j : ℕ) = 0 then q + 2 else if (j : ℕ) = 1 then q + 3 else j - 2 := by
  have h1 := Fin.val_one_of_two_le (m := 1 + 1 + (q + 1) + 1) (by omega)
  have h1' := Fin.val_one_of_two_le (m := 1 + 1 + (q + 1)) (by omega)
  rw [stabilizeX_X]
  induction j using Fin.succAboveCases 1 with
  | x =>
    rw [GridState.splitPoint_apply_newColumn]
    simp only [Fin.succAbove, Fin.lt_def, apply_ite Fin.val, Fin.val_castSucc, Fin.val_succ,
      Fin.val_zero, h1, torusLink_one_X_val, h1']
    split_ifs <;> first | omega | contradiction
  | p i =>
    rw [GridState.splitPoint_apply_succAbove]
    have hi := i.isLt
    by_cases h : i = 1
    · subst h
      simp only [ite_true, Fin.succAbove, Fin.lt_def, apply_ite Fin.val, Fin.val_castSucc,
        Fin.val_succ, Fin.val_zero, h1, h1']
      split_ifs <;> omega
    · have h' : (i : ℕ) ≠ 1 := fun h'' => h (Fin.ext (by rw [h'', h1']))
      simp only [h, ite_false, Fin.succAbove, Fin.lt_def, apply_ite Fin.val, Fin.val_castSucc,
        Fin.val_succ, Fin.val_zero, h1, torusLink_one_X_val]
      split_ifs <;> first | omega | contradiction

/-- Exchanging the first two columns of the `(2, q + 3)` torus link grid gives a twofold
`X`-stabilization of the `(2, q + 1)` torus link grid: first split the `X`-marking of column `1`,
then that of column `0`, with the new row and column at the top and right edge. -/
private theorem stabilizeX_stabilizeX_torusLink_one :
    ((torusLink 1 q).stabilizeX 1 0 1).stabilizeX (Fin.last _) (Fin.last _) 0 =
      (torusLink 1 (q + 2)).swapColumns 0 1 := by
  have h1 := Fin.val_one_of_two_le (m := 1 + 1 + (q + 2 + 1)) (by omega)
  have h0 : ((0 : Fin (1 + 1 + (q + 2 + 1))) : ℕ) = 0 := rfl
  refine GridDiagram.ext (GridState.ext fun c => Fin.ext ?_) (GridState.ext fun c => Fin.ext ?_)
  · rw [stabilizeX_O, swapColumns_O, GridState.swapColumns_apply, torusLink_O_apply,
      Equiv.swap_apply_def]
    induction c using Fin.lastCases with
    | last =>
      rw [GridState.insertPoint_apply_newColumn]
      simp only [apply_ite Fin.val, Fin.ext_iff, Fin.val_last, h0, h1]
      split_ifs <;> first | omega | contradiction
    | cast j =>
      have hj := j.isLt
      rw [← Fin.succAbove_last_apply, GridState.insertPoint_apply_succAbove,
        Fin.succAbove_last_apply, Fin.val_castSucc, stabilizeX_torusLink_one_O_val]
      simp only [apply_ite Fin.val, Fin.ext_iff, Fin.val_castSucc, Fin.succAbove_last_apply, h0,
        h1]
      split_ifs <;> first | omega | rfl
  · rw [stabilizeX_X, swapColumns_X, GridState.swapColumns_apply, torusLink_one_X_val,
      Equiv.swap_apply_def]
    induction c using Fin.lastCases with
    | last =>
      rw [GridState.splitPoint_apply_newColumn, Fin.succAbove_last_apply, Fin.val_castSucc,
        stabilizeX_torusLink_one_X_val]
      simp only [apply_ite Fin.val, Fin.ext_iff, Fin.val_last, h0, h1]
      split_ifs <;> first | omega | contradiction
    | cast j =>
      have hj := j.isLt
      rw [← Fin.succAbove_last_apply, GridState.splitPoint_apply_succAbove,
        Fin.succAbove_last_apply]
      by_cases hj0 : j = 0
      · subst hj0
        simp only [ite_true, Fin.val_last, apply_ite Fin.val, Fin.ext_iff, Fin.val_castSucc,
          Fin.succAbove_last_apply, h0, h1]
        split_ifs <;> first | omega | contradiction
      · have hj0' : (j : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
        simp only [hj0, ↓reduceIte]
        rw [Fin.succAbove_last_apply, Fin.val_castSucc, stabilizeX_torusLink_one_X_val]
        simp only [apply_ite Fin.val, Fin.ext_iff, Fin.val_castSucc, h0, h1]
        split_ifs <;> omega

/-- The first two columns of the `(2, q + 3)` torus link grid interleave. -/
private theorem columnsInterleaving_torusLink_one_zero :
    (torusLink 1 (q + 2)).ColumnsInterleaving 0 (finRotate _ 0) := by
  have h1 := Fin.val_one_of_two_le (m := 1 + 1 + (q + 2 + 1)) (by omega)
  have hX0 := torusLink_X_val_of_le 1 (q + 2) (c := 0) (by simp)
  have hX1 := torusLink_X_val_of_le 1 (q + 2) (c := 1) h1.le
  have hr : finRotate (1 + 1 + (q + 2 + 1)) 0 = 1 := finRotate_apply_zero
  rw [hr, columnsInterleaving_iff, mem_columnArc, mem_columnArc]
  right
  simp only [Grid.mem_cIoo, torusLink_O_apply, ne_eq, Fin.ext_iff, h1, Fin.val_zero] at hX0 hX1 ⊢
  rw [hX0, hX1]
  split_ifs <;> omega

/-- Exchanging the first two columns of the `(2, q + 3)` torus link grid gives a diagram of the
`(2, q + 1)` torus link. -/
private theorem movesTo_swapColumns_torusLink_one :
    ((torusLink 1 (q + 2)).swapColumns 0 1).MovesTo (torusLink 1 q) := by
  set H₁ := (torusLink 1 q).stabilizeX 1 0 1
  have h₁ : (1 : Fin (1 + 1 + (q + 1))).castSucc = 1 := by
    ext
    rw [Fin.val_castSucc, Fin.val_one_of_two_le (by omega), Fin.val_one_of_two_le (by omega)]
  -- The cyclic permutation of the columns moves the new last column of the second stabilization
  -- to the front, next to the split column `0`; the new row then slides down by commutations
  -- to the elementary stabilization.
  have h₂ : (H₁.stabilizeX (Fin.last _) (Fin.last _) 0).MovesTo H₁ := by
    refine (cyclicColumns_movesTo _).trans ?_
    rw [stabilizeX_last_relabelColumns, ← Fin.castSucc_zero]
    exact H₁.movesTo_stabilizeX_castSucc 0 _
  -- The same slide for the first stabilization, whose new column `1` precedes the split column.
  have h₃ : H₁.MovesTo (torusLink 1 q) := by
    simp only [H₁, ← h₁]
    exact (torusLink 1 q).movesTo_stabilizeX_castSucc 1 _
  rw [← stabilizeX_stabilizeX_torusLink_one]
  exact h₂.trans h₃

end GridDiagram

namespace GridLink

/-- The Hopf link, presented by the standard `4 × 4` grid of the `(2, 2)` torus link, has
unknotting number `⊤`: it has two components, so no sequence of crossing changes reaches the
unknot. -/
theorem unknottingNumber_toGridLink_torusLink_one_one :
    (GridDiagram.torusLink 1 1).toGridLink.unknottingNumber = ⊤ := by
  by_contra h
  have := isKnot_of_unknottingNumber_ne_top h
  rw [isKnot_toGridLink] at this
  exact GridDiagram.not_isKnot_torusLink_one_one this

/-- The `(2, q + 3)` and `(2, q + 1)` torus links differ by one crossing change: exchanging the
first two columns of the standard grid of the former is a cross-commutation, and the result is a
twofold stabilization of the standard grid of the latter, up to commutation and cyclic
permutation. -/
theorem isCrossingChange_toGridLink_torusLink_one_add_two (q : ℕ) :
    IsCrossingChange (GridDiagram.torusLink 1 (q + 2)).toGridLink
      (GridDiagram.torusLink 1 q).toGridLink := by
  have h := (GridDiagram.torusLink 1 (q + 2)).isColumnCrossCommutation_swapColumns
    (GridDiagram.columnsInterleaving_torusLink_one_zero q)
  have hr : finRotate (1 + 1 + (q + 2 + 1)) 0 = 1 := finRotate_apply_zero
  rw [hr] at h
  exact (isCrossingChange_iff _ _).mpr
    ⟨_, _, _, (GridDiagram.isCrossCommutation_iff _ _).mpr (Or.inr h), rfl,
      (GridDiagram.toGridLink_eq_iff_movesTo _).mpr
        (GridDiagram.movesTo_swapColumns_torusLink_one q)⟩

/-- Removing a full twist: the unknotting number of the grid link of the standard
`(p + 1, (q + (p + 1)) + 1)` torus link grid exceeds that of the `(p + 1, q + 1)` torus link grid
by at most `(p + 1) choose 2`. -/
theorem unknottingNumber_toGridLink_torusLink_add_le (p q : ℕ) :
    (GridDiagram.torusLink p (q + (p + 1))).toGridLink.unknottingNumber ≤
      (p + 1).choose 2 + (GridDiagram.torusLink p q).toGridLink.unknottingNumber := by
  rw [unknottingNumber_def, unknottingNumber_def]
  exact SimpleGraph.edist_triangle.trans
    (by gcongr; exact crossingChangeGraph_edist_torusLink_add_le p q)

/-- The `(p + 1, k (p + 1) + 1)` torus knot, presented by its standard grid, has unknotting number
at most `k ((p + 1) choose 2)`. This is the upper bound `u(T_{P,Q}) ≤ (P - 1) (Q - 1) / 2` of the
Milnor conjecture for `P = p + 1` and `Q = k P + 1`: each of the `k` full twists is removed by
`P choose 2` crossing changes, and the `(p + 1, 1)` torus link grid is the standard unknot grid. -/
theorem unknottingNumber_toGridLink_torusLink_mul_le (p k : ℕ) :
    (GridDiagram.torusLink p (k * (p + 1))).toGridLink.unknottingNumber ≤ k * (p + 1).choose 2 := by
  induction k with
  | zero =>
    rw [Nat.zero_mul, GridDiagram.torusLink_zero_right, GridDiagram.toGridLink_unknot,
      unknottingNumber_unknot]
    exact zero_le
  | succ k ih =>
    rw [Nat.succ_mul]
    calc _ ≤ _ := unknottingNumber_toGridLink_torusLink_add_le p (k * (p + 1))
      _ ≤ (p + 1).choose 2 + k * (p + 1).choose 2 := by gcongr
      _ = (k + 1) * (p + 1).choose 2 := by ring

/-- The `(2, 2k + 1)` torus knot, presented by its standard grid, has unknotting number at most
`k`: this is the upper bound `u(T_{2, 2k+1}) ≤ (2 - 1) (2k + 1 - 1) / 2` of the Milnor
conjecture, the case `P = 2` of `unknottingNumber_toGridLink_torusLink_mul_le`. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_mul_le (k : ℕ) :
    (GridDiagram.torusLink 1 (2 * k)).toGridLink.unknottingNumber ≤ k := by
  rw [Nat.mul_comm]
  simpa using unknottingNumber_toGridLink_torusLink_mul_le 1 k

/-- The `(3, 4)` torus knot, presented by its standard `7 × 7` grid, has unknotting number at most
three.

This is the upper bound `u(T_{3,4}) ≤ (3 - 1) (4 - 1) / 2` of the Milnor conjecture for this torus
knot. -/
theorem unknottingNumber_toGridLink_torusLink_two_three_le_three :
    (GridDiagram.torusLink 2 3).toGridLink.unknottingNumber ≤ 3 := by
  simpa using unknottingNumber_toGridLink_torusLink_mul_le 2 1

end GridLink

/-! ### The transposed torus link grids -/

namespace GridLink

open GridDiagram

/-- **The unknotting number of a torus link grid is symmetric in its two winding numbers.** The
standard grids of the `(p + 1, q + 1)` and `(q + 1, p + 1)` torus links present grid links with the
same unknotting number, since they are diagonal reflections of each other. -/
theorem unknottingNumber_toGridLink_torusLink_comm (p q : ℕ) :
    (torusLink q p).toGridLink.unknottingNumber = (torusLink p q).toGridLink.unknottingNumber := by
  rw [← toGridLink_transpose_torusLink, ← transpose_toGridLink, unknottingNumber_transpose]

/-- The `(q + 3, 2)` and `(q + 1, 2)` torus links differ by one crossing change: reflect the
crossing change between the `(2, q + 3)` and `(2, q + 1)` torus links in the diagonal. -/
theorem isCrossingChange_toGridLink_torusLink_add_two_one (q : ℕ) :
    IsCrossingChange (torusLink (q + 2) 1).toGridLink (torusLink q 1).toGridLink := by
  simpa only [transpose_toGridLink, toGridLink_transpose_torusLink] using
    (isCrossingChange_toGridLink_torusLink_one_add_two q).transpose

/-- **The upper bound of the Milnor conjecture for the `(2 k + 1, 2)` torus knots.** The knot
presented by the standard grid of the `(2 k + 1, 2)` torus knot has unknotting number at most
`k = (2 k + 1 - 1) (2 - 1) / 2`, as its reflection, the `(2, 2 k + 1)` torus knot, does. -/
theorem unknottingNumber_toGridLink_torusLink_two_mul_one_le (k : ℕ) :
    (torusLink (2 * k) 1).toGridLink.unknottingNumber ≤ k := by
  rw [unknottingNumber_toGridLink_torusLink_comm]
  exact unknottingNumber_toGridLink_torusLink_one_two_mul_le k

end GridLink

end TauCeti
