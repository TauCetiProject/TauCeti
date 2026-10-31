/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.TorusLink.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.Mk
import TauCeti.KnotTheory.Grid.Move.Stabilization
import TauCeti.KnotTheory.Grid.TorusLink.Alexander

/-!
# Unknotting numbers of torus link grids

This file bounds the unknotting number (`GridLink.unknottingNumber`) of the grid links presented
by the standard grids of torus links. The Hopf link has unknotting number `⊤`, since it has two
components. The `(2, 2k + 1)` torus knot is unknotted by `k` crossing changes, and the `(3, 4)`
torus knot, presented by its standard `7 × 7` grid, by three. These are the upper bounds
`u(T_{p,q}) ≤ (p - 1) (q - 1) / 2` of the Milnor conjecture for these torus knots.

The two-strand family is handled by one crossing change in the standard grid of every size.
Exchanging the first two columns of the standard grid of the `(2, q + 3)` torus link is a
cross-commutation, and the resulting diagram is obtained from the standard grid of the
`(2, q + 1)` torus link by two `X`-stabilizations, up to a cyclic permutation of the columns and
row commutations. Induction on `k`, starting from the standard unknot grid, bounds the unknotting
number of the `(2, 2k + 1)` torus knot by `k`. The `(3, 4)` bound comes from an explicit sequence
of cross-commutations and commutations.

The same upper bound holds for the transposed grids of the `(2 k + 1, 2)` torus knots: the knot
presented by the standard grid `torusLink (2 * k) 1` has unknotting number at most `k`. This
follows by induction from the inequality that the `(p + 3, 2)` torus link has unknotting number
at most one more than the `(p + 1, 2)` torus link, for the links presented by their standard
grids. For even `p` both are knots, and the standard grid of the `(p + 3, 2)` torus knot is one
crossing change away from that of the `(p + 1, 2)` torus knot. On the grid of size `p + 5`,
whose `O`-markings lie on the diagonal and whose `X`-markings lie two rows above it, exchanging
the first two columns is a cross-commutation. The first two rows can then be exchanged, a
commutation, and for `j = 1, 2, …` so can the rows `2 j` and `2 j + 1` followed by the same two
columns. These keep the `O`-markings on the diagonal and conjugate the `X`-permutation by
transpositions. The last of these diagrams is an `O`-stabilization of a grid of size `p + 4`, and
after one more commutation that grid is an `X`-stabilization of the standard grid of size `p + 3`.
For odd `p` the inequality holds because the `(p + 1, 2)` torus link has two components, so its
unknotting number is `⊤`.

## Main results

* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_one`: the Hopf link has unknotting
  number `⊤`.
* `TauCeti.GridLink.isCrossingChange_toGridLink_torusLink_one_add_two`: the `(2, q + 3)` and
  `(2, q + 1)` torus links differ by one crossing change.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_one_two_mul_le`: the `(2, 2k + 1)`
  torus knot has unknotting number at most `k`.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_two_three_le_three`: the `(3, 4)` torus
  knot has unknotting number at most three.
* `TauCeti.GridDiagram.toGridLink_torusLink_zero_one`: the standard `3 × 3` grid of the `(1, 2)`
  torus knot presents the unknot.
* `TauCeti.GridLink.unknottingNumber_toGridLink_torusLink_add_two_one_le_add_one`: the
  `(p + 3, 2)` torus link has unknotting number at most one more than the `(p + 1, 2)` torus link.
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

/-- The `(2, 2k + 1)` torus knot, presented by its standard grid, has unknotting number at most
`k`: this is the upper bound `u(T_{2, 2k+1}) ≤ (2 - 1) (2k + 1 - 1) / 2` of the Milnor
conjecture. Each crossing change of `isCrossingChange_toGridLink_torusLink_one_add_two` lowers
`k` by one, and the `(2, 1)` torus link grid is the standard unknot grid. -/
theorem unknottingNumber_toGridLink_torusLink_one_two_mul_le (k : ℕ) :
    (GridDiagram.torusLink 1 (2 * k)).toGridLink.unknottingNumber ≤ k := by
  induction k with
  | zero =>
    rw [Nat.mul_zero, GridDiagram.torusLink_zero_right, GridDiagram.toGridLink_unknot,
      unknottingNumber_unknot, Nat.cast_zero]
  | succ k ih =>
    rw [Nat.mul_succ, Nat.cast_succ]
    exact (isCrossingChange_toGridLink_torusLink_one_add_two _).unknottingNumber_le.trans
      (by gcongr)

/-- The standard `7 × 7` grid of the `(3, 4)` torus knot with its markings made explicit. -/
private def torusTwoThreeGrid : GridDiagram 7 where
  O := ⟨1⟩
  X := ⟨finRotate 7 ^ 4⟩
  disjoint := by decide

private theorem torusLink_two_three_eq_torusTwoThreeGrid :
    GridDiagram.torusLink 2 3 = torusTwoThreeGrid := by
  ext c <;> simp [torusTwoThreeGrid]

/-- The standard `7 × 7` unknot grid with its markings made explicit. -/
private def unknotSevenGrid : GridDiagram 7 where
  O := ⟨1⟩
  X := ⟨finRotate 7⟩
  disjoint := by decide

private theorem unknot_five_eq_unknotSevenGrid : GridDiagram.unknot 5 = unknotSevenGrid := by
  ext c <;> simp [unknotSevenGrid]

/-- The `(3, 4)` torus knot, presented by its standard `7 × 7` grid, has unknotting number at most
three. Three cross-commutations of adjacent columns, interspersed with nine commutations, turn
it into the standard `7 × 7` unknot grid.

This is the upper bound `u(T_{3,4}) ≤ (3 - 1) (4 - 1) / 2` of the Milnor conjecture for this torus
knot. -/
theorem unknottingNumber_toGridLink_torusLink_two_three_le_three :
    (GridDiagram.torusLink 2 3).toGridLink.unknottingNumber ≤ 3 := by
  rw [torusLink_two_three_eq_torusTwoThreeGrid]
  -- The diagrams `G₁`, `G₃` and `G₇` are reached by a cross-commutation (`h₁`, `h₃`, `h₇`), each
  -- of the others by a commutation; the commutations are grouped into the move sequences `h₂`,
  -- `h₆` and `h₁₂`, the last of which ends at the standard unknot grid.
  set G₁ := torusTwoThreeGrid.swapColumns 0 (finRotate 7 0)
  set G₂ := G₁.swapRows 0 (finRotate 7 0)
  set G₃ := G₂.swapColumns 1 (finRotate 7 1)
  set G₄ := G₃.swapRows 1 (finRotate 7 1)
  set G₅ := G₄.swapRows 2 (finRotate 7 2)
  set G₆ := G₅.swapColumns 2 (finRotate 7 2)
  set G₇ := G₆.swapColumns 6 (finRotate 7 6)
  set G₈ := G₇.swapRows 6 (finRotate 7 6)
  set G₉ := G₈.swapRows 0 (finRotate 7 0)
  set G₁₀ := G₉.swapColumns 0 (finRotate 7 0)
  set G₁₁ := G₁₀.swapRows 5 (finRotate 7 5)
  have h₁ : torusTwoThreeGrid.toGridLink.unknottingNumber ≤ G₁.toGridLink.unknottingNumber + 1 :=
    torusTwoThreeGrid.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 0) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₃ : G₂.toGridLink.unknottingNumber ≤ G₃.toGridLink.unknottingNumber + 1 :=
    G₂.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 1) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₇ : G₆.toGridLink.unknottingNumber ≤ G₇.toGridLink.unknottingNumber + 1 :=
    G₆.unknottingNumber_toGridLink_le_swapColumns_add_one (a := 6) (by
      simp only [GridDiagram.columnsInterleaving_iff, GridDiagram.columnArc, Grid.mem_cIoo]
      decide)
  have h₂ : G₁.MovesTo G₂ := G₁.movesTo_swapRows 0 (by
    simp only [GridDiagram.RowsNoninterleaving, Grid.Noninterleaving, Grid.mem_cIoo]
    decide)
  have h₆ : G₃.MovesTo G₆ := by
    refine (G₃.movesTo_swapRows 1 ?_).trans <|
      (G₄.movesTo_swapRows 2 ?_).trans <| G₅.movesTo_swapColumns 2 ?_
    all_goals
      simp only [GridDiagram.RowsNoninterleaving, GridDiagram.ColumnsNoninterleaving,
        Grid.Noninterleaving, Grid.mem_cIoo]
      decide
  have h₁₂ : G₇.MovesTo (GridDiagram.unknot 5) := by
    have h : G₁₁.swapColumns 5 (finRotate 7 5) = GridDiagram.unknot 5 := by
      rw [unknot_five_eq_unknotSevenGrid]
      ext c
      all_goals revert c; decide
    rw [← h]
    refine (G₇.movesTo_swapRows 6 ?_).trans <|
      (G₈.movesTo_swapRows 0 ?_).trans <|
      (G₉.movesTo_swapColumns 0 ?_).trans <|
      (G₁₀.movesTo_swapRows 5 ?_).trans <| G₁₁.movesTo_swapColumns 5 ?_
    all_goals
      simp only [GridDiagram.RowsNoninterleaving, GridDiagram.ColumnsNoninterleaving,
        Grid.Noninterleaving, Grid.mem_cIoo]
      decide
  calc torusTwoThreeGrid.toGridLink.unknottingNumber
      ≤ G₁.toGridLink.unknottingNumber + 1 := h₁
    _ = G₂.toGridLink.unknottingNumber + 1 := by rw [(G₁.toGridLink_eq_iff_movesTo).mpr h₂]
    _ ≤ G₃.toGridLink.unknottingNumber + 1 + 1 := by gcongr
    _ = G₆.toGridLink.unknottingNumber + 1 + 1 := by rw [(G₃.toGridLink_eq_iff_movesTo).mpr h₆]
    _ ≤ G₇.toGridLink.unknottingNumber + 1 + 1 + 1 := by gcongr
    _ = 3 := by
      rw [(G₇.toGridLink_eq_iff_movesTo).mpr h₁₂, GridDiagram.toGridLink_unknot,
        unknottingNumber_unknot]
      norm_num

end GridLink

/-! ### The `(2 k + 1, 2)` torus knots -/

namespace GridDiagram

open Equiv

/-! #### The chain of conjugations

Start from the standard grid of the `(n + 3, 2)` torus link, of size `n + 5`. Exchange its first
two columns, a crossing change, and then its first two rows, a commutation. This conjugates the
`X`-permutation `finRotate ^ 2` by the transposition `swap 0 1`. Each further step exchanges the
rows `2 j` and `2 j + 1` and then the same two columns, both commutations, and conjugates the
`X`-permutation by `swap (2 j) (2 j + 1)`. The `O`-markings stay on the diagonal throughout. -/

/-- The diagrams of the chain of conjugations, of size `n + 5`. -/
private def chainGrid (n : ℕ) : ℕ → GridDiagram (n + 5)
  | 0 => ((torusLink (n + 2) 1).swapColumns 0 1).swapRows 0 1
  | j + 1 => ((chainGrid n j).swapRows (Fin.ofNat (n + 5) (2 * (j + 1)))
      (Fin.ofNat (n + 5) (2 * (j + 1) + 1))).swapColumns (Fin.ofNat (n + 5) (2 * (j + 1)))
      (Fin.ofNat (n + 5) (2 * (j + 1) + 1))

/-- The `X`-permutation of `chainGrid n j`. -/
private def chainPerm (n j : ℕ) : Perm (Fin (n + 5)) :=
  swap 0 1 * finRotate (n + 5) ^ 2 *
    swap (Fin.ofNat (n + 5) (2 * j)) (Fin.ofNat (n + 5) (2 * j + 1))

private theorem chainGrid_O_toPerm (n j : ℕ) : (chainGrid n j).O.toPerm = 1 := by
  induction j with
  | zero =>
    ext c
    simp [chainGrid]
  | succ j ih => rw [chainGrid, swapRows_swapColumns_O_toPerm, ih, mul_one, swap_mul_self]

private theorem chainGrid_X_toPerm (n j : ℕ) (hj : 2 * j + 1 < n + 5) :
    (chainGrid n j).X.toPerm = chainPerm n j := by
  induction j with
  | zero =>
    have h0 : Fin.ofNat (n + 5) (2 * 0) = 0 := Fin.ext (by simp)
    have h1 : Fin.ofNat (n + 5) (2 * 0 + 1) = 1 := Fin.ext (by simp)
    rw [chainPerm, h0, h1]
    ext c
    simp only [chainGrid, swapRows_X, swapColumns_X, GridState.swapRows_apply,
      GridState.swapColumns_apply, torusLink_X_apply, Perm.mul_apply]
  | succ j ih =>
    rw [chainGrid, swapRows_swapColumns_X_toPerm, ih (by omega), chainPerm, chainPerm]
    set A := swap (Fin.ofNat (n + 5) (2 * (j + 1))) (Fin.ofNat (n + 5) (2 * (j + 1) + 1))
    set R := finRotate (n + 5) ^ 2
    -- `R` carries the transposition of the previous step to `A`, which fixes `0` and `1`.
    have hRB : R * swap (Fin.ofNat (n + 5) (2 * j)) (Fin.ofNat (n + 5) (2 * j + 1)) = A * R := by
      simp (disch := omega) only [R, A, mul_swap_eq_swap_mul, Fin.ofNat_eq_cast,
        Fin.natCast_eq_mk, pow_two, Perm.mul_apply, Fin.finRotate_mk]
      congr 3
    have hconj : A * swap 0 1 * A = swap 0 1 := by
      have hA : A⁻¹ = A := swap_inv _ _
      nth_rw 2 [← hA]
      rw [← swap_apply_apply]
      simp (disch := omega) only [A, Fin.ofNat_eq_cast, Fin.natCast_eq_mk, ← Fin.mk_zero,
        ← Fin.mk_one, swap_apply_def, Fin.mk.injEq, ite_eq_right]
    calc A * (swap 0 1 * R * swap (Fin.ofNat (n + 5) (2 * j)) (Fin.ofNat (n + 5) (2 * j + 1))) * A
        = A * swap 0 1 * A * R * A := by rw [mul_assoc (swap 0 1), hRB]; simp only [mul_assoc]
      _ = swap 0 1 * R * A := by rw [hconj]

/-- The first two columns of the torus knot grid interleave, so exchanging them is a crossing
change. -/
private theorem columnsInterleaving_torusLink (n : ℕ) :
    (torusLink (n + 2) 1).ColumnsInterleaving 0 (finRotate (n + 5) 0) := by
  have hO (c : Fin (n + 5)) : (torusLink (n + 2) 1).O c = c := torusLink_O_apply (n + 2) 1 c
  have hX (c : Fin (n + 5)) : (torusLink (n + 2) 1).X c = (finRotate (n + 5) ^ 2) c :=
    torusLink_X_apply (n + 2) 1 c
  rw [finRotate_apply_zero, columnsInterleaving_iff]
  simp (disch := omega) only [mem_columnArc, hO, hX, pow_two, Perm.mul_apply, ← Fin.mk_zero,
    ← Fin.mk_one, Fin.finRotate_mk, Grid.mem_cIoo, ne_eq, Fin.mk.injEq]
  grind

/-- After the crossing change, the first two rows do not interleave. -/
private theorem rowsNoninterleaving_torusLink_swapColumns (n : ℕ) :
    ((torusLink (n + 2) 1).swapColumns 0 1).RowsNoninterleaving 0 (finRotate (n + 5) 0) := by
  have hO (c : Fin (n + 5)) : (torusLink (n + 2) 1).O c = c := torusLink_O_apply (n + 2) 1 c
  have hX (c : Fin (n + 5)) : (torusLink (n + 2) 1).X c = (finRotate (n + 5) ^ 2) c :=
    torusLink_X_apply (n + 2) 1 c
  rw [finRotate_apply_zero]
  refine rowsNoninterleaving_of_apply (c := 1) (d := ⟨n + 3, by omega⟩) (c' := 0)
    (d' := ⟨n + 4, by omega⟩) ?_ ?_ ?_ ?_ ?_ <;>
  simp (disch := omega) only [swapColumns_O, swapColumns_X, GridState.swapColumns_apply, hO, hX,
    pow_two, Perm.mul_apply, ← Fin.mk_zero, ← Fin.mk_one, swap_apply_def, Fin.finRotate_mk,
    Fin.finRotate_mk_of_eq, Grid.noninterleaving_iff, Grid.mem_cIoo, ne_eq, Fin.mk.injEq,
    ite_eq_left, ite_eq_right, ↓reduceIte]
  grind

private theorem movesTo_chainGrid_zero (n : ℕ) :
    ((torusLink (n + 2) 1).swapColumns 0 (finRotate (n + 5) 0)).MovesTo (chainGrid n 0) := by
  have h := ((torusLink (n + 2) 1).swapColumns 0 (finRotate (n + 5) 0)).movesTo_swapRows 0
    (rowsNoninterleaving_torusLink_swapColumns n)
  rw [finRotate_apply_zero] at h ⊢
  exact h

/-- Each conjugation step of the chain is a pair of commutations. -/
private theorem movesTo_chainGrid_succ (n j : ℕ) (hj : 2 * (j + 1) + 1 < n + 4) :
    (chainGrid n j).MovesTo (chainGrid n (j + 1)) := by
  have hO := chainGrid_O_toPerm n j
  have hX := chainGrid_X_toPerm n j (by omega)
  have hrot : finRotate (n + 5) ⟨2 * (j + 1), by omega⟩ = ⟨2 * (j + 1) + 1, by omega⟩ :=
    finRotate_of_lt (by omega)
  have hrow : (chainGrid n j).RowsNoninterleaving ⟨2 * (j + 1), by omega⟩
      (finRotate (n + 5) ⟨2 * (j + 1), by omega⟩) := by
    rw [hrot]
    refine rowsNoninterleaving_of_apply (c := ⟨2 * (j + 1), by omega⟩) (d := ⟨2 * j + 1, by omega⟩)
      (c' := ⟨2 * (j + 1) + 1, by omega⟩) (d' := ⟨2 * j, by omega⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp (disch := omega) only [hO, hX, chainPerm, Perm.one_apply, Perm.mul_apply, pow_two,
      Fin.ofNat_eq_cast, Fin.natCast_eq_mk, ← Fin.mk_zero, ← Fin.mk_one, swap_apply_def,
      Fin.finRotate_mk, Grid.noninterleaving_iff, Grid.mem_cIoo, ne_eq, Fin.mk.injEq, ite_eq_right,
      ↓reduceIte] <;>
    grind
  have hcol : ((chainGrid n j).swapRows ⟨2 * (j + 1), by omega⟩
      (finRotate (n + 5) ⟨2 * (j + 1), by omega⟩)).ColumnsNoninterleaving
      ⟨2 * (j + 1), by omega⟩ (finRotate (n + 5) ⟨2 * (j + 1), by omega⟩) := by
    rw [hrot, ColumnsNoninterleaving]
    -- The `X`-marking of column `2 j + 3` wraps around the top of the grid in the last step.
    rcases Nat.lt_or_ge (2 * j + 5) (n + 5) with h | h <;>
    simp (disch := omega) only [swapRows_O, swapRows_X, GridState.swapRows_apply, hO, hX,
      chainPerm, Perm.one_apply, Perm.mul_apply, pow_two, Fin.ofNat_eq_cast, Fin.natCast_eq_mk,
      ← Fin.mk_zero, ← Fin.mk_one, swap_apply_def, Fin.finRotate_mk, Fin.finRotate_mk_of_eq,
      Grid.noninterleaving_iff, Grid.mem_cIoo, ne_eq, Fin.mk.injEq, ite_eq_left, ite_eq_right,
      ↓reduceIte] <;>
    grind
  have h := ((chainGrid n j).movesTo_swapRows _ hrow).trans (movesTo_swapColumns _ _ hcol)
  rw [hrot] at h
  rw [chainGrid, Fin.ofNat_eq_cast, Fin.ofNat_eq_cast,
    Fin.natCast_eq_mk (show 2 * (j + 1) < n + 5 by omega),
    Fin.natCast_eq_mk (show 2 * (j + 1) + 1 < n + 5 by omega)]
  exact h

private theorem movesTo_chainGrid (k j : ℕ) (hj : j ≤ k + 1) :
    (chainGrid (2 * k) 0).MovesTo (chainGrid (2 * k) j) := by
  induction j with
  | zero => exact MovesTo.refl _
  | succ j ih => exact (ih (by omega)).trans (movesTo_chainGrid_succ _ _ (by omega))

/-! #### The two destabilizations

For `n = 2 k` the chain ends at `chainGrid n (k + 1)`, with `X`-permutation
`swap 0 1 * finRotate ^ 2 * swap (n + 2) (n + 3)`. Its last two columns carry an `O`-stabilization
of `destabGrid n`, of size `n + 4`. Exchanging the last two columns of `destabGrid n`, a
commutation, gives an `X`-stabilization of the standard grid of the `(n + 1, 2)` torus link. -/

/-- The diagram of size `n + 4` with diagonal `O`-markings and `X`-permutation
`swap 0 1 * finRotate (n + 4) ^ 2`. -/
private def destabGrid (n : ℕ) : GridDiagram (n + 4) where
  O := ⟨1⟩
  X := ⟨swap 0 1 * finRotate (n + 4) ^ 2⟩
  disjoint := by
    rintro ⟨c, hc⟩ h
    rcases (show c + 2 < n + 4 ∨ c = n + 2 ∨ c = n + 3 by omega) with h' | h' | h' <;>
    simp (disch := omega) only [Perm.one_apply, Perm.mul_apply, pow_two, ← Fin.mk_zero,
      ← Fin.mk_one, swap_apply_def, Fin.finRotate_mk, Fin.finRotate_mk_of_eq, Fin.mk.injEq,
      ite_eq_right, ↓reduceIte] at h <;>
    omega

private theorem destabGrid_O_toPerm (n : ℕ) : (destabGrid n).O.toPerm = 1 :=
  rfl

private theorem destabGrid_X_toPerm (n : ℕ) :
    (destabGrid n).X.toPerm = swap 0 1 * finRotate (n + 4) ^ 2 :=
  rfl

/-- The end of the chain is an `O`-stabilization of `destabGrid`. -/
private theorem isStabilization_destabGrid_chainGrid (k : ℕ) :
    IsStabilization (destabGrid (2 * k)) (chainGrid (2 * k) (k + 1)) := by
  have hO := chainGrid_O_toPerm (2 * k) (k + 1)
  have hX := chainGrid_X_toPerm (2 * k) (k + 1) (by omega)
  have heq : chainGrid (2 * k) (k + 1) = (destabGrid (2 * k)).stabilizeO ⟨2 * k + 3, by omega⟩
      ⟨2 * k + 4, by omega⟩ ⟨2 * k + 3, by omega⟩ := by
    refine GridDiagram.ext (GridState.ext fun c => ?_) (GridState.ext fun c => ?_) <;>
    rcases Fin.eq_self_or_eq_succAbove (⟨2 * k + 3, by omega⟩ : Fin (2 * k + 5)) c with
      rfl | ⟨⟨i, hi⟩, rfl⟩
    · simp (disch := omega) only [hO, destabGrid_O_toPerm, stabilizeO_O,
        GridState.splitPoint_apply_newColumn, Perm.one_apply, Fin.succAbove_mk_of_lt]
    · rw [stabilizeO_O, GridState.splitPoint_apply_succAbove]
      rcases (show i < 2 * k + 3 ∨ i = 2 * k + 3 by omega) with h | h <;>
      simp (disch := omega) only [hO, destabGrid_O_toPerm, Perm.one_apply, Fin.succAbove_mk_of_lt,
        Fin.succAbove_mk_of_le, Fin.mk.injEq, ite_eq_left, ite_eq_right]
      omega
    · simp (disch := omega) only [hX, chainPerm, stabilizeO_X,
        GridState.insertPoint_apply_newColumn, Perm.mul_apply, pow_two, Fin.ofNat_eq_cast,
        Fin.natCast_eq_mk, ← Fin.mk_zero, ← Fin.mk_one, swap_apply_def, Fin.finRotate_mk,
        Fin.mk.injEq, ite_eq_left, ite_eq_right]
      omega
    · rw [stabilizeO_X, GridState.insertPoint_apply_succAbove]
      rcases (show i < 2 * k + 2 ∨ i = 2 * k + 2 ∨ i = 2 * k + 3 by omega) with h | h | h <;>
      simp (disch := omega) only [hX, chainPerm, destabGrid_X_toPerm, Perm.mul_apply, pow_two,
        Fin.ofNat_eq_cast, Fin.natCast_eq_mk, ← Fin.mk_zero, ← Fin.mk_one, swap_apply_def,
        Fin.finRotate_mk, Fin.finRotate_mk_of_eq, Fin.succAbove_mk_of_lt, Fin.succAbove_mk_of_le,
        Fin.mk.injEq, ite_eq_left, ite_eq_right, ↓reduceIte]
  rw [heq]
  refine (isStabilization_iff _ _).mpr (Or.inl ((destabGrid (2 * k)).isOStabilization_stabilizeO
    ⟨2 * k + 3, by omega⟩ ⟨2 * k + 4, by omega⟩ ⟨2 * k + 3, by omega⟩ (Or.inl ?_) (Or.inr ?_)))
  · simp (disch := omega) only [Fin.succAbove_mk_of_le, Fin.finRotate_mk]
  · simp (disch := omega) only [destabGrid_O_toPerm, Perm.one_apply, Fin.succAbove_mk_of_lt,
      Fin.finRotate_mk]

/-- The last two columns of `destabGrid` do not interleave. -/
private theorem columnsNoninterleaving_destabGrid (n : ℕ) :
    (destabGrid n).ColumnsNoninterleaving ⟨n + 2, by omega⟩
      (finRotate (n + 4) ⟨n + 2, by omega⟩) := by
  rw [ColumnsNoninterleaving]
  simp (disch := omega) only [destabGrid_O_toPerm, destabGrid_X_toPerm, Perm.one_apply,
    Perm.mul_apply, pow_two, ← Fin.mk_zero, ← Fin.mk_one, swap_apply_def, Fin.finRotate_mk,
    Fin.finRotate_mk_of_eq, Grid.noninterleaving_iff, Grid.mem_cIoo, ne_eq, Fin.mk.injEq,
    ite_eq_right, ↓reduceIte]
  grind

/-- After exchanging its last two columns, `destabGrid n` is an `X`-stabilization of the standard
grid of the `(n + 1, 2)` torus link. -/
private theorem isStabilization_torusLink_destabGrid_swapColumns (n : ℕ) :
    IsStabilization (torusLink n 1) ((destabGrid n).swapColumns ⟨n + 2, by omega⟩
      (finRotate (n + 4) ⟨n + 2, by omega⟩)) := by
  have hO (c : Fin (n + 3)) : (torusLink n 1).O c = c := torusLink_O_apply n 1 c
  have hX (c : Fin (n + 3)) : (torusLink n 1).X c = (finRotate (n + 3) ^ 2) c :=
    torusLink_X_apply n 1 c
  have hrot : finRotate (n + 4) ⟨n + 2, by omega⟩ = ⟨n + 3, by omega⟩ := finRotate_of_lt (by omega)
  have heq : (destabGrid n).swapColumns ⟨n + 2, by omega⟩ (finRotate (n + 4) ⟨n + 2, by omega⟩) =
      (torusLink n 1).stabilizeX ⟨n + 2, by omega⟩ ⟨n + 3, by omega⟩ ⟨n + 1, by omega⟩ := by
    rw [hrot]
    refine GridDiagram.ext (GridState.ext fun c => ?_) (GridState.ext fun c => ?_) <;>
    rcases Fin.eq_self_or_eq_succAbove (⟨n + 2, by omega⟩ : Fin (n + 4)) c with
      rfl | ⟨⟨i, hi⟩, rfl⟩
    · rw [stabilizeX_O, GridState.insertPoint_apply_newColumn]
      simp (disch := omega) only [swapColumns_O, GridState.swapColumns_apply, destabGrid_O_toPerm,
        Perm.one_apply, swap_apply_def, ↓reduceIte]
    · rw [stabilizeX_O, GridState.insertPoint_apply_succAbove]
      rcases (show i < n + 2 ∨ i = n + 2 by omega) with h | h <;>
      simp (disch := omega) only [swapColumns_O, GridState.swapColumns_apply, destabGrid_O_toPerm,
        hO, Perm.one_apply, swap_apply_def, Fin.succAbove_mk_of_lt, Fin.succAbove_mk_of_le,
        Fin.mk.injEq, ite_eq_left, ite_eq_right]
      omega
    · rw [stabilizeX_X, GridState.splitPoint_apply_newColumn]
      simp (disch := omega) only [swapColumns_X, GridState.swapColumns_apply, destabGrid_X_toPerm,
        hX, Perm.mul_apply, pow_two, ← Fin.mk_zero, ← Fin.mk_one, swap_apply_def,
        Fin.finRotate_mk, Fin.finRotate_mk_of_eq, Fin.succAbove_mk_of_lt, Fin.mk.injEq,
        ite_eq_right, ↓reduceIte]
    · rw [stabilizeX_X, GridState.splitPoint_apply_succAbove]
      rcases (show i < n + 1 ∨ i = n + 1 ∨ i = n + 2 by omega) with h | h | h <;>
      simp (disch := omega) only [swapColumns_X, GridState.swapColumns_apply, destabGrid_X_toPerm,
        hX, Perm.mul_apply, pow_two, ← Fin.mk_zero, ← Fin.mk_one, swap_apply_def,
        Fin.finRotate_mk, Fin.finRotate_mk_of_eq, Fin.succAbove_mk_of_lt, Fin.succAbove_mk_of_le,
        Fin.mk.injEq, ite_eq_left, ite_eq_right, ↓reduceIte]
      omega
  rw [heq]
  refine (isStabilization_iff _ _).mpr (Or.inr ((torusLink n 1).isXStabilization_stabilizeX
    ⟨n + 2, by omega⟩ ⟨n + 3, by omega⟩ ⟨n + 1, by omega⟩ (Or.inr ?_) (Or.inl ?_)))
  · simp (disch := omega) only [Fin.succAbove_mk_of_lt, Fin.finRotate_mk]
  · simp (disch := omega) only [hX, pow_two, Perm.mul_apply, Fin.finRotate_mk,
      Fin.finRotate_mk_of_eq, Fin.succAbove_mk_of_lt]

/-- The end of the chain presents the same grid link as the standard grid of the `(2 k + 1, 2)`
torus knot. -/
private theorem movesTo_torusLink_of_chainGrid (k : ℕ) :
    (chainGrid (2 * k) (k + 1)).MovesTo (torusLink (2 * k) 1) :=
  (IsDestabilization.movesTo ((isDestabilization_iff_isStabilization _ _).mpr
    (isStabilization_destabGrid_chainGrid k))).trans <|
    ((destabGrid _).movesTo_swapColumns _ (columnsNoninterleaving_destabGrid _)).trans <|
      IsDestabilization.movesTo ((isDestabilization_iff_isStabilization _ _).mpr
        (isStabilization_torusLink_destabGrid_swapColumns _))

/-! #### The `(1, 2)` torus knot -/

/-- The standard `3 × 3` grid of the `(1, 2)` torus knot with its markings made explicit. -/
private def torusZeroOneGrid : GridDiagram 3 where
  O := ⟨1⟩
  X := ⟨finRotate 3 ^ 2⟩
  disjoint := by decide

private theorem torusLink_zero_one_eq : torusLink 0 1 = torusZeroOneGrid := by
  ext c <;> simp [torusZeroOneGrid]

/-- The standard `3 × 3` unknot grid with its markings made explicit. -/
private def unknotThreeGrid : GridDiagram 3 where
  O := ⟨1⟩
  X := ⟨finRotate 3⟩
  disjoint := by decide

private theorem unknot_one_eq_unknotThreeGrid : unknot 1 = unknotThreeGrid := by
  ext c <;> simp [unknotThreeGrid]

/-- The standard `3 × 3` grid of the `(1, 2)` torus knot presents the unknot: a commutation of its
first two rows followed by one of its first two columns gives the standard unknot grid. -/
theorem toGridLink_torusLink_zero_one : (torusLink 0 1).toGridLink = GridLink.unknot := by
  rw [torusLink_zero_one_eq, ← toGridLink_unknot 1, toGridLink_eq_iff_movesTo,
    unknot_one_eq_unknotThreeGrid]
  have h : (torusZeroOneGrid.swapRows 0 (finRotate 3 0)).swapColumns 0 (finRotate 3 0) =
      unknotThreeGrid := by
    ext c
    all_goals revert c; decide
  rw [← h]
  refine (torusZeroOneGrid.movesTo_swapRows 0 ?_).trans (movesTo_swapColumns _ 0 ?_) <;>
  simp only [RowsNoninterleaving, ColumnsNoninterleaving, Grid.Noninterleaving, Grid.mem_cIoo] <;>
  decide

end GridDiagram

namespace GridLink

open GridDiagram

/-- **The `(p + 3, 2)` torus link has unknotting number at most one more than the `(p + 1, 2)`
torus link**, for the links presented by the standard torus link grids. For even `p` both are
knots, and a cross-commutation of the first two columns of the larger grid, followed by
commutations and two destabilizations, reaches the smaller grid, so the two knots are one crossing
change apart. For odd `p` the `(p + 1, 2)` torus link has two components, so its unknotting number
is `⊤` and the inequality is immediate. -/
theorem unknottingNumber_toGridLink_torusLink_add_two_one_le_add_one (p : ℕ) :
    (torusLink (p + 2) 1).toGridLink.unknottingNumber ≤
      (torusLink p 1).toGridLink.unknottingNumber + 1 := by
  rcases Nat.even_or_odd p with ⟨k, rfl⟩ | hp
  · rw [← two_mul]
    refine ((torusLink (2 * k + 2) 1).unknottingNumber_toGridLink_le_swapColumns_add_one
      (columnsInterleaving_torusLink (2 * k))).trans_eq ?_
    rw [(toGridLink_eq_iff_movesTo _).mpr ((movesTo_chainGrid_zero _).trans
      ((movesTo_chainGrid k (k + 1) le_rfl).trans (movesTo_torusLink_of_chainGrid k)))]
  · have hknot : ¬(torusLink p 1).IsKnot := by
      rw [isKnot_torusLink_iff, Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two,
        not_not, ← even_iff_two_dvd]
      exact hp.add_one
    have htop : (torusLink p 1).toGridLink.unknottingNumber = ⊤ := by
      by_contra h
      exact hknot ((isKnot_toGridLink _).mp (isKnot_of_unknottingNumber_ne_top h))
    simp [htop]

/-- **The upper bound of the Milnor conjecture for the `(2 k + 1, 2)` torus knots.** The knot
presented by the standard grid of the `(2 k + 1, 2)` torus knot has unknotting number at most
`k = (2 k + 1 - 1) (2 - 1) / 2`. -/
theorem unknottingNumber_toGridLink_torusLink_two_mul_one_le (k : ℕ) :
    (torusLink (2 * k) 1).toGridLink.unknottingNumber ≤ k := by
  induction k with
  | zero => simp [toGridLink_torusLink_zero_one, unknottingNumber_unknot]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring]
    calc (torusLink (2 * k + 2) 1).toGridLink.unknottingNumber
        ≤ (torusLink (2 * k) 1).toGridLink.unknottingNumber + 1 :=
          unknottingNumber_toGridLink_torusLink_add_two_one_le_add_one (2 * k)
      _ ≤ k + 1 := by gcongr
      _ = (k + 1 : ℕ) := by push_cast; rfl

end GridLink

end TauCeti
