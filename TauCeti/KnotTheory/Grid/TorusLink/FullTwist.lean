/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.Move.Stabilization
public import TauCeti.KnotTheory.Grid.TorusLink.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.Fin

/-!
# Removing a full twist from a torus link grid

Write `P = p + 1` and `Q = q + 1`. As a braid closure, the `(P, Q + P)` torus link is the
`(P, Q)` torus link with one more full twist `Δ²` on its `P` strands. The full twist is the square
of the half twist `Δ`, a positive braid with `P (P - 1) / 2 = (P choose 2)` crossings, so changing
these crossings turns `Δ²` into `Δ⁻¹ Δ`, the trivial braid. This file carries out that argument
on the standard torus link grids (`GridDiagram.torusLink`): the grid links of the standard grids of
the `(P, Q + P)` and the `(P, Q)` torus links are joined by at most `P choose 2` crossing changes
(`GridLink.crossingChangeGraph_edist_torusLink_add_le`).

The proof runs through a family of intermediate grids. For `m ≤ P`, the private grid
`twistGrid p q m` of size `P + Q + m` has its `O`-markings on the diagonal and the `X`-marking of
column `j` in row `j + P + Q` for `j < m`, in row `j + Q` for `m ≤ j < P`, and in row `j - P`
for `j ≥ P`. With `m = P` it is the standard grid of the `(P, Q + P)` torus link, and with
`m = 0` the standard grid of the `(P, Q)` torus link. From `m + 1` to `m`, move the first column,
with its markings in the rows `0` and `P + Q`, to the right, one adjacent column at a time,
until it reaches column `P - 1`.

* The first `m` exchanges pass the columns `j < m + 1`, whose markings lie in the rows `j` and
  `j + P + Q`. These segments interleave with that of the moving column, so each exchange is a
  cross-commutation, a crossing change.
* The remaining exchanges pass the columns `m + 1 ≤ j < P`, whose segments, from row `j` to row
  `j + Q`, are nested inside that of the moving column, so each exchange is a commutation.
* The moving column now sits just before column `P`, whose `X`-marking is in row `0`, next to
  the `O`-marking of the moving column. The result is the `X`-stabilization of `twistGrid p q m`
  splitting the `X`-marking of column `P - 1`, with the new column just before the split column
  and the new row at the bottom, which is connected to `twistGrid p q m` by grid moves
  (`GridDiagram.movesTo_stabilizeX_castSucc`).

So the `m`-th step costs `m` crossing changes, and the `P` steps together cost
`0 + 1 + ⋯ + (P - 1) = P choose 2`.

## Main results

* `TauCeti.GridLink.crossingChangeGraph_edist_torusLink_add_le`: the grid links of the standard
  grids of the `(P, Q + P)` and the `(P, Q)` torus links are at distance at most `P choose 2` in
  the crossing change graph.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 6: crossing changes as cross-commutations, the unknotting
  number, and the Milnor conjecture `u(T_{p,q}) = (p - 1) (q - 1) / 2`.
-/

public section

namespace TauCeti

namespace GridDiagram

variable (p q : ℕ)

/-! ### The intermediate grids -/

/-- The row of the `X`-marking in column `j` of the intermediate grid with parameter `m`. -/
private def twistXRow (m j : ℕ) : ℕ :=
  if j < m then j + (p + 1) + (q + 1) else if j ≤ p then j + (q + 1) else j - (p + 1)

private theorem twistXRow_lt {n m j : ℕ} (hn : n = p + 1 + (q + 1) + m) (hj : j < n) :
    twistXRow p q m j < n := by
  unfold twistXRow
  split_ifs <;> omega

private theorem twistXRow_inj {n m i j : ℕ} (hm : m ≤ p + 1) (hn : n = p + 1 + (q + 1) + m)
    (hi : i < n) (hj : j < n) (h : twistXRow p q m i = twistXRow p q m j) : i = j := by
  unfold twistXRow at h
  split_ifs at h <;> omega

/-- The intermediate grid of size `(p + 1) + (q + 1) + m`: its `O`-markings are on the diagonal,
and the `X`-marking of column `j` is in row `twistXRow p q m j`. -/
private noncomputable def twistGrid {n : ℕ} (m : ℕ) (hm : m ≤ p + 1)
    (hn : n = p + 1 + (q + 1) + m) : GridDiagram n where
  O := ⟨1⟩
  X := ⟨Equiv.ofBijective (fun j ↦ ⟨twistXRow p q m j, twistXRow_lt p q hn j.isLt⟩)
    (Finite.injective_iff_bijective.mp fun i j h ↦
      Fin.ext (twistXRow_inj p q hm hn i.isLt j.isLt (congrArg Fin.val h)))⟩
  disjoint c h := by
    have h' : (c : ℕ) = twistXRow p q m c := congrArg Fin.val h
    unfold twistXRow at h'
    split_ifs at h' <;> omega

section TwistGrid

variable {p q} {n m : ℕ} (hm : m ≤ p + 1) (hn : n = p + 1 + (q + 1) + m)

private theorem twistGrid_O_apply (c : Fin n) : (twistGrid p q m hm hn).O c = c :=
  rfl

private theorem twistGrid_X_val (c : Fin n) :
    ((twistGrid p q m hm hn).X c : ℕ) = twistXRow p q m c :=
  rfl

end TwistGrid

/-- With no twisted column, the intermediate grid is the standard `(p + 1, q + 1)` torus link
grid. -/
private theorem twistGrid_zero : twistGrid p q 0 (Nat.zero_le _) rfl = torusLink p q := by
  refine GridDiagram.ext (GridState.ext fun c ↦ ?_) (GridState.ext fun c ↦ Fin.ext ?_)
  · rw [twistGrid_O_apply, torusLink_O_apply]
  · rw [twistGrid_X_val, twistXRow]
    rcases le_or_gt (c : ℕ) p with h | h
    · rw [torusLink_X_val_of_le p q h]
      split_ifs <;> omega
    · rw [torusLink_X_val_of_lt p q h]
      split_ifs <;> omega

/-- With all `p + 1` columns twisted, the intermediate grid is the standard
`(p + 1, (q + (p + 1)) + 1)` torus link grid. -/
private theorem twistGrid_top :
    twistGrid p q (n := p + 1 + (q + (p + 1) + 1)) (p + 1) le_rfl (by omega) =
      torusLink p (q + (p + 1)) := by
  refine GridDiagram.ext (GridState.ext fun c ↦ ?_) (GridState.ext fun c ↦ Fin.ext ?_)
  · rw [twistGrid_O_apply, torusLink_O_apply]
  · rw [twistGrid_X_val, twistXRow]
    rcases le_or_gt (c : ℕ) p with h | h
    · rw [torusLink_X_val_of_le p (q + (p + 1)) h]
      split_ifs <;> omega
    · rw [torusLink_X_val_of_lt p (q + (p + 1)) h]
      split_ifs <;> omega

/-! ### Sliding the first column to the right -/

/-- The cycle `(0 1 ⋯ i)` on natural numbers. -/
private def cycleVal (i c : ℕ) : ℕ :=
  if c < i then c + 1 else if c = i then 0 else c

/-- The intermediate grid with its first column moved to position `i`. -/
private noncomputable def twistSlide {n m : ℕ} (hm : m ≤ p + 1) (hn : n = p + 1 + (q + 1) + m)
    (i : Fin n) : GridDiagram n :=
  (twistGrid p q m hm hn).relabelColumns (Fin.cycleRange i).symm

section TwistSlide

variable {p q} {n m : ℕ} (hm : m ≤ p + 1) (hn : n = p + 1 + (q + 1) + m)

private theorem twistSlide_O_val (i c : Fin n) :
    ((twistSlide p q hm hn i).O c : ℕ) = cycleVal i c := by
  rw [twistSlide, relabelColumns_O_apply, Equiv.symm_symm, twistGrid_O_apply,
    Fin.coe_cycleRange, cycleVal]

private theorem twistSlide_X_val (i c : Fin n) :
    ((twistSlide p q hm hn i).X c : ℕ) =
      twistXRow p q m (cycleVal i c) := by
  rw [twistSlide, relabelColumns_X_apply, Equiv.symm_symm, twistGrid_X_val,
    Fin.coe_cycleRange, cycleVal]

private theorem twistSlide_zero (h0 : 0 < n) :
    twistSlide p q hm hn ⟨0, h0⟩ = twistGrid p q m hm hn := by
  rw [twistSlide, Fin.cycleRange_mk_zero h0]
  exact relabelColumns_refl _

/-- Moving the first column one step further right is exchanging two adjacent columns. -/
private theorem twistSlide_succ (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    twistSlide p q hm hn ⟨i + 1, hi⟩ =
      (twistSlide p q hm hn i).swapColumns i (finRotate n i) := by
  rw [(Fin.ext (Fin.coe_finRotate_of_add_one_lt hi) : finRotate n i = ⟨i + 1, hi⟩)]
  refine GridDiagram.ext (GridState.ext fun c ↦ Fin.ext ?_) (GridState.ext fun c ↦ Fin.ext ?_)
  · rw [swapColumns_O, GridState.swapColumns_apply, twistSlide_O_val, twistSlide_O_val,
      Equiv.swap_apply_def]
    simp only [Fin.ext_iff, cycleVal]
    split_ifs <;> simp_all <;> omega
  · rw [swapColumns_X, GridState.swapColumns_apply, twistSlide_X_val, twistSlide_X_val,
      Equiv.swap_apply_def]
    simp only [Fin.ext_iff, cycleVal]
    split_ifs <;> simp_all <;> omega

/-- While the moving column passes a column `j < m`, the exchange is a cross-commutation. -/
private theorem columnsInterleaving_twistSlide (i : Fin n) (hi : (i : ℕ) + 1 < m) :
    (twistSlide p q hm hn i).ColumnsInterleaving i (finRotate n i) := by
  rw [(Fin.ext (Fin.coe_finRotate_of_add_one_lt (by omega)) : finRotate n i = ⟨i + 1, by omega⟩),
    columnsInterleaving_iff]
  right
  simp only [mem_columnArc, Grid.mem_cIoo, ne_eq, Fin.ext_iff, twistSlide_O_val, twistSlide_X_val,
    twistXRow, cycleVal]
  split_ifs <;> omega

/-- Once the moving column passes the columns `m ≤ j ≤ p`, the exchanges are commutations. -/
private theorem columnsNoninterleaving_twistSlide (h0 : 0 < m) (i : Fin n)
    (hi₁ : m ≤ (i : ℕ) + 1) (hi₂ : (i : ℕ) + 1 ≤ p) :
    (twistSlide p q hm hn i).ColumnsNoninterleaving i (finRotate n i) := by
  rw [(Fin.ext (Fin.coe_finRotate_of_add_one_lt (by omega)) : finRotate n i = ⟨i + 1, by omega⟩),
    ColumnsNoninterleaving, Grid.noninterleaving_iff]
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩ <;>
    simp only [Grid.mem_cIoo, ne_eq, Fin.ext_iff, twistSlide_O_val, twistSlide_X_val, twistXRow,
      cycleVal] at h ⊢ <;>
    split_ifs at h ⊢ <;> (try simp only [not_false_eq_true, true_and] at h ⊢) <;> omega

end TwistSlide

/-- At the end of the slide, the moving column sits just before the split column of an
`X`-stabilization of the intermediate grid with one fewer twisted column. -/
private theorem twistSlide_last {n m : ℕ} (hm : m + 1 ≤ p + 1) (hn : n = p + 1 + (q + 1) + m) :
    twistSlide p q (n := n + 1) hm (by omega) ⟨p, by omega⟩ =
      (twistGrid p q m (by omega) hn).stabilizeX (⟨p, by omega⟩ : Fin n).castSucc 0
        ⟨p, by omega⟩ := by
  refine GridDiagram.ext (GridState.ext fun c ↦ Fin.ext ?_) (GridState.ext fun c ↦ Fin.ext ?_)
  · rw [stabilizeX_O, twistSlide_O_val]
    induction c using Fin.succAboveCases (⟨p, by omega⟩ : Fin n).castSucc with
    | x => simp [cycleVal]
    | p i =>
      rw [GridState.insertPoint_apply_succAbove, twistGrid_O_apply]
      simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite Fin.val, Fin.val_succ,
        Fin.val_zero, cycleVal]
      split_ifs <;> omega
  · rw [stabilizeX_X, twistSlide_X_val]
    induction c using Fin.succAboveCases (⟨p, by omega⟩ : Fin n).castSucc with
    | x =>
      rw [GridState.splitPoint_apply_newColumn, Fin.succAbove_zero, Fin.val_succ, twistGrid_X_val]
      simp only [Fin.val_castSucc, cycleVal, lt_self_iff_false, ite_false, ite_true, twistXRow]
      split_ifs <;> omega
    | p i =>
      rw [GridState.splitPoint_apply_succAbove]
      simp only [Fin.ext_iff, apply_ite Fin.val, Fin.val_succ, Fin.val_zero,
        twistGrid_X_val, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, twistXRow, cycleVal]
      split_ifs <;> omega

/-! ### Crossing-change distances -/

/-- From `m + 1` twisted columns to `m`, at most `m` crossing changes are needed. -/
private theorem edist_twistGrid_succ_le {n m : ℕ} (hm : m + 1 ≤ p + 1)
    (hn : n = p + 1 + (q + 1) + m) :
    GridLink.crossingChangeGraph.edist
        (twistGrid p q (n := n + 1) (m + 1) hm (by omega)).toGridLink
        (twistGrid p q m (by omega) hn).toGridLink ≤ m := by
  have hn' : n + 1 = p + 1 + (q + 1) + (m + 1) := by omega
  -- The first `m` exchanges are crossing changes.
  have hcross (k : ℕ) (hk : k ≤ m) :
      GridLink.crossingChangeGraph.edist
          (twistSlide p q hm hn' ⟨0, by omega⟩).toGridLink
          (twistSlide p q hm hn' ⟨k, by omega⟩).toGridLink ≤ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : (twistSlide p q hm hn' ⟨k, by omega⟩).IsCrossCommutation
          (twistSlide p q hm hn' ⟨k + 1, by omega⟩) := by
        rw [twistSlide_succ hm hn' ⟨k, by omega⟩ (by simp only; omega)]
        exact (isCrossCommutation_iff _ _).mpr <| Or.inr <|
          isColumnCrossCommutation_swapColumns _ <|
            columnsInterleaving_twistSlide hm hn' _ (by simp only; omega)
      calc _ ≤ _ + _ := SimpleGraph.edist_triangle
        _ ≤ k + 1 := by
          gcongr
          · exact ih (by omega)
          · exact hstep.isCrossingChange.edist_le_one
  -- The remaining exchanges are commutations.
  have hcomm (k : ℕ) (hk₁ : m ≤ k) (hk₂ : k ≤ p) :
      (twistSlide p q hm hn' ⟨m, by omega⟩).toGridLink =
        (twistSlide p q hm hn' ⟨k, by omega⟩).toGridLink := by
    induction k, hk₁ using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [ih (by omega), toGridLink_eq_iff_movesTo,
        twistSlide_succ hm hn' ⟨k, by omega⟩ (by simp only; omega)]
      exact movesTo_swapColumns _ _ <| columnsNoninterleaving_twistSlide hm hn' (by omega) _
        (by simp only; omega) (by simp only; omega)
  have hlast : (twistSlide p q hm hn' ⟨p, by omega⟩).toGridLink =
      (twistGrid p q m (by omega) hn).toGridLink := by
    rw [toGridLink_eq_iff_movesTo, twistSlide_last p q hm hn]
    exact movesTo_stabilizeX_castSucc _ _ _
  rw [← twistSlide_zero hm hn' (by omega), ← hlast, ← hcomm p (by omega) le_rfl]
  exact hcross m le_rfl

/-- The intermediate grid with `m` twisted columns is at most `m choose 2` crossing changes away
from the standard `(p + 1, q + 1)` torus link grid. -/
private theorem edist_twistGrid_le (m : ℕ) (hm : m ≤ p + 1) {n : ℕ}
    (hn : n = p + 1 + (q + 1) + m) :
    GridLink.crossingChangeGraph.edist (twistGrid p q m hm hn).toGridLink
      (torusLink p q).toGridLink ≤ m.choose 2 := by
  induction m generalizing n with
  | zero =>
    subst hn
    rw [twistGrid_zero, SimpleGraph.edist_self]
    exact zero_le
  | succ m ih =>
    subst hn
    calc _ ≤ _ + _ := SimpleGraph.edist_triangle
      _ ≤ (m : ℕ∞) + m.choose 2 :=
        add_le_add (edist_twistGrid_succ_le p q hm rfl) (ih (by omega) rfl)
      _ = (m + 1).choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]

end GridDiagram

namespace GridLink

/-- **Removing a full twist from a torus link costs `(p + 1) choose 2` crossing changes.** The grid
links of the standard grids of the `(p + 1, (q + (p + 1)) + 1)` and the `(p + 1, q + 1)` torus
links are at distance at most `(p + 1) choose 2` in the crossing change graph: the former has one
more full twist on its `p + 1` strands, and changing the crossings of a half twist removes it. -/
theorem crossingChangeGraph_edist_torusLink_add_le (p q : ℕ) :
    crossingChangeGraph.edist (GridDiagram.torusLink p (q + (p + 1))).toGridLink
      (GridDiagram.torusLink p q).toGridLink ≤ (p + 1).choose 2 := by
  rw [← GridDiagram.twistGrid_top]
  exact GridDiagram.edist_twistGrid_le p q (p + 1) le_rfl _

end GridLink

end TauCeti
