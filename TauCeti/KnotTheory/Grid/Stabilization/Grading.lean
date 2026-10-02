/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Grading.UnblockedChain
public import TauCeti.KnotTheory.Grid.Stabilization.Basic
public import TauCeti.KnotTheory.Grid.XHomotopy.Basic
import TauCeti.Data.Fin.Basic

/-!
# The gradings of the center states of an `X`-stabilization

Let `G' = G.stabilizeX s.castSucc (G.X s).castSucc s` be the stabilization of a grid diagram `G`
of size `n` splitting the `X`-marking of column `s`. Its center states are the states
`x' = x.insertPoint s.succ (G.X s).succ` obtained from the states `x` of `G` by adding the
center of the new `2 × 2` block. This file computes the gradings of `x'` in `G'` from those of
`x` in `G`:

`M_O(x') = M_O(x) - 1`, `M_X(x') = M_X(x)` and `A(x') = A(x) - 1`.

All three point sets entering these gradings arise by inserting one point: the `O`-marking state
of `G'` inserts the new `O`-marking at `(s.castSucc, (G.X s).castSucc)`, and its `X`-marking state
inserts `X₂` at `(s.succ, (G.X s).castSucc)` (`GridState.splitPoint_castSucc_eq_insertPoint`).
With these column and row offsets, every comparison between two old points is the comparison in
`G`, so each point-pair count in the Maslov gradings of `x'` (`GridDiagram.maslovOℤ_eq_card`) is
the count for `x` plus the comparisons involving an inserted point. Those extra comparisons
cancel, up to the constant `-1` for `M_O`.

On off-center states the chain map `GC⁻(G') ⟶ GC⁻(G)` of the stabilization is the component
`H_I^N` of the `X₂`-homotopy, which sends an off-center state `y` to the sum of the terms
`V^{O(r)} · x'` over its rectangles `r` from `y` to center states `x'`, followed by `x' ↦ x` and
the merging of the two variables of the new block
(`GridDiagram.map_offCenterInclusion_comp_stabilizeXMap`). Combining the grading shift with the
grading change across such a rectangle
(`GridDiagram.alexander_sub_card_OColumns_eq_alexander_sub_one`), the term `V^{O(r)} · x` has the
`O`-Maslov and Alexander gradings of `y` (`GridDiagram.maslovOℤ_stabilizeX_eq_of_isEmpty` and
`GridDiagram.alexander_stabilizeX_eq_of_mem_XHomotopyRectangles`). These are the grading facts
from which the stabilization map preserves the bigrading.

## Main results

* `TauCeti.GridDiagram.maslovOℤ_stabilizeX_insertPoint`,
  `TauCeti.GridDiagram.maslovXℤ_stabilizeX_insertPoint`,
  `TauCeti.GridDiagram.alexanderTwoℤ_stabilizeX_insertPoint` and
  `TauCeti.GridDiagram.alexander_stabilizeX_insertPoint`: the gradings of a center state.
* `TauCeti.GridDiagram.maslovOℤ_stabilizeX_eq_of_isEmpty` and
  `TauCeti.GridDiagram.alexander_stabilizeX_eq_of_mem_XHomotopyRectangles`: a term `V^{O(r)} · x`
  of the `X`-homotopy into the center states has the bigrading of its source.

## References

This is the grading computation in the proof of stabilization invariance in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.2, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.2.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ}

/-! ### Point-pair counts of inserted states -/

variable (s b : Fin n) (x m : GridState n)

/-- The non-inversions of a state with the point `(s.succ, b.succ)` inserted. -/
private theorem card_lt_insertPoint_succ_succ :
    (Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 < p.2 ∧ x.insertPoint s.succ b.succ p.1 < x.insertPoint s.succ b.succ p.2).card =
      0 + (Finset.univ.filter fun d : Fin n => s < d ∧ b < x d).card +
        (Finset.univ.filter fun c : Fin n => c ≤ s ∧ x c ≤ b).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2).card := by
  rw [Fin.card_filter_prod_succAbove _ s.succ s.succ]
  simp only [GridState.insertPoint_apply_newColumn, GridState.insertPoint_apply_succAbove]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp
  all_goals
    congr 1; ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def,
      Fin.val_succAbove, Fin.val_succ]
    split_ifs <;> omega

/-- The non-inversions of a state with the point `(s.castSucc, b.castSucc)` inserted. -/
private theorem card_lt_insertPoint_castSucc_castSucc :
    (Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 < p.2 ∧ m.insertPoint s.castSucc b.castSucc p.1 <
        m.insertPoint s.castSucc b.castSucc p.2).card =
      0 + (Finset.univ.filter fun d : Fin n => s ≤ d ∧ b ≤ m d).card +
        (Finset.univ.filter fun c : Fin n => c < s ∧ m c < b).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ m p.1 < m p.2).card := by
  rw [Fin.card_filter_prod_succAbove _ s.castSucc s.castSucc]
  simp only [GridState.insertPoint_apply_newColumn, GridState.insertPoint_apply_succAbove]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp
  all_goals
    congr 1; ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def,
      Fin.val_succAbove, Fin.val_castSucc]
    split_ifs <;> omega

/-- The non-inversions of a state with the point `(s.succ, b.castSucc)` inserted. -/
private theorem card_lt_insertPoint_succ_castSucc :
    (Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 < p.2 ∧ m.insertPoint s.succ b.castSucc p.1 < m.insertPoint s.succ b.castSucc p.2).card =
      0 + (Finset.univ.filter fun d : Fin n => s < d ∧ b ≤ m d).card +
        (Finset.univ.filter fun c : Fin n => c ≤ s ∧ m c < b).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ m p.1 < m p.2).card := by
  rw [Fin.card_filter_prod_succAbove _ s.succ s.succ]
  simp only [GridState.insertPoint_apply_newColumn, GridState.insertPoint_apply_succAbove]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp
  all_goals
    congr 1; ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def,
      Fin.val_succAbove, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> omega

/-- The weak comparisons of a state with `(s.succ, b.succ)` inserted against a marking state with
`(s.castSucc, b.castSucc)` inserted. -/
private theorem card_le_insertPoint_succ_succ_castSucc_castSucc :
    (Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 ≤ p.2 ∧ x.insertPoint s.succ b.succ p.1 ≤ m.insertPoint s.castSucc b.castSucc p.2).card =
      0 + (Finset.univ.filter fun d : Fin n => s ≤ d ∧ b ≤ m d).card +
        (Finset.univ.filter fun c : Fin n => c ≤ s ∧ x c ≤ b).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ m p.2).card := by
  rw [Fin.card_filter_prod_succAbove _ s.succ s.castSucc]
  simp only [GridState.insertPoint_apply_newColumn, GridState.insertPoint_apply_succAbove]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp [Fin.le_def]
  all_goals
    congr 1; ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def,
      Fin.val_succAbove, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> omega

/-- The strict comparisons of a marking state with `(s.castSucc, b.castSucc)` inserted against a
state with `(s.succ, b.succ)` inserted. -/
private theorem card_lt_insertPoint_castSucc_castSucc_succ_succ :
    (Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 < p.2 ∧ m.insertPoint s.castSucc b.castSucc p.1 < x.insertPoint s.succ b.succ p.2).card =
      1 + (Finset.univ.filter fun d : Fin n => s < d ∧ b < x d).card +
        (Finset.univ.filter fun c : Fin n => c < s ∧ m c < b).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ m p.1 < x p.2).card := by
  rw [Fin.card_filter_prod_succAbove _ s.castSucc s.succ]
  simp only [GridState.insertPoint_apply_newColumn, GridState.insertPoint_apply_succAbove]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp [Fin.lt_def]
  all_goals
    congr 1; ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
      Fin.val_succAbove, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> omega

/-- The weak comparisons of a state with `(s.succ, b.succ)` inserted against a marking state with
`(s.succ, b.castSucc)` inserted. -/
private theorem card_le_insertPoint_succ_succ_succ_castSucc :
    (Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 ≤ p.2 ∧ x.insertPoint s.succ b.succ p.1 ≤ m.insertPoint s.succ b.castSucc p.2).card =
      0 + (Finset.univ.filter fun d : Fin n => s < d ∧ b ≤ m d).card +
        (Finset.univ.filter fun c : Fin n => c ≤ s ∧ x c ≤ b).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ m p.2).card := by
  rw [Fin.card_filter_prod_succAbove _ s.succ s.succ]
  simp only [GridState.insertPoint_apply_newColumn, GridState.insertPoint_apply_succAbove]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp [Fin.le_def]
  all_goals
    congr 1; ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def,
      Fin.val_succAbove, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> omega

/-- The strict comparisons of a marking state with `(s.succ, b.castSucc)` inserted against a
state with `(s.succ, b.succ)` inserted. -/
private theorem card_lt_insertPoint_succ_castSucc_succ_succ :
    (Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 < p.2 ∧ m.insertPoint s.succ b.castSucc p.1 < x.insertPoint s.succ b.succ p.2).card =
      0 + (Finset.univ.filter fun d : Fin n => s < d ∧ b < x d).card +
        (Finset.univ.filter fun c : Fin n => c ≤ s ∧ m c < b).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ m p.1 < x p.2).card := by
  rw [Fin.card_filter_prod_succAbove _ s.succ s.succ]
  simp only [GridState.insertPoint_apply_newColumn, GridState.insertPoint_apply_succAbove]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · simp
  all_goals
    congr 1; ext
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, Fin.le_def,
      Fin.val_succAbove, Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> omega

/-! ### The gradings of the center states -/

variable (G : GridDiagram n)

/-- **The `O`-Maslov grading of a center state.** Adding the center of the new block to a state
of `G` gives a state of the stabilization one lower in the `O`-Maslov grading. -/
theorem maslovOℤ_stabilizeX_insertPoint :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ (x.insertPoint s.succ (G.X s).succ) =
      G.maslovOℤ x - 1 := by
  rw [maslovOℤ_eq_card, maslovOℤ_eq_card, stabilizeX_O, card_lt_insertPoint_succ_succ,
    card_le_insertPoint_succ_succ_castSucc_castSucc,
    card_lt_insertPoint_castSucc_castSucc_succ_succ, card_lt_insertPoint_castSucc_castSucc]
  push_cast
  ring

/-- **The `X`-Maslov grading of a center state.** Adding the center of the new block to a state
of `G` gives a state of the stabilization with the same `X`-Maslov grading. -/
theorem maslovXℤ_stabilizeX_insertPoint :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovXℤ (x.insertPoint s.succ (G.X s).succ) =
      G.maslovXℤ x := by
  rw [maslovXℤ_eq_card, maslovXℤ_eq_card, stabilizeX_X,
    GridState.splitPoint_castSucc_eq_insertPoint, card_lt_insertPoint_succ_succ,
    card_le_insertPoint_succ_succ_succ_castSucc, card_lt_insertPoint_succ_castSucc_succ_succ,
    card_lt_insertPoint_succ_castSucc]
  push_cast
  ring

/-- **The Alexander grading of a center state**, in its doubled integer form. -/
theorem alexanderTwoℤ_stabilizeX_insertPoint :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexanderTwoℤ
        (x.insertPoint s.succ (G.X s).succ) =
      G.alexanderTwoℤ x - 2 := by
  rw [alexanderTwoℤ_def, alexanderTwoℤ_def, maslovOℤ_stabilizeX_insertPoint,
    maslovXℤ_stabilizeX_insertPoint]
  push_cast
  ring

/-- **The Alexander grading of a center state.** Adding the center of the new block to a state
of `G` gives a state of the stabilization one lower in the Alexander grading. -/
theorem alexander_stabilizeX_insertPoint :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander (x.insertPoint s.succ (G.X s).succ) =
      G.alexander x - 1 := by
  have h := (G.stabilizeX s.castSucc (G.X s).castSucc s).two_mul_alexander_eq_intCast
    (x.insertPoint s.succ (G.X s).succ)
  rw [alexanderTwoℤ_stabilizeX_insertPoint, Int.cast_sub, ← G.two_mul_alexander_eq_intCast] at h
  push_cast at h
  linarith

/-! ### The terms of the stabilization map -/

/-- An empty rectangle of the stabilization from a state `y` to a center state `x'` lowers the
`O`-Maslov grading by one once its weight `V^{O(r)}` is charged `-2` per variable, and `x'` lies
one below `x`: so the term `V^{O(r)} · x` has the `O`-Maslov grading of `y`. -/
theorem maslovOℤ_stabilizeX_eq_of_isEmpty {y : GridState (n + 1)}
    {r : GridRectangleBetween y (x.insertPoint s.succ (G.X s).succ)} (hr : r.IsEmpty) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ y =
      G.maslovOℤ x -
        2 * ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card := by
  have h := (G.stabilizeX s.castSucc (G.X s).castSucc s).maslovOℤ_sub_two_mul_card_OColumns hr
  rw [maslovOℤ_stabilizeX_insertPoint] at h
  omega

/-- A rectangle of an `X`-marking homotopy of the stabilization from a state `y` to a center
state `x'` lowers the Alexander grading by one once its weight `V^{O(r)}` is charged `-1` per
variable, and `x'` lies one below `x`: so the term `V^{O(r)} · x` has the Alexander grading of
`y`. -/
theorem alexander_stabilizeX_eq_of_mem_XHomotopyRectangles {k : Fin (n + 1)}
    {y : GridState (n + 1)} {r : GridRectangleBetween y (x.insertPoint s.succ (G.X s).succ)}
    (hr : r ∈ (G.stabilizeX s.castSucc (G.X s).castSucc s).XHomotopyRectangles k y
      (x.insertPoint s.succ (G.X s).succ)) :
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander y =
      G.alexander x -
        ((G.stabilizeX s.castSucc (G.X s).castSucc s).OColumns r.toGridRectangle).card := by
  have h :=
    (G.stabilizeX s.castSucc (G.X s).castSucc s).alexander_sub_card_OColumns_eq_alexander_sub_one hr
  rw [alexander_stabilizeX_insertPoint] at h
  linarith

end GridDiagram

end TauCeti
