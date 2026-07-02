/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.DifferentialSquareSupport

/-!
# Backtracking in the two-step grid differential support

The support of the square of the fully blocked grid differential is already bounded by
`GridState.twoStepColumnSwapNeighbors`: states reached from `x` by two nontrivial column
transpositions. This file records the first exact feature of that two-step support. A path that
swaps the same pair of columns twice returns to the starting state, so the source state appears in
its own two-step neighbour set exactly when the grid has at least two columns.

This is small but useful bookkeeping for the later `∂² = 0` rectangle-pairing argument: diagonal
coefficients of `∂²` are precisely the backtracking part of the two-step search space, while grids
of size `0` and `1` have no such two-step targets at all.

## Main results

* `TauCeti.GridState.mem_twoStepColumnSwapNeighbors_of_backtrack`: swapping a pair of distinct
  columns and then swapping it back puts `x` in its own two-step neighbour set.
* `TauCeti.GridState.self_mem_twoStepColumnSwapNeighbors_iff_exists_pair`: this is possible
  exactly when there is a distinct pair of columns.
* `TauCeti.GridState.self_mem_twoStepColumnSwapNeighbors_iff_two_le`: equivalently, exactly when
  `2 ≤ n`.
* `TauCeti.GridDiagram.fullyBlockedDifferential_sq_single_apply_eq_zero_self_of_le_one`: the
  diagonal coefficient of `∂²` on a generator is zero in grid size at most `1`.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3,
"The complexes and `∂² = 0`", where the square-zero proof pairs two-step rectangle
decompositions. The column-transposition model of rectangle targets follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- Swapping a distinct pair of columns gives a column-swap neighbour. -/
theorem swapColumns_mem_columnSwapNeighbors (x : GridState n) {a b : Fin n} (hab : a ≠ b) :
    x.swapColumns a b ∈ x.columnSwapNeighbors := by
  rw [mem_columnSwapNeighbors]
  exact ⟨a, b, hab, rfl⟩

/-- If `y` is a column-swap neighbour of `x`, then `x` is a column-swap neighbour of `y`.

This is the elementary reversibility of a rectangle target: the same pair of side columns swaps
back to the source state. -/
theorem mem_columnSwapNeighbors_comm {x y : GridState n} :
    y ∈ x.columnSwapNeighbors ↔ x ∈ y.columnSwapNeighbors := by
  constructor
  · rw [mem_columnSwapNeighbors]
    rintro ⟨a, b, hab, rfl⟩
    rw [mem_columnSwapNeighbors]
    exact ⟨a, b, hab, by simp⟩
  · rw [mem_columnSwapNeighbors]
    rintro ⟨a, b, hab, hxy⟩
    rw [mem_columnSwapNeighbors]
    refine ⟨a, b, hab, ?_⟩
    rw [hxy]
    simp

/-- Swapping a distinct pair of columns and then swapping the same pair back puts the source state
in its own two-step column-swap neighbour set. -/
theorem mem_twoStepColumnSwapNeighbors_of_backtrack (x : GridState n) {a b : Fin n}
    (hab : a ≠ b) : x ∈ x.twoStepColumnSwapNeighbors := by
  rw [mem_twoStepColumnSwapNeighbors]
  refine ⟨x.swapColumns a b, x.swapColumns_mem_columnSwapNeighbors hab, ?_⟩
  rw [mem_columnSwapNeighbors]
  exact ⟨a, b, hab, by simp⟩

/-- The source state appears in its own two-step neighbour set exactly when there is a distinct
pair of grid columns. -/
theorem self_mem_twoStepColumnSwapNeighbors_iff_exists_pair (x : GridState n) :
    x ∈ x.twoStepColumnSwapNeighbors ↔ ∃ a b : Fin n, a ≠ b := by
  constructor
  · intro hx
    rw [mem_twoStepColumnSwapNeighbors] at hx
    obtain ⟨y, hy, _hyx⟩ := hx
    rw [mem_columnSwapNeighbors] at hy
    exact hy.imp fun a ha => ha.imp fun b hb => hb.1
  · rintro ⟨a, b, hab⟩
    exact x.mem_twoStepColumnSwapNeighbors_of_backtrack hab

/-- If the grid has at least two columns, the source state is a two-step neighbour of itself. -/
theorem self_mem_twoStepColumnSwapNeighbors_of_two_le (x : GridState n) (hn : 2 ≤ n) :
    x ∈ x.twoStepColumnSwapNeighbors := by
  rw [self_mem_twoStepColumnSwapNeighbors_iff_exists_pair]
  refine ⟨⟨0, Nat.lt_of_lt_of_le (by decide) hn⟩,
    ⟨1, Nat.lt_of_lt_of_le (by decide) hn⟩, ?_⟩
  intro h
  exact Nat.zero_ne_one (congrArg Fin.val h)

/-- The source state is a two-step neighbour of itself exactly in grid size at least two. -/
theorem self_mem_twoStepColumnSwapNeighbors_iff_two_le (x : GridState n) :
    x ∈ x.twoStepColumnSwapNeighbors ↔ 2 ≤ n := by
  rw [self_mem_twoStepColumnSwapNeighbors_iff_exists_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    have hcard : 1 < Fintype.card (Fin n) :=
      Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    exact Nat.succ_le_of_lt (by simpa [Fintype.card_fin] using hcard)
  · intro hn
    refine ⟨⟨0, Nat.lt_of_lt_of_le (by decide) hn⟩,
      ⟨1, Nat.lt_of_lt_of_le (by decide) hn⟩, ?_⟩
    intro h
    exact Nat.zero_ne_one (congrArg Fin.val h)

/-- In grid size at most `1`, the source state is not a two-step neighbour of itself. -/
theorem self_notMem_twoStepColumnSwapNeighbors_of_le_one (x : GridState n) (hn : n ≤ 1) :
    x ∉ x.twoStepColumnSwapNeighbors := by
  rw [self_mem_twoStepColumnSwapNeighbors_iff_two_le]
  omega

/-- In grid size `0`, the source state is not a two-step neighbour of itself. -/
@[simp]
theorem self_notMem_twoStepColumnSwapNeighbors_zero (x : GridState 0) :
    x ∉ x.twoStepColumnSwapNeighbors :=
  x.self_notMem_twoStepColumnSwapNeighbors_of_le_one (Nat.zero_le 1)

/-- In grid size `1`, the source state is not a two-step neighbour of itself. -/
@[simp]
theorem self_notMem_twoStepColumnSwapNeighbors_one (x : GridState 1) :
    x ∉ x.twoStepColumnSwapNeighbors :=
  x.self_notMem_twoStepColumnSwapNeighbors_of_le_one le_rfl

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- In grid size at most `1`, the diagonal coefficient of `∂²` on a generator is zero.

This is the coefficient-level form of the fact that there are no nontrivial two-step
backtracking paths when there are not two distinct columns to swap. -/
theorem fullyBlockedDifferential_sq_single_apply_eq_zero_self_of_le_one
    (hn : n ≤ 1) (x : GridState n) :
    G.fullyBlockedDifferential (G.fullyBlockedDifferential (Finsupp.single x 1)) x = 0 :=
  G.fullyBlockedDifferential_sq_single_apply_eq_zero_of_notMem_twoStep x
    (x.self_notMem_twoStepColumnSwapNeighbors_of_le_one hn)

/-- In grid size `0`, the diagonal coefficient of `∂²` on a generator is zero. -/
@[simp]
theorem fullyBlockedDifferential_sq_single_apply_eq_zero_self_zero
    (G : GridDiagram 0) (x : GridState 0) :
    G.fullyBlockedDifferential (G.fullyBlockedDifferential (Finsupp.single x 1)) x = 0 :=
  G.fullyBlockedDifferential_sq_single_apply_eq_zero_self_of_le_one (Nat.zero_le 1) x

/-- In grid size `1`, the diagonal coefficient of `∂²` on a generator is zero. -/
@[simp]
theorem fullyBlockedDifferential_sq_single_apply_eq_zero_self_one
    (G : GridDiagram 1) (x : GridState 1) :
    G.fullyBlockedDifferential (G.fullyBlockedDifferential (Finsupp.single x 1)) x = 0 :=
  G.fullyBlockedDifferential_sq_single_apply_eq_zero_self_of_le_one le_rfl x

end GridDiagram

end TauCeti
