/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import TauCeti.Combinatorics.Network.Decomposition
public import TauCeti.Combinatorics.Network.Shift

/-!
# Sign conventions in path decompositions

Excess is incoming minus outgoing value, so in a path–cycle decomposition every path starts at a
vertex of negative excess and ends at a vertex of positive excess. These examples check that
convention in the two places where the sign is easy to get wrong.

On three vertices `s = 0`, `a = 1` and `t = 2`, the assignment sending two units along
`t → a → s` is capacity-feasible and conserved at `a`, so it is a bounded `s`–`t` assignment.
Its excess at the designated sink `t` is `-2`, so it is not an ordinary `s`–`t` flow. Terminal
exchange turns it into an ordinary `t`–`s` flow of value `2` with the same arrow values, and
every decomposition of that flow consists of paths from `t` to `s` of total weight `2`.

On the same three vertices, the prescribed excess `-2, 1, 1` makes `0` a supply vertex and `1`
and `2` demand vertices. The assignment sending one unit along each of `0 → 1` and `0 → 2`
realizes it, and every decomposition of that assignment has all its paths starting at the supply
vertex, with path weight `2` leaving it and path weight `1` entering each demand vertex.
-/

namespace TauCeti.Examples.DecompositionSigns

open Finset

private abbrev Hom (_ _ : Fin 3) : Type := Unit

/-! ### Negative value at the designated sink -/

/-- Capacity three on every arrow, including the loops. -/
private def cap : Assignment Hom ℤ := fun _ _ _ ↦ 3

/-- Two units along `2 → 1 → 0`, against the direction from `s = 0` to `t = 2`. -/
private def backwardFun : Assignment Hom ℤ := fun v w _ ↦
  ![![0, 0, 0],
    ![2, 0, 0],
    ![0, 2, 0]] v w

private def backward : BoundedFlow 0 cap 0 2 where
  toFun := backwardFun
  mem_Icc := ⟨fun v w _ ↦ by fin_cases v <;> fin_cases w <;> simp [backwardFun],
    fun v w _ ↦ by fin_cases v <;> fin_cases w <;> simp [backwardFun, cap]⟩
  conserve v hv0 hv2 := by
    fin_cases v
    · exact absurd rfl hv0
    · simp [backwardFun, excessAt_def, Fin.sum_univ_succ]
    · exact absurd rfl hv2

private theorem backward_val : backward.val = -2 := by
  simp [BoundedFlow.val_def, backward, backwardFun, excessAt_def, Fin.sum_univ_succ]

private theorem backward_val_nonpos : backward.val ≤ 0 := by
  rw [backward_val]
  norm_num

/-- The single path `2 → 1 → 0` of the exchanged flow. -/
private def backwardPath : ArrowWalk Hom 2 0 :=
  ((ArrowWalk.nil 2).cons (x := 1) ()).cons (x := 0) ()

private def exchangedDecomposition :
    PathCycleDecomposition (backward.swapFlow backward_val_nonpos).toFun where
  paths := [⟨2, 0, backwardPath, 2⟩]
  cycles := []
  isPath_walk := by
    simp [backwardPath, ArrowWalk.isPath_def, Quiver.Path.vertices_cons]
  isCycle_walk := by simp
  weight_pos_of_mem_paths := by simp
  weight_pos_of_mem_cycles := by simp
  excessAt_source_neg := by
    simp [backward, backwardFun, excessAt_def, Fin.sum_univ_succ]
  excessAt_target_pos := by
    simp [backward, backwardFun, excessAt_def, Fin.sum_univ_succ]
  sum_paths_add_sum_cycles := by
    funext v w e
    fin_cases v <;> fin_cases w <;>
      simp [WeightedWalk.assignment_def, backward, backwardFun, backwardPath,
        Assignment.single_apply]

/-- A capacity-feasible `0`–`2` assignment of value `-2` is an ordinary `2`–`0` flow of value `2`
after terminal exchange, with the same arrow values. Every path–cycle decomposition of it routes
all its path weight from `2` to `0`. -/
public theorem exists_terminal_exchange_decomposition :
    ∃ (cap : Assignment (fun _ _ : Fin 3 ↦ Unit) ℤ) (f : BoundedFlow 0 cap 0 2)
      (hf : f.val ≤ 0),
      f.val = -2 ∧ (f.swapFlow hf).toFun = f.toFun ∧ (f.swapFlow hf).val = 2 ∧
      ∀ D : PathCycleDecomposition (f.swapFlow hf).toFun,
        (∀ p ∈ D.paths, p.source = 2 ∧ p.target = 0) ∧
          (D.paths.map WeightedWalk.weight).sum = 2 := by
  refine ⟨cap, backward, backward_val_nonpos, backward_val, by simp, ?_, fun D ↦
    ⟨fun p hp ↦ ⟨D.source_eq_of_mem_paths hp, D.target_eq_of_mem_paths hp⟩, ?_⟩⟩
  · simp [backward_val]
  · simp [D.sum_weight_paths_eq_val, backward_val]

-- The same assignment is not an ordinary flow from `0` to `2`, whose value would be nonnegative.
example : ¬∃ f : Flow cap 0 2, f.toFun = backward.toFun := by
  rintro ⟨f, hf⟩
  have h := f.excessAt_sink_nonneg
  rw [hf, ← BoundedFlow.val_def, backward_val] at h
  norm_num at h

-- The exchanged flow has a decomposition consisting of the single path `2 → 1 → 0`.
example : exchangedDecomposition.paths.length = 1 ∧ exchangedDecomposition.cycles = [] :=
  ⟨rfl, rfl⟩

/-! ### Supply and demand signs of a prescribed excess -/

/-- The prescribed excess: vertex `0` supplies two units, vertices `1` and `2` demand one each. -/
private def demand : Fin 3 → ℤ := ![-2, 1, 1]

/-- One unit along each of `0 → 1` and `0 → 2`. -/
private def supplyFun : Assignment Hom ℤ := fun v w _ ↦
  ![![0, 1, 1],
    ![0, 0, 0],
    ![0, 0, 0]] v w

private def supplyFlow : ExcessFlow 0 cap demand :=
  ⟨supplyFun,
    ⟨fun v w _ ↦ by fin_cases v <;> fin_cases w <;> simp [supplyFun],
      fun v w _ ↦ by fin_cases v <;> fin_cases w <;> simp [supplyFun, cap]⟩,
    by
      funext v
      fin_cases v <;> simp [supplyFun, demand, excessAt_def, Fin.sum_univ_succ]⟩

private def supplyDecomposition : PathCycleDecomposition supplyFlow.val where
  paths := [⟨0, 1, (ArrowWalk.nil 0).cons (x := 1) (), 1⟩,
    ⟨0, 2, (ArrowWalk.nil 0).cons (x := 2) (), 1⟩]
  cycles := []
  isPath_walk := by simp [ArrowWalk.isPath_def, Quiver.Path.vertices_cons]
  isCycle_walk := by simp
  weight_pos_of_mem_paths := by simp
  weight_pos_of_mem_cycles := by simp
  excessAt_source_neg := by simp [supplyFlow, supplyFun, excessAt_def, Fin.sum_univ_succ]
  excessAt_target_pos := by simp [supplyFlow, supplyFun, excessAt_def, Fin.sum_univ_succ]
  sum_paths_add_sum_cycles := by
    funext v w e
    fin_cases v <;> fin_cases w <;>
      simp [WeightedWalk.assignment_def, supplyFlow, supplyFun, Assignment.single_apply]

/-- An assignment realizing the prescribed excess `-2, 1, 1` exists. In every path–cycle
decomposition of it, all paths start at the supply vertex `0`, whose prescribed excess is
negative; the path weight leaving `0` is `2`, and the path weight entering each of the demand
vertices `1` and `2` is `1`. -/
public theorem exists_prescribed_excess_decomposition :
    ∃ f : ExcessFlow (0 : Assignment (fun _ _ : Fin 3 ↦ Unit) ℤ) (fun _ _ _ ↦ 3) ![-2, 1, 1],
      ∀ D : PathCycleDecomposition f.val,
        (∀ p ∈ D.paths, p.source = 0) ∧
          ((D.paths.filter fun p ↦ p.source = 0).map WeightedWalk.weight).sum = 2 ∧
          ((D.paths.filter fun p ↦ p.target = 1).map WeightedWalk.weight).sum = 1 ∧
          ((D.paths.filter fun p ↦ p.target = 2).map WeightedWalk.weight).sum = 1 := by
  refine ⟨supplyFlow, fun D ↦ ⟨fun p hp ↦ ?_, ?_, ?_, ?_⟩⟩
  · have hneg := D.excessAt_source_neg p hp
    rw [supplyFlow.excessAt_eq] at hneg
    exact (by decide : ∀ v : Fin 3, demand v < 0 → v = 0) _ hneg
  · rw [D.sum_weight_filter_source_eq_negPart, supplyFlow.excessAt_eq]
    simp [demand]
  · rw [D.sum_weight_filter_target_eq_posPart, supplyFlow.excessAt_eq]
    simp [demand]
  · rw [D.sum_weight_filter_target_eq_posPart, supplyFlow.excessAt_eq]
    simp [demand]

-- The supply vertex has a decomposition with one unit path to each demand vertex.
example : supplyDecomposition.paths.map WeightedWalk.target = [1, 2] ∧
    supplyDecomposition.cycles = [] :=
  ⟨rfl, rfl⟩

end TauCeti.Examples.DecompositionSigns
