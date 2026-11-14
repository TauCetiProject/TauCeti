/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
public import TauCeti.Combinatorics.Network.Decomposition

/-!
# Path–cycle decompositions of zero-excess assignments

A path–cycle decomposition may have empty families of paths and of cycles, and its cycles may be
loops. These examples exercise both conventions on two vertices `0` and `1`, with one arrow for
each ordered pair, including a loop at each vertex.

The zero assignment has the decomposition with no paths and no cycles, and this is its only
decomposition. The assignment with one unit on the loop at `0` and two units on each of the arrows
`0 → 1` and `1 → 0` is nonnegative and has zero excess everywhere. Every decomposition of it
therefore has no paths, its cycles account for the whole assignment, and one of its cycles
traverses the loop. An explicit decomposition consists of the loop with weight one and the
two-arrow cycle with weight two.
-/

namespace TauCeti.Examples.CirculationDecomposition

open Finset

private abbrev Hom (_ _ : Fin 2) : Type := Unit

/-! ### The zero assignment -/

/-- The decomposition of the zero assignment with no components. -/
private def emptyDecomposition : PathCycleDecomposition (0 : Assignment Hom ℤ) where
  paths := []
  cycles := []
  isPath_walk := by simp
  isCycle_walk := by simp
  weight_pos_of_mem_paths := by simp
  weight_pos_of_mem_cycles := by simp
  excessAt_source_neg := by simp
  excessAt_target_pos := by simp
  sum_paths_add_sum_cycles := by simp

/-- The zero assignment has a path–cycle decomposition, and every one of them has empty families
of paths and cycles. -/
public theorem nonempty_pathCycleDecomposition_zero_and_forall_eq_nil :
    Nonempty (PathCycleDecomposition (0 : Assignment (fun _ _ : Fin 2 ↦ Unit) ℤ)) ∧
      ∀ D : PathCycleDecomposition (0 : Assignment (fun _ _ : Fin 2 ↦ Unit) ℤ),
        D.paths = [] ∧ D.cycles = [] :=
  ⟨⟨emptyDecomposition⟩, fun D ↦ D.paths_eq_nil_and_cycles_eq_nil_iff.2 rfl⟩

/-! ### A circulation through a loop -/

/-- One unit on the loop at `0` and two units on each of `0 → 1` and `1 → 0`. -/
private def circulation : Assignment Hom ℤ := fun v w _ ↦
  ![![1, 2],
    ![2, 0]] v w

private theorem circulation_nonneg : 0 ≤ circulation := fun v w _ ↦ by
  fin_cases v <;> fin_cases w <;> simp [circulation]

private theorem isCirculation_circulation : IsCirculation circulation := by
  refine (isCirculation_iff _).2 fun v ↦ ?_
  fin_cases v <;> simp [circulation, excessAt_def, Fin.sum_univ_succ]

/-- The one-arrow cycle along the loop at `0`. -/
private def loopCycle : ArrowWalk Hom 0 0 :=
  (ArrowWalk.nil 0).cons (x := 0) ()

/-- The two-arrow cycle `0 → 1 → 0`. -/
private def swapCycle : ArrowWalk Hom 0 0 :=
  ((ArrowWalk.nil 0).cons (x := 1) ()).cons (x := 0) ()

private def circulationDecomposition : PathCycleDecomposition circulation where
  paths := []
  cycles := [⟨0, loopCycle, 1⟩, ⟨0, swapCycle, 2⟩]
  isPath_walk := by simp
  isCycle_walk := by
    simp [loopCycle, swapCycle, ArrowWalk.isCycle_def, Quiver.Path.vertices_cons]
  weight_pos_of_mem_paths := by simp
  weight_pos_of_mem_cycles := by simp
  excessAt_source_neg := by simp
  excessAt_target_pos := by simp
  sum_paths_add_sum_cycles := by
    funext v w e
    fin_cases v <;> fin_cases w <;>
      simp [WeightedClosedWalk.assignment_def, circulation, loopCycle, swapCycle,
        Assignment.single_apply]

/-- A nonnegative assignment of zero excess with positive value on a loop has a path–cycle
decomposition. Every such decomposition has no paths, its cycles add up to the whole assignment,
and one of its cycles traverses the loop. -/
public theorem exists_loop_circulation_decomposition :
    ∃ f : Assignment (fun _ _ : Fin 2 ↦ Unit) ℤ,
      0 ≤ f ∧ IsCirculation f ∧ f (x := 0) (y := 0) () = 1 ∧
      Nonempty (PathCycleDecomposition f) ∧
      ∀ D : PathCycleDecomposition f, D.paths = [] ∧ D.cycleAssignment = f ∧
        ∃ c ∈ D.cycles, (⟨0, 0, ()⟩ : Σ _ _ : Fin 2, Unit) ∈ c.walk.arrows := by
  refine ⟨circulation, circulation_nonneg, isCirculation_circulation, rfl,
    ⟨circulationDecomposition⟩, fun D ↦ ?_⟩
  have hpaths := D.paths_eq_nil isCirculation_circulation
  have hcycles : D.cycleAssignment = circulation := by
    simpa [PathCycleDecomposition.pathAssignment_def, hpaths] using
      D.pathAssignment_add_cycleAssignment
  refine ⟨hpaths, hcycles, ?_⟩
  by_contra h
  push Not at h
  have hloop := congrArg (fun g : Assignment Hom ℤ ↦ g (x := 0) (y := 0) ()) hcycles
  simp only [PathCycleDecomposition.cycleAssignment_def, Pi.list_sum_apply, List.map_map] at hloop
  rw [List.sum_eq_zero fun a ha ↦ ?_] at hloop
  · simp [circulation] at hloop
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    simpa [WeightedClosedWalk.assignment_def] using
      walkAssignment_eq_zero_of_notMem c.walk c.weight (h c hc)

-- The explicit decomposition uses the loop as a cycle of weight one.
example : circulationDecomposition.cycles.map (fun c ↦ (c.walk.length, c.weight)) =
    [(1, 1), (2, 2)] := by
  simp [circulationDecomposition, loopCycle, swapCycle]

end TauCeti.Examples.CirculationDecomposition
