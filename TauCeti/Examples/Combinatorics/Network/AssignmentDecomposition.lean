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

/-!
# A path--cycle decomposition with several supplies and demands

This example decomposes a nonnegative integer assignment on five vertices. Vertices `0` and `1`
each supply three units, vertices `3` and `4` each demand three units, and vertex `2` is balanced.
The assignment contains a positive two-arrow cycle between `2` and `3`.

Four weighted paths account for all supply and demand, while one weighted cycle accounts for the
remaining circulation. The example checks the assignment arrow by arrow, computes every vertex
excess, and verifies both the supply and demand weight identities. It demonstrates that cycle
components do not affect the imbalance recorded by the path components.
-/

namespace TauCeti.Examples.AssignmentDecomposition

open Finset

private abbrev Hom (_ _ : Fin 5) : Type := Unit

private def assignment : Assignment Hom ℤ := fun v w _ ↦
  ![![0, 0, 2, 0, 1],
    ![0, 0, 2, 1, 0],
    ![0, 0, 0, 3, 2],
    ![0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0]] v w

private def path₀₃ : ArrowWalk Hom 0 3 :=
  ((ArrowWalk.nil 0).cons (x := 2) ()).cons (x := 3) ()

private def path₀₄ : ArrowWalk Hom 0 4 :=
  (ArrowWalk.nil 0).cons (x := 4) ()

private def path₁₃ : ArrowWalk Hom 1 3 :=
  (ArrowWalk.nil 1).cons (x := 3) ()

private def path₁₄ : ArrowWalk Hom 1 4 :=
  ((ArrowWalk.nil 1).cons (x := 2) ()).cons (x := 4) ()

private def cycle₂₃ : ArrowWalk Hom 2 2 :=
  ((ArrowWalk.nil 2).cons (x := 3) ()).cons (x := 2) ()

private def paths : List (WeightedWalk Hom ℤ) :=
  [⟨0, 3, path₀₃, 2⟩, ⟨0, 4, path₀₄, 1⟩,
    ⟨1, 3, path₁₃, 1⟩, ⟨1, 4, path₁₄, 2⟩]

private def cycles : List (WeightedClosedWalk Hom ℤ) :=
  [⟨2, cycle₂₃, 1⟩]

private def decomposition : PathCycleDecomposition assignment where
  paths := paths
  cycles := cycles
  isPath_walk := by
    simp [paths, path₀₃, path₀₄, path₁₃, path₁₄,
      ArrowWalk.isPath_def, Quiver.Path.vertices_cons]
  isCycle_walk := by
    simp [cycles, cycle₂₃, ArrowWalk.isCycle_def, Quiver.Path.vertices_cons]
  weight_pos_of_mem_paths := by simp [paths]
  weight_pos_of_mem_cycles := by simp [cycles]
  excessAt_source_neg := by
    simp [paths, assignment, excessAt_def, Fin.sum_univ_succ]
  excessAt_target_pos := by
    simp [paths, assignment, excessAt_def, Fin.sum_univ_succ]
  sum_paths_add_sum_cycles := by
    funext v w e
    fin_cases v <;> fin_cases w <;>
      simp [paths, cycles, WeightedWalk.assignment_def, WeightedClosedWalk.assignment_def,
        assignment, path₀₃, path₀₄, path₁₃, path₁₄, cycle₂₃,
        Assignment.single_apply]

private theorem excessAt_assignment (v : Fin 5) :
    excessAt assignment v = ![-3, -3, 0, 3, 3] v := by
  fin_cases v <;> norm_num [assignment, excessAt_def, Fin.sum_univ_succ]

/-!
The four conclusions below exercise different parts of the decomposition interface: exact
reconstruction, the vertex imbalance, the two global weight identities, and the fact that the
cycle component is nonzero while carrying no excess.
-/

/-- There is a nonnegative assignment with two supply vertices, two demand vertices, and a
nonzero cycle component whose explicit path--cycle decomposition reconstructs the assignment and
realizes the supply and demand weight identities. -/
public theorem exists_two_supply_two_demand_decomposition :
    ∃ (f : Assignment (fun _ _ : Fin 5 ↦ Unit) ℤ) (D : PathCycleDecomposition f),
    (∀ v, excessAt f v = ![-3, -3, 0, 3, 3] v) ∧
    D.paths.length = 4 ∧ D.cycles.length = 1 ∧ D.cycleAssignment ≠ 0 := by
  refine ⟨assignment, decomposition, excessAt_assignment, by simp [decomposition, paths],
    by simp [decomposition, cycles], ?_⟩
  intro h
  have h₂₃ := congrArg (fun g : Assignment Hom ℤ ↦ g (x := 2) (y := 3) ()) h
  norm_num [decomposition, PathCycleDecomposition.cycleAssignment_def, cycles,
    WeightedClosedWalk.assignment_def, cycle₂₃, Assignment.single_apply] at h₂₃

-- Reconstruction is checked against the explicit matrix, rather than defining the assignment as
-- the sum of its displayed components.
example :
    ∀ v w, ∀ e : Hom v w,
      decomposition.pathAssignment e + decomposition.cycleAssignment e = assignment e :=
  fun v w e ↦ congrArg (fun g : Assignment Hom ℤ ↦ g (x := v) (y := w) e)
    decomposition.pathAssignment_add_cycleAssignment

-- The generic supply and demand identities both specialize at every vertex of the example.
example :
    (∀ v,
      ((decomposition.paths.filter fun p ↦ p.source = v).map WeightedWalk.weight).sum =
        (excessAt assignment v)⁻) ∧
    ∀ v,
      ((decomposition.paths.filter fun p ↦ p.target = v).map WeightedWalk.weight).sum =
        (excessAt assignment v)⁺ :=
  ⟨decomposition.sum_weight_filter_source_eq_negPart,
    decomposition.sum_weight_filter_target_eq_posPart⟩

-- Each supply contributes three units of path weight, and each demand receives three units.
example :
    ((decomposition.paths.filter fun p ↦ p.source = 0).map WeightedWalk.weight).sum = 3 ∧
    ((decomposition.paths.filter fun p ↦ p.source = 1).map WeightedWalk.weight).sum = 3 ∧
    ((decomposition.paths.filter fun p ↦ p.target = 3).map WeightedWalk.weight).sum = 3 ∧
    ((decomposition.paths.filter fun p ↦ p.target = 4).map WeightedWalk.weight).sum = 3 := by
  norm_num [decomposition, paths]

-- The cycle carries one unit in each direction and does not change any vertex excess.
example :
    decomposition.cycleAssignment (x := 2) (y := 3) () = 1 ∧
    decomposition.cycleAssignment (x := 3) (y := 2) () = 1 ∧
    ∀ v, excessAt decomposition.cycleAssignment v = 0 := by
  refine ⟨?_, ?_, fun v ↦
    (isCirculation_iff decomposition.cycleAssignment).1
      decomposition.isCirculation_cycleAssignment v⟩ <;>
    norm_num [decomposition, PathCycleDecomposition.cycleAssignment_def, cycles,
      WeightedClosedWalk.assignment_def, cycle₂₃, Assignment.single_apply]

end TauCeti.Examples.AssignmentDecomposition
