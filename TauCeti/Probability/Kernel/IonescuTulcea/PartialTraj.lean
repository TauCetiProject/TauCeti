/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Evaluating the trajectories of `partialTraj` at a fixed time

For a chain on a fixed state space `α`, a trajectory up to time `n` is a path `Iic n → α`, and
`TauCeti.Probability.pathEval i hi` evaluates it at a time `i ≤ n`. This file records how the
law of the state at a fixed time behaves under Mathlib's `ProbabilityTheory.Kernel.partialTraj`.

## Main definitions

* `TauCeti.Probability.pathEval`: evaluation of a path indexed by `Finset.Iic n` at a time `i ≤ n`.

## Main results

* `ProbabilityTheory.Kernel.partialTraj_map_pathEval`: the state at time `t ≤ b` of a trajectory
  up to time `b` has the same law as the state at time `t` of a trajectory up to time `t`.
* `ProbabilityTheory.Kernel.partialTraj_map_pathEval_left`: started at a path `y` up to time
  `a ≤ b`, the state at time `a` is `y a`.
-/

public section

open MeasureTheory Finset

namespace TauCeti.Probability

/-- Evaluation at time `i ≤ n` of a path indexed by the times `Finset.Iic n`. -/
@[expose] def pathEval {α : Type*} {n : ℕ} (i : ℕ) (hi : i ≤ n) (x : Iic n → α) : α :=
  x ⟨i, mem_Iic.2 hi⟩

/-- Unfolding lemma for `pathEval`. -/
@[simp]
theorem pathEval_apply {α : Type*} {n : ℕ} (i : ℕ) (hi : i ≤ n) (x : Iic n → α) :
    pathEval i hi x = x ⟨i, mem_Iic.2 hi⟩ := (rfl)

/-- Evaluation of a path at a fixed time is measurable. -/
@[fun_prop]
theorem measurable_pathEval {α : Type*} [MeasurableSpace α] {n : ℕ} (i : ℕ) (hi : i ≤ n) :
    Measurable (pathEval (α := α) i hi) :=
  measurable_pi_apply _

end TauCeti.Probability

namespace ProbabilityTheory.Kernel

open TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] {κ : (n : ℕ) → Kernel (Iic n → α) α}
  [∀ n, IsMarkovKernel (κ n)]

/-- The state at time `t ≤ b` of a trajectory up to time `b` only depends on the trajectory up to
time `t`. -/
theorem partialTraj_map_pathEval (a : ℕ) {b t : ℕ} (ht : t ≤ b) :
    (partialTraj (X := fun _ ↦ α) κ a b).map (pathEval t ht) =
      (partialTraj (X := fun _ ↦ α) κ a t).map (pathEval t le_rfl) := by
  rw [← partialTraj_map_frestrictLe₂ a ht]
  -- `pathEval t ht` is `pathEval t le_rfl ∘ frestrictLe₂ ht` by unfolding both sides.
  exact map_comp_right _ (Preorder.measurable_frestrictLe₂ (X := fun _ ↦ α) ht)
    (measurable_pathEval (α := α) t le_rfl)

/-- Started at a path `y` up to time `a ≤ b`, a trajectory up to time `b` is at time `a` in the
state `y a`. -/
theorem partialTraj_map_pathEval_left {a b : ℕ} (hab : a ≤ b) :
    (partialTraj (X := fun _ ↦ α) κ a b).map (pathEval a hab) =
      deterministic (pathEval a le_rfl) (measurable_pathEval a le_rfl) := by
  rw [partialTraj_map_pathEval, partialTraj_self, id_map]

end ProbabilityTheory.Kernel
