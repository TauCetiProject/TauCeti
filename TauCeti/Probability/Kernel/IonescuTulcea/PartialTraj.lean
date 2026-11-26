/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# Evaluating the trajectories of `partialTraj` at a fixed time

For a chain with state space `X j` at time `j`, a trajectory up to time `n` is a path
`Π j : Iic n, X j`, and `TauCeti.Probability.pathEval i hi` evaluates it at a time `i ≤ n`.
This file records how the law of the state at a fixed time behaves under Mathlib's
`ProbabilityTheory.Kernel.partialTraj`.

## Main definitions

* `TauCeti.Probability.pathEval`: evaluation of a path indexed by `Finset.Iic n` at a time `i ≤ n`.

## Main results

* `ProbabilityTheory.Kernel.partialTraj_map_pathEval`: the state at time `t ≤ b` of a trajectory
  up to time `b` has the same law as the state at time `t` of a trajectory up to time `t`.
* `ProbabilityTheory.Kernel.partialTraj_map_pathEval_left`: started at a path `y` up to time
  `a ≤ b`, the state at time `a` is `y a`.
* `ProbabilityTheory.Kernel.partialTraj_succ_map_pathEval`: started at a path up to time `n`, the
  state at time `n + 1` has law `κ n`.
-/

public section

open MeasureTheory Finset

namespace TauCeti.Probability

/-- Evaluation at time `i ≤ n` of a path indexed by the times `Finset.Iic n`. The state spaces
`X j` may depend on the time `j`. -/
def pathEval {n : ℕ} {X : Iic n → Type*} (i : ℕ) (hi : i ≤ n) (x : Π j, X j) :
    X ⟨i, mem_Iic.2 hi⟩ :=
  x ⟨i, mem_Iic.2 hi⟩

/-- Unfolding lemma for `pathEval`. -/
@[simp]
theorem pathEval_apply {n : ℕ} {X : Iic n → Type*} (i : ℕ) (hi : i ≤ n) (x : Π j, X j) :
    pathEval i hi x = x ⟨i, mem_Iic.2 hi⟩ := (rfl)

/-- Evaluation of a path at a fixed time is measurable. -/
@[fun_prop]
theorem measurable_pathEval {n : ℕ} {X : Iic n → Type*} [∀ j, MeasurableSpace (X j)] (i : ℕ)
    (hi : i ≤ n) : Measurable (pathEval (X := X) i hi) :=
  measurable_pi_apply _

end TauCeti.Probability

namespace ProbabilityTheory.Kernel

open TauCeti.Probability

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]

/-- The state at time `t ≤ b` of a trajectory up to time `b` only depends on the trajectory up to
time `t`. -/
theorem partialTraj_map_pathEval (a : ℕ) {b t : ℕ} (ht : t ≤ b) :
    (partialTraj κ a b).map (pathEval t ht) = (partialTraj κ a t).map (pathEval t le_rfl) := by
  rw [← partialTraj_map_frestrictLe₂ a ht]
  -- `pathEval t ht` is `pathEval t le_rfl ∘ frestrictLe₂ ht` by unfolding both sides.
  exact map_comp_right _ (Preorder.measurable_frestrictLe₂ ht) (measurable_pathEval t le_rfl)

/-- Started at a path `y` up to time `a ≤ b`, a trajectory up to time `b` is at time `a` in the
state `y a`. -/
theorem partialTraj_map_pathEval_left {a b : ℕ} (hab : a ≤ b) :
    (partialTraj κ a b).map (pathEval a hab) =
      deterministic (pathEval a le_rfl) (measurable_pathEval a le_rfl) := by
  rw [partialTraj_map_pathEval, partialTraj_self, id_map]

/-- One step of the trajectory: started at a path up to time `n`, the state at time `n + 1` has
law `κ n`. This is Mathlib's `ProbabilityTheory.Kernel.map_partialTraj_succ_self`, with its
evaluation map written as `pathEval`. -/
theorem partialTraj_succ_map_pathEval (n : ℕ) :
    (partialTraj κ n (n + 1)).map (pathEval (n + 1) le_rfl) = κ n :=
  map_partialTraj_succ_self n

end ProbabilityTheory.Kernel
