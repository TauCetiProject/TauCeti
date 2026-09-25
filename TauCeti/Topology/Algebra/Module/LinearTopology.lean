/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.LinearTopology

/-!
# Separated linearly topologized modules

A T1 module with a linear topology is separated by its open submodules.
-/

public section

open Filter Topology

namespace TauCeti

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsLinearTopology R M]

variable (R) in
/-- **Linearly topologized modules are separated by their open submodules.** In a T1 module whose
topology is `R`-linear, an element lying in every open submodule is `0`. -/
theorem eq_zero_of_forall_isOpen_submodule_mem [ContinuousAdd M] [T1Space M] {x : M}
    (h : ∀ N : Submodule R M, IsOpen (N : Set M) → x ∈ N) : x = 0 := by
  by_contra hx
  obtain ⟨N, hN, hNx⟩ := (IsLinearTopology.hasBasis_open_submodule R).mem_iff.mp
    (isOpen_compl_singleton.mem_nhds (Ne.symm hx))
  exact hNx (h N hN) rfl

end TauCeti
