/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of identity stabilization

For `m ≤ n`, identity stabilization `TauCeti.stabilizeGL` sends an invertible `m × m` matrix `u`
to the invertible `n × n` matrix `diag (u, 1)`. Over a topological ring it is continuous for the
topology of the unit group: every entry of `diag (u, 1)`, and of its inverse `diag (u⁻¹, 1)`, is
either an entry of `u`, respectively `u⁻¹`, or constant. This lets loops of invertible matrices be
stabilized, for instance to compare a loop of size two with its images in all larger sizes.

## Main results

* `TauCeti.continuous_stabilizeGL`: identity stabilization is continuous.
-/

public section

open Matrix

namespace TauCeti

/-- **Identity stabilization is continuous**: `u ↦ diag (u, 1)` from `GL (Fin m) A` to
`GL (Fin n) A`. -/
@[fun_prop]
theorem continuous_stabilizeGL {A : Type*} [Ring A] [TopologicalSpace A] {m n : ℕ}
    (h : m ≤ n) : Continuous (stabilizeGL A h) := by
  -- Each entry of `diag (M, 1)` is an entry of `M` or constant, hence continuous in `M`.
  have entry (f : GL (Fin m) A → Matrix (Fin m) (Fin m) A) (hf : Continuous f) (i j : Fin n) :
      Continuous fun u => if hij : (i : ℕ) < m ∧ (j : ℕ) < m then f u ⟨i, hij.1⟩ ⟨j, hij.2⟩
        else (1 : Matrix (Fin n) (Fin n) A) i j := by
    by_cases hij : (i : ℕ) < m ∧ (j : ℕ) < m
    · simp only [hij, and_self, dite_true]
      exact (continuous_apply_apply _ _).comp hf
    · simp only [hij, dite_false]
      exact continuous_const
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · simpa only [Function.comp_apply, coe_stabilizeGL_apply] using
      entry _ Units.continuous_val i j
  · -- The inverse of `diag (u, 1)` is `diag (u⁻¹, 1)`.
    simpa only [Function.comp_apply, ← map_inv (stabilizeGL A h), coe_stabilizeGL_apply] using
      entry _ Units.continuous_coe_inv i j

end TauCeti
