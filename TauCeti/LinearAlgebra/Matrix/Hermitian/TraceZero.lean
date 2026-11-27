/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The trace-free Hermitian matrices

Over `𝕜 = ℝ` or `ℂ`, the Hermitian matrices of trace zero (over `ℝ`, the trace-free symmetric
matrices) form a real vector subspace `Matrix.traceZeroSelfAdjoint n 𝕜` of the Hermitian matrices.
It is the Hermitian part of `𝔰𝔩(n, 𝕜)`: the space `𝔭₀` of the Cartan decomposition of the
special linear group, and the domain of the exponential coordinates on the positive-definite
matrices of determinant one.
-/

public section

namespace Matrix

variable (n 𝕜 : Type*) [Fintype n] [RCLike 𝕜]

/-- The **trace-free Hermitian matrices** (over `ℝ`, the trace-free symmetric matrices), a real
vector subspace of the Hermitian matrices. -/
def traceZeroSelfAdjoint : Submodule ℝ (selfAdjoint (Matrix n n 𝕜)) where
  carrier := {X | (X : Matrix n n 𝕜).trace = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, AddSubgroup.coe_add, trace_add] at hX hY ⊢
    rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' c X hX := by
    simp only [Set.mem_ofPred_eq, selfAdjoint.val_smul, trace_smul] at hX ⊢
    rw [hX, smul_zero]

variable {n 𝕜}

/-- Membership in the trace-free Hermitian matrices is the vanishing of the trace. -/
@[simp]
theorem mem_traceZeroSelfAdjoint {X : selfAdjoint (Matrix n n 𝕜)} :
    X ∈ traceZeroSelfAdjoint n 𝕜 ↔ (X : Matrix n n 𝕜).trace = 0 :=
  Iff.rfl

end Matrix
