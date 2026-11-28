/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.Matrix

/-!
# Shifted and scaled entry arrays

Scaling by the reciprocal square root of the dimension and adding a deterministic
matrix gives the inputs to Hermitian dilation in the circular-law argument.
-/

public section

namespace Matrix

/-- Scale a square array of entries by the reciprocal square root of its dimension and add
the deterministic matrix `D`. -/
noncomputable def addInvSqrtCardSmulEntries {n : Type*} [Fintype n]
    (D : Matrix n n ℂ) (x : n × n → ℂ) : Matrix n n ℂ :=
  D + (Real.sqrt (Fintype.card n))⁻¹ • Matrix.of (fun i j ↦ x (i, j))

theorem addInvSqrtCardSmulEntries_def {n : Type*} [Fintype n]
    (D : Matrix n n ℂ) (x : n × n → ℂ) :
    D.addInvSqrtCardSmulEntries x =
      D + (Real.sqrt (Fintype.card n))⁻¹ • Matrix.of (fun i j ↦ x (i, j)) := (rfl)

/-- Scaling an array by a fixed factor and adding a fixed shift is continuous in the entries. -/
theorem continuous_addInvSqrtCardSmulEntries {n : Type*} [Fintype n]
    (D : Matrix n n ℂ) : Continuous D.addInvSqrtCardSmulEntries := by
  unfold addInvSqrtCardSmulEntries
  fun_prop

end Matrix
