/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.CompletelyPositive
import Mathlib.LinearAlgebra.Matrix.Permutation
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Checks: multiplicativity defects of completely positive contractions

These examples compute the 2-norm defect `d₂(φ, a) = Re tr_k(φ(a⋆a) - φ(a)⋆φ(a))` of two
completely positive contractions into `M₁`, with matrix units `e_ij`:

* for the compression `φ(x) = x₁₁ : M₂ → M₁`, the product estimate
  `‖φ(ab) - φ(a)φ(b)‖₂ ≤ d₂(φ, a⋆)^{1/2} ‖b‖`
  (`CompletelyPositiveMap.normalizedTwoNorm_map_mul_sub_le'`) is attained at `a = e₁₂`,
  `b = e₂₁`, where both sides are `1`, and both sides are `0` at `a = e₂₁`, `b = e₁₂`;
* for the normalized trace `tr_n : M_n → M₁`, `d₂(tr_n, e_ij) = 1/n` for `i ≠ j`, while
  `d₂(tr_n, u) = 1 - |tr_n u|²` for a unitary `u`, which is `1` for the matrix of a permutation
  without fixed points.

Indices are written from `0`, so `e₁₂` is `matrixUnit 0 1`.
-/

public section

noncomputable section

open CStarMatrix CompletelyPositiveMap Matrix
open scoped CStarAlgebra ComplexOrder

namespace TauCeti.Examples.DefectChecks

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The compression `x ↦ x₁₁ : M₂ → M₁` -/

-- At `a = e₁₂`, `b = e₂₁` both sides of the product estimate are `1`.
example : normalizedTwoNorm (diagEntryCP 0 (matrixUnit (0 : Fin 2) 1 * matrixUnit 1 0) -
      diagEntryCP 0 (matrixUnit (0 : Fin 2) 1) * diagEntryCP 0 (matrixUnit (1 : Fin 2) 0)) = 1 ∧
    √((diagEntryCP (0 : Fin 2)).twoNormDefect (star (matrixUnit 0 1))) *
      ‖matrixUnit (1 : Fin 2) 0‖ = 1 := by
  rw [diagEntryCP_def, PositiveLinearMap.normalizedTwoNorm_toCompletelyPositiveMapOfId_mul_sub,
    PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapOfId, star_star, star_matrixUnit,
    matrixUnit_mul_matrixUnit, norm_matrixUnit]
  simp

-- At `a = e₂₁`, `b = e₁₂` both sides of the product estimate are `0`.
example : normalizedTwoNorm (diagEntryCP 0 (matrixUnit (1 : Fin 2) 0 * matrixUnit 0 1) -
      diagEntryCP 0 (matrixUnit (1 : Fin 2) 0) * diagEntryCP 0 (matrixUnit (0 : Fin 2) 1)) = 0 ∧
    √((diagEntryCP (0 : Fin 2)).twoNormDefect (star (matrixUnit 1 0))) *
      ‖matrixUnit (0 : Fin 2) 1‖ = 0 := by
  rw [diagEntryCP_def, PositiveLinearMap.normalizedTwoNorm_toCompletelyPositiveMapOfId_mul_sub,
    PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapOfId, star_star, star_matrixUnit,
    matrixUnit_mul_matrixUnit]
  simp

/-! ### The normalized trace `tr_n : M_n → M₁` -/

-- The defect of the trace at an off-diagonal matrix unit is `1/n`.
example {i j : n} (h : i ≠ j) :
    normalizedTraceCP.twoNormDefect (matrixUnit i j) = (Fintype.card n : ℝ)⁻¹ := by
  rw [normalizedTraceCP_def, PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapOfId,
    star_matrixUnit, matrixUnit_mul_matrixUnit]
  simp [h]

-- At a unitary, the defect of the trace is `1 - |tr_n u|²`.
example [Nonempty n] {u : CStarMatrix n n ℂ} (hu : u ∈ unitary (CStarMatrix n n ℂ)) :
    normalizedTraceCP.twoNormDefect u = 1 - ‖normalizedTrace u‖ ^ 2 :=
  twoNormDefect_normalizedTraceCP_of_mem_unitary hu

-- At the matrix of a permutation without fixed points, the defect of the trace is `1`.
example [Nonempty n] (σ : Equiv.Perm n) (hσ : ∀ i, σ i ≠ i) :
    normalizedTraceCP.twoNormDefect (ofMatrixStarAlgEquiv (σ.permMatrix ℂ)) = 1 := by
  have hu := Unitary.map_mem ofMatrixStarAlgEquiv (permMatrix_mem_unitary (R := ℂ) σ)
  have htr : normalizedTrace (ofMatrixStarAlgEquiv (σ.permMatrix ℂ)) = 0 := by
    rw [normalizedTrace_def, ← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.symm_apply_apply,
      trace_permutation]
    have : Function.fixedPoints σ = ∅ := Set.eq_empty_of_forall_notMem hσ
    simp [this]
  rw [twoNormDefect_normalizedTraceCP_of_mem_unitary hu, htr]
  simp

end TauCeti.Examples.DefectChecks
