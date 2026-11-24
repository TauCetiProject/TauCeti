/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.CompletelyPositive
import Mathlib.LinearAlgebra.Matrix.Permutation

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

Indices are written from `0`, so `e₁₂` is `unit 0 1`.
-/

public section

noncomputable section

open CStarMatrix CompletelyPositiveMap Matrix
open scoped CStarAlgebra ComplexOrder

namespace TauCeti.Examples.DefectChecks

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix unit `e_ij`. -/
abbrev unit (i j : n) : CStarMatrix n n ℂ := ofMatrixStarAlgEquiv (single i j 1)

private theorem unit_mul_unit (i j k : n) : unit i j * unit j k = unit i k := by
  rw [← map_mul, single_mul_single_same, one_mul]

private theorem star_unit (i j : n) : star (unit i j) = unit j i := by
  rw [← map_star, Matrix.star_eq_conjTranspose, conjTranspose_single, star_one]

private theorem unit_apply (i j k l : n) : unit i j k l = if i = k ∧ j = l then 1 else 0 := by
  simp [unit, ← ofMatrix_eq_ofMatrixStarAlgEquiv, single_apply]

private theorem normalizedTrace_unit (i j : n) :
    normalizedTrace (unit i j) = if i = j then (Fintype.card n : ℂ)⁻¹ else 0 := by
  rw [normalizedTrace_def, unit, ← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.symm_apply_apply]
  split_ifs with h
  · rw [h, trace_single_eq_same, mul_one]
  · rw [trace_single_eq_of_ne _ _ _ h, mul_zero]

/-- A matrix unit has norm one: `e_jj` is a nonzero projection and `e_ij⋆ e_ij = e_jj`. -/
private theorem norm_unit (i j : n) : ‖unit i j‖ = 1 := by
  have hp : ‖unit j j‖ = 1 := by
    have h := CStarRing.norm_star_mul_self (x := unit j j)
    rw [star_unit, unit_mul_unit] at h
    have hne : unit j j ≠ 0 := fun h0 => by simpa [unit_apply] using congrFun (congrFun h0 j) j
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hne) (h.symm.trans (mul_one _).symm)
  have h := CStarRing.norm_star_mul_self (x := unit i j)
  rw [star_unit, unit_mul_unit, hp] at h
  nlinarith [norm_nonneg (unit i j)]

/-! ### The compression `x ↦ x₁₁ : M₂ → M₁` -/

-- At `a = e₁₂`, `b = e₂₁` both sides of the product estimate are `1`.
example : normalizedTwoNorm (diagEntryCP 0 (unit (0 : Fin 2) 1 * unit 1 0) -
      diagEntryCP 0 (unit (0 : Fin 2) 1) * diagEntryCP 0 (unit (1 : Fin 2) 0)) = 1 ∧
    √((diagEntryCP (0 : Fin 2)).twoNormDefect (star (unit 0 1))) * ‖unit (1 : Fin 2) 0‖ = 1 := by
  rw [diagEntryCP_def, PositiveLinearMap.normalizedTwoNorm_toCompletelyPositiveMapMatrixOne_mul_sub,
    PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapMatrixOne, star_star, star_unit,
    unit_mul_unit, norm_unit]
  simp [unit_apply]

-- At `a = e₂₁`, `b = e₁₂` both sides of the product estimate are `0`.
example : normalizedTwoNorm (diagEntryCP 0 (unit (1 : Fin 2) 0 * unit 0 1) -
      diagEntryCP 0 (unit (1 : Fin 2) 0) * diagEntryCP 0 (unit (0 : Fin 2) 1)) = 0 ∧
    √((diagEntryCP (0 : Fin 2)).twoNormDefect (star (unit 1 0))) * ‖unit (0 : Fin 2) 1‖ = 0 := by
  rw [diagEntryCP_def, PositiveLinearMap.normalizedTwoNorm_toCompletelyPositiveMapMatrixOne_mul_sub,
    PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapMatrixOne, star_star, star_unit,
    unit_mul_unit]
  simp [unit_apply]

/-! ### The normalized trace `tr_n : M_n → M₁` -/

-- The defect of the trace at an off-diagonal matrix unit is `1/n`.
example {i j : n} (h : i ≠ j) :
    normalizedTraceCP.twoNormDefect (unit i j) = (Fintype.card n : ℝ)⁻¹ := by
  rw [normalizedTraceCP_def, PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapMatrixOne,
    star_unit, unit_mul_unit]
  simp [normalizedTrace_unit, h]

/-- At a unitary, the defect of the trace is `1 - |tr_n u|²`. -/
private theorem twoNormDefect_normalizedTraceCP_of_mem_unitary [Nonempty n]
    {u : CStarMatrix n n ℂ} (hu : u ∈ unitary (CStarMatrix n n ℂ)) :
    normalizedTraceCP.twoNormDefect u = 1 - ‖normalizedTrace u‖ ^ 2 := by
  rw [normalizedTraceCP_def, PositiveLinearMap.twoNormDefect_toCompletelyPositiveMapMatrixOne,
    Unitary.star_mul_self_of_mem hu]
  simp

example [Nonempty n] {u : CStarMatrix n n ℂ} (hu : u ∈ unitary (CStarMatrix n n ℂ)) :
    normalizedTraceCP.twoNormDefect u = 1 - ‖normalizedTrace u‖ ^ 2 :=
  twoNormDefect_normalizedTraceCP_of_mem_unitary hu

-- At the matrix of a permutation without fixed points, the defect of the trace is `1`.
example [Nonempty n] (σ : Equiv.Perm n) (hσ : ∀ i, σ i ≠ i) :
    normalizedTraceCP.twoNormDefect (ofMatrixStarAlgEquiv (σ.permMatrix ℂ)) = 1 := by
  have hstar : star (ofMatrixStarAlgEquiv (σ.permMatrix ℂ)) =
      ofMatrixStarAlgEquiv (σ⁻¹.permMatrix ℂ) := by
    rw [← map_star, Matrix.star_eq_conjTranspose, conjTranspose_permMatrix]
  have hu : ofMatrixStarAlgEquiv (σ.permMatrix ℂ) ∈ unitary (CStarMatrix n n ℂ) := by
    rw [Unitary.mem_iff, hstar, ← map_mul, ← map_mul, ← permMatrix_mul, ← permMatrix_mul,
      mul_inv_cancel, inv_mul_cancel, permMatrix_one, map_one]
    exact ⟨rfl, rfl⟩
  have htr : normalizedTrace (ofMatrixStarAlgEquiv (σ.permMatrix ℂ)) = 0 := by
    rw [normalizedTrace_def, ← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.symm_apply_apply,
      trace_permutation]
    have : Function.fixedPoints σ = ∅ := Set.eq_empty_of_forall_notMem hσ
    simp [this]
  rw [twoNormDefect_normalizedTraceCP_of_mem_unitary hu, htr]
  simp

end TauCeti.Examples.DefectChecks
