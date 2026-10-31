/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Operator norms of bounded maps extended to completions

A bounded semilinear map `f : E →SL[σ₁₂] F` between seminormed spaces extends to the bounded
map `f.completion` between the completions, and, when `F` is complete and Hausdorff, to the
bounded map `f.fromCompletion` from the completion of `E` to `F`. Since `E` has dense image in
its completion and the canonical map preserves norms, neither extension changes the operator norm.

These are the continuous semilinear analogues of Mathlib's `NormedAddGroupHom.norm_completion`.
They make extension to completions an isometric operation, as needed for the norm-preserving
universal properties of completed normed constructions. Likewise, a linear isometric equivalence
extends to the linear isometric equivalence `e.completion` between the completions, the analogue
for equivalences of Mathlib's `LinearIsometry.completion`.

## Main results

* `ContinuousLinearMap.norm_completion`: `‖f.completion‖ = ‖f‖`.
* `ContinuousLinearMap.norm_fromCompletion`: `‖f.fromCompletion‖ = ‖f‖`.
* `LinearIsometryEquiv.completion`: the extension of a linear isometric equivalence to the
  completions.
-/

public section

open UniformSpace

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Extending a bounded semilinear map to the completions of its domain and codomain preserves
its operator norm. -/
@[simp]
theorem norm_completion (f : E →SL[σ₁₂] F) : ‖f.completion‖ = ‖f‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun x ↦ ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [completion_apply_coe, Completion.norm_coe] using f.le_opNorm x
  · simpa only [completion_apply_coe, Completion.norm_coe] using f.completion.le_opNorm x

/-- Extending a bounded semilinear map into a complete Hausdorff space to the completion of its
domain preserves its operator norm. -/
@[simp]
theorem norm_fromCompletion [T0Space F] [CompleteSpace F] (f : E →SL[σ₁₂] F) :
    ‖f.fromCompletion‖ = ‖f‖ := by
  refine le_antisymm (opNorm_le_bound _ (norm_nonneg f) fun x ↦ ?_)
    (opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
  · induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x => simpa only [fromCompletion_apply_coe, Completion.norm_coe] using f.le_opNorm x
  · simpa only [fromCompletion_apply_coe, Completion.norm_coe] using f.fromCompletion.le_opNorm x

end ContinuousLinearMap

namespace LinearIsometryEquiv

variable {𝕜 𝕜₂ E F : Type*} [NormedField 𝕜] [NormedField 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
  {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- Extend a linear isometric equivalence `e : E ≃ₛₗᵢ[σ₁₂] F` to a linear isometric equivalence
between the completions of `E` and `F`. -/
noncomputable def completion (e : E ≃ₛₗᵢ[σ₁₂] F) : Completion E ≃ₛₗᵢ[σ₁₂] Completion F :=
  e.toLinearEquiv.extendOfIsometry Completion.toComplₗᵢ.toLinearMap
    Completion.toComplₗᵢ.toLinearMap Completion.denseRange_coe Completion.denseRange_coe
    fun x ↦ by simp

/-- On `E`, the extension of `e` to the completions is `e`. -/
@[simp]
theorem completion_coe (e : E ≃ₛₗᵢ[σ₁₂] F) (x : E) : e.completion x = e x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- On `F`, the inverse of the extension of `e` to the completions is `e.symm`. -/
@[simp]
theorem completion_symm_coe (e : E ≃ₛₗᵢ[σ₁₂] F) (y : F) : e.completion.symm y = e.symm y :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ y

end LinearIsometryEquiv
