/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion
public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology

/-!
# Ultraweak continuity of tensor-product amplifications and slice maps

Conjugating operator amplifications into Hilbert-sum ampliations `lp.ampliation` via a Hilbert basis
of the completed passive factor, and expressing slice maps via pure-tensor creation maps and their
adjoints, this file proves ultraweak continuity on completed Hilbert tensor products:
* `TauCeti.ContinuousLinearMapUltraweak.continuous_rTensorCompletion` and
  `continuous_lTensorCompletion`: `A ↦ A ⊗ 1` and `A ↦ 1 ⊗ A` are ultraweakly continuous with no
  completeness, separability, or nontriviality on the passive factor.
* `TauCeti.ContinuousLinearMapUltraweak.continuous_sliceRight` and `continuous_sliceLeft`.
-/

public section
open UniformSpace TensorProduct
open scoped TensorProduct

namespace TauCeti.ContinuousLinearMapUltraweak
variable {𝕜 E E₁ E₂ F F₁ F₂ G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
/-- Left-factor amplification `A ↦ A ⊗ 1` (`ContinuousLinearMap.rTensorCompletion G`) between
complete spaces `E` and `F` is ultraweakly continuous for any inner product space `G` (without
separability, nontriviality, or completeness assumptions on `G`). -/
@[fun_prop] theorem continuous_rTensorCompletion [CompleteSpace E] [CompleteSpace F] (G : Type*)
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] :
    Continuous fun A : ContinuousLinearMapUltraweak 𝕜 E F ↦
      ofCLM (A.toCLM.rTensorCompletion G) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 (Completion G)
  let uE := (completionRightIsometry 𝕜 E G).trans (b.tensorCompletionEquiv E)
  let uF := (completionRightIsometry 𝕜 F G).trans (b.tensorCompletionEquiv F)
  refine ((continuous_linearIsometryEquiv_postcomp uF.symm).comp
    ((continuous_precomp uE.toLinearIsometry.toContinuousLinearMap).comp
      (continuous_ampliation w))).congr fun A ↦ congrArg ofCLM ?_
  refine completion_ext fun x z ↦ uF.injective ?_
  simpa [uE, uF] using
    (congr($(b.tensorCompletionEquiv_comp_rTensorCompletion A.toCLM)
      ((x ⊗ₜ[𝕜] (z : Completion G) : E ⊗[𝕜] Completion G) : Completion (E ⊗[𝕜] Completion G)))).symm
/-- Right-factor amplification `A ↦ 1 ⊗ A` (`ContinuousLinearMap.lTensorCompletion E`) between
complete spaces `F` and `G` is ultraweakly continuous for any inner product space `E` (without
separability, nontriviality, or completeness assumptions on `E`). -/
@[fun_prop] theorem continuous_lTensorCompletion (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace F] [CompleteSpace G] :
    Continuous fun A : ContinuousLinearMapUltraweak 𝕜 F G ↦
      ofCLM (A.toCLM.lTensorCompletion E) := by
  let cEF := (commIsometry 𝕜 E F).completion
  let cGE := (commIsometry 𝕜 G E).completion
  refine ((continuous_linearIsometryEquiv_postcomp cGE).comp
    ((continuous_precomp cEF.toLinearIsometry.toContinuousLinearMap).comp
      (continuous_rTensorCompletion E))).congr fun _ ↦
    congrArg ofCLM <| completion_ext fun _ _ ↦ by simp [cEF, cGE]
/-- Every right slice map `T ↦ sliceRight ξ η T` (with `E₂` complete) is ultraweakly continuous. -/
@[fun_prop] theorem continuous_sliceRight [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    Continuous fun A : ContinuousLinearMapUltraweak 𝕜 (Completion (E₁ ⊗[𝕜] F₁))
        (Completion (E₂ ⊗[𝕜] F₂)) ↦ ofCLM (sliceRight ξ η A.toCLM) :=
  ((continuous_postcomp ((tmulCLM 𝕜 E₂ F₂).flip η).adjoint).comp
    (continuous_precomp ((tmulCLM 𝕜 E₁ F₁).flip ξ))).congr fun _ ↦
      congrArg ofCLM (sliceRight_apply _ _ _).symm
/-- Every left slice map `T ↦ sliceLeft e₁ e₂ T` (with `F₂` complete) is ultraweakly continuous. -/
@[fun_prop] theorem continuous_sliceLeft [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    Continuous fun A : ContinuousLinearMapUltraweak 𝕜 (Completion (E₁ ⊗[𝕜] F₁))
        (Completion (E₂ ⊗[𝕜] F₂)) ↦ ofCLM (sliceLeft e₁ e₂ A.toCLM) :=
  ((continuous_postcomp (tmulCLM 𝕜 E₂ F₂ e₂).adjoint).comp
    (continuous_precomp (tmulCLM 𝕜 E₁ F₁ e₁))).congr fun _ ↦
      congrArg ofCLM (sliceLeft_apply _ _ _).symm
end TauCeti.ContinuousLinearMapUltraweak
