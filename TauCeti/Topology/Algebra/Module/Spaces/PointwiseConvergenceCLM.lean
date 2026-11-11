/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Basic facts on the topology of pointwise convergence

Scalar multiplication on `E →SLₚₜ[σ] F` is jointly continuous whenever it is on `F`, since it is
computed pointwise (`PointwiseConvergenceCLM.continuousSMul`). Passing from `E →SL[σ] F` to its
pointwise-convergence copy is injective
(`ContinuousLinearMap.toPointwiseConvergenceCLM_injective`).
-/

public section

namespace PointwiseConvergenceCLM

variable {𝕜₁ 𝕜₂ M E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [Monoid M] [TopologicalSpace M]
    [DistribMulAction M F] [SMulCommClass 𝕜₂ M F] [ContinuousSMul M F]

/-- Scalar multiplication is jointly continuous for the topology of pointwise convergence, since
it is computed pointwise. -/
instance continuousSMul : ContinuousSMul M (E →SLₚₜ[σ] F) where
  continuous_smul := continuous_of_continuous_eval fun x ↦
    continuous_fst.smul (((continuous_apply x).comp
      (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).continuous).comp continuous_snd :
        Continuous fun p : M × (E →SLₚₜ[σ] F) ↦ p.2 x)

end PointwiseConvergenceCLM

/-- Passing to the topology of pointwise convergence does not identify distinct maps. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_injective {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F] :
    Function.Injective (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F) :=
  fun _ _ h ↦ ContinuousLinearMap.ext fun v ↦ congrArg (fun T : E →SLₚₜ[σ] F ↦ T v) h
