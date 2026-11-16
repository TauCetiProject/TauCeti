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
computed pointwise (`PointwiseConvergenceCLM.continuousSMul`). The canonical map
`ContinuousLinearMap.toPointwiseConvergenceCLM` is bijective, with inverse
`PointwiseConvergenceCLM.toCLM` (`ContinuousLinearMap.toPointwiseConvergenceCLM_injective`,
`ContinuousLinearMap.toPointwiseConvergenceCLM_surjective`).
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

section ToCLM

variable {𝕜₁ 𝕜₂ E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E]
    [AddCommGroup F] [TopologicalSpace F] [Module 𝕜₂ F]

/-- The continuous linear map underlying an element of `E →SLₚₜ[σ] F`. -/
def toCLM (T : E →SLₚₜ[σ] F) : E →SL[σ] F :=
  (UniformConvergenceCLM.ofFun σ F {s : Set E | Finite s}).symm T

/-- Evaluating the underlying continuous linear map agrees with evaluating in the pointwise
convergence copy. -/
@[simp]
theorem toCLM_apply (T : E →SLₚₜ[σ] F) (x : E) : toCLM T x = T x :=
  (rfl)

/-- Forgetting the pointwise convergence topology is injective. -/
theorem toCLM_injective : Function.Injective (toCLM (σ := σ) (E := E) (F := F)) :=
  (UniformConvergenceCLM.ofFun σ F {s : Set E | Finite s}).symm.injective

/-- Every continuous linear map underlies an element of the pointwise convergence copy. -/
theorem toCLM_surjective : Function.Surjective (toCLM (σ := σ) (E := E) (F := F)) :=
  (UniformConvergenceCLM.ofFun σ F {s : Set E | Finite s}).symm.surjective

variable [ContinuousSMul 𝕜₁ E] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]

/-- Passing to the pointwise convergence copy and forgetting it recovers the original map. -/
theorem toCLM_toPointwiseConvergenceCLM (T : E →SL[σ] F) :
    toCLM (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F T) = T :=
  (rfl)

/-- Forgetting the pointwise convergence topology and re-applying `toPointwiseConvergenceCLM` is
the identity. -/
theorem toPointwiseConvergenceCLM_toCLM (T : E →SLₚₜ[σ] F) :
    ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F (toCLM T) = T :=
  (rfl)

end ToCLM

end PointwiseConvergenceCLM

/-- Evaluating `toPointwiseConvergenceCLM` at a vector agrees with evaluating the original map. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_apply_apply {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F]
    (T : E →SL[σ] F) (x : E) :
    (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F T) x = T x :=
  (rfl)

/-- Passing to the topology of pointwise convergence does not identify distinct maps. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_injective {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F] :
    Function.Injective (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F) :=
  fun _ _ h ↦ ContinuousLinearMap.ext fun v ↦ congrArg (fun T : E →SLₚₜ[σ] F ↦ T v) h

/-- Passing to the topology of pointwise convergence is surjective. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_surjective {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F] :
    Function.Surjective (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F) :=
  fun T ↦ ⟨PointwiseConvergenceCLM.toCLM T,
    PointwiseConvergenceCLM.toPointwiseConvergenceCLM_toCLM T⟩
