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
computed pointwise (`PointwiseConvergenceCLM.continuousSMul`). For seminormed codomains, closure in
the topology of pointwise convergence is characterized by simultaneous norm approximation on finite
sets of vectors (`PointwiseConvergenceCLM.mem_closure_iff`,
`ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff`). Passing from `E →SL[σ] F`
to its pointwise-convergence copy is injective
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

/-- An operator `T : E →SLₚₜ[σ] F` lies in the closure of `s` for the topology of pointwise
convergence if and only if for every finite set of vectors `F₀` and every `ε > 0`, some `a ∈ s`
satisfies `‖T v - a v‖ < ε` for all `v ∈ F₀`. -/
theorem mem_closure_iff {𝕜₁ 𝕜₂ E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂}
    [AddCommGroup E] [TopologicalSpace E] [Module 𝕜₁ E] [SeminormedAddCommGroup F] [Module 𝕜₂ F]
    {s : Set (E →SLₚₜ[σ] F)} {T : E →SLₚₜ[σ] F} :
    T ∈ closure s ↔ ∀ (F₀ : Finset E) {ε : ℝ}, 0 < ε → ∃ a ∈ s, ∀ v ∈ F₀, ‖T v - a v‖ < ε := by
  rw [mem_closure_iff_nhds_basis
    ((PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis
      (σ := σ) (E := E) Metric.nhds_basis_ball).nhds_of_zero T)]
  constructor
  · intro h F₀ ε hε
    obtain ⟨a, ha, hball⟩ := h ⟨(F₀ : Set E), ε⟩ ⟨F₀.finite_toSet, hε⟩
    refine ⟨a, ha, fun v hv => ?_⟩
    simpa only [Metric.mem_ball, dist_zero_right, _root_.sub_apply, norm_sub_rev] using hball v hv
  · rintro h ⟨F₀, ε⟩ ⟨hF₀, hε⟩
    classical
    have hF : F₀.Finite := hF₀
    obtain ⟨a, ha, happrox⟩ := h hF.toFinset hε
    refine ⟨a, ha, fun v hv => ?_⟩
    simpa only [Metric.mem_ball, dist_zero_right, _root_.sub_apply, norm_sub_rev] using
      happrox v (hF.mem_toFinset.2 hv)

end PointwiseConvergenceCLM

/-- Passing to the topology of pointwise convergence does not identify distinct maps. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_injective {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F] :
    Function.Injective (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F) :=
  fun _ _ h ↦ ContinuousLinearMap.ext fun v ↦ congrArg (fun T : E →SLₚₜ[σ] F ↦ T v) h

/-- An operator `T` lies in the pointwise-convergence (strong operator) closure of `s` if and only
if for every finite set of vectors `F₀` and every `ε > 0`, some `a ∈ s` satisfies
`‖T v - a v‖ < ε` for all `v ∈ F₀`. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [SeminormedAddCommGroup F] [Module 𝕜₂ F]
    [ContinuousConstSMul 𝕜₂ F] {s : Set (E →SL[σ] F)} {T : E →SL[σ] F} :
    toPointwiseConvergenceCLM 𝕜₂ σ E F T ∈ closure (toPointwiseConvergenceCLM 𝕜₂ σ E F '' s) ↔
      ∀ (F₀ : Finset E) {ε : ℝ}, 0 < ε → ∃ a ∈ s, ∀ v ∈ F₀, ‖T v - a v‖ < ε := by
  rw [PointwiseConvergenceCLM.mem_closure_iff]
  simp only [Set.exists_mem_image, toPointwiseConvergenceCLM_apply]
  -- `UniformConvergenceCLM.instFunLike` is definitionally `ContinuousLinearMap.funLike`.
  exact Iff.rfl
