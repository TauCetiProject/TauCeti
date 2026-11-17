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
(`ContinuousLinearMap.toPointwiseConvergenceCLM_injective`). A map lies in the closure of a set
of maps in this topology exactly when it is the pointwise limit along some filter of maps
eventually in the set (`ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff`);
since the strong operator topology is not first countable, nets or filters cannot be replaced by
sequences here.
-/

public section

open Filter Topology

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

/-- A map lies in the closure of a set `s` of maps for the topology of pointwise convergence
exactly when it is the pointwise limit, along some nontrivial filter, of maps eventually in `s`. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F] {s : Set (E →SL[σ] F)}
    {T : E →SL[σ] F} :
    toPointwiseConvergenceCLM 𝕜₂ σ E F T ∈ closure (toPointwiseConvergenceCLM 𝕜₂ σ E F '' s) ↔
      ∃ l : Filter (E →SL[σ] F), l.NeBot ∧ (∀ᶠ A in l, A ∈ s) ∧
        ∀ x, Tendsto (fun A => A x) l (𝓝 (T x)) := by
  set q := toPointwiseConvergenceCLM 𝕜₂ σ E F
  constructor
  · intro h
    -- Pull the neighbourhood filter within `q '' s` back along the bijection `q`.
    refine ⟨comap q (𝓝[q '' s] (q T)),
      (mem_closure_iff_nhdsWithin_neBot.mp h).comap_of_surj fun p => ⟨p, rfl⟩,
      mem_comap.mpr ⟨_, self_mem_nhdsWithin, ?_⟩, fun x => ?_⟩
    · rintro A ⟨B, hB, hBA⟩
      exact toPointwiseConvergenceCLM_injective hBA ▸ hB
    · exact PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mp
        (tendsto_comap.mono_right nhdsWithin_le_nhds) x
  · rintro ⟨l, hl, hs, hT⟩
    exact mem_closure_of_tendsto (PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr hT)
      (hs.mono fun A hA => ⟨A, hA, rfl⟩)
