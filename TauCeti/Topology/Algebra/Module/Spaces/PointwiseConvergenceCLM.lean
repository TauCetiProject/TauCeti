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
computed pointwise (`PointwiseConvergenceCLM.continuousSMul`). Post-composition evaluates as
`postcomp E L f x = L (f x)` (`PointwiseConvergenceCLM.postcomp_apply_apply`). For seminormed
codomains, closure in the topology of pointwise convergence is characterized by simultaneous norm
approximation on finite sets of vectors (`PointwiseConvergenceCLM.mem_closure_iff`,
`ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff_norm`). The canonical map
`ContinuousLinearMap.toPointwiseConvergenceCLM` is bijective, with inverse
`PointwiseConvergenceCLM.toCLM` (`ContinuousLinearMap.toPointwiseConvergenceCLM_injective`,
`ContinuousLinearMap.toPointwiseConvergenceCLM_surjective`).
A map lies in the closure of a set of maps in this topology exactly when it is the pointwise limit
along some filter of maps eventually in the set
(`ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff`); since this topology need
not be first countable, nets or filters cannot in general be replaced by sequences here.
-/

public section

open Filter Topology

namespace PointwiseConvergenceCLM

/-- Evaluating `PointwiseConvergenceCLM.postcomp` on a map and a vector applies the outer map to
the value. -/
theorem postcomp_apply_apply {𝕜₁ 𝕜₂ 𝕜₃ E F G : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂} {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ]
    [AddCommGroup E] [TopologicalSpace E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [Module 𝕜₁ E] [Module 𝕜₂ F] [Module 𝕜₃ G] [ContinuousConstSMul 𝕜₂ F]
    [ContinuousConstSMul 𝕜₃ G] (L : F →SL[τ] G) (f : E →SLₚₜ[σ] F) (x : E) :
    postcomp E L f x = L (f x) :=
  DFunLike.congr_fun (postcomp_apply E L f) x

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

/-- Passing to the topology of pointwise convergence is surjective. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_surjective {𝕜₁ 𝕜₂ E F : Type*}
    [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E] [TopologicalSpace E]
    [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F] :
    Function.Surjective (ContinuousLinearMap.toPointwiseConvergenceCLM 𝕜₂ σ E F) :=
  fun T ↦ ⟨PointwiseConvergenceCLM.toCLM T,
    PointwiseConvergenceCLM.toPointwiseConvergenceCLM_toCLM T⟩

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

/-- An operator `T` lies in the pointwise-convergence (strong operator) closure of `s` if and only
if for every finite set of vectors `F₀` and every `ε > 0`, some `a ∈ s` satisfies
`‖T v - a v‖ < ε` for all `v ∈ F₀`. -/
theorem ContinuousLinearMap.toPointwiseConvergenceCLM_mem_closure_image_iff_norm
    {𝕜₁ 𝕜₂ E F : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜₁ E] [ContinuousSMul 𝕜₁ E] [SeminormedAddCommGroup F]
    [Module 𝕜₂ F] [ContinuousConstSMul 𝕜₂ F] {s : Set (E →SL[σ] F)} {T : E →SL[σ] F} :
    toPointwiseConvergenceCLM 𝕜₂ σ E F T ∈ closure (toPointwiseConvergenceCLM 𝕜₂ σ E F '' s) ↔
      ∀ (F₀ : Finset E) {ε : ℝ}, 0 < ε → ∃ a ∈ s, ∀ v ∈ F₀, ‖T v - a v‖ < ε := by
  rw [PointwiseConvergenceCLM.mem_closure_iff]
  simp only [Set.exists_mem_image, toPointwiseConvergenceCLM_apply]
  -- `UniformConvergenceCLM.instFunLike` is definitionally `ContinuousLinearMap.funLike`.
  exact Iff.rfl
