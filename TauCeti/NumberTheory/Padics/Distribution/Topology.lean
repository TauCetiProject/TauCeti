/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Dual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# The projective-limit topology on locally analytic distributions

Distributions on `ℤ_p` carry the initial uniformity for restriction to the Banach duals of
all analytic stages. This is the topology of the stage seminorms, not a single Banach norm
and not the topology of pointwise convergence on test functions.

The compatible families form a closed submodule of the product of the stage duals.
Consequently the distribution space is complete and metrizable. The continuity and convergence
criteria below allow maps and limits to be checked one stage at a time. Measures map
continuously to distributions for this topology.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
* P. Schneider and J. Teitelbaum, *Locally analytic distributions and p-adic representation
  theory, with applications to GL₂*, §1.
-/

public section

open Filter Topology TopologicalSpace

namespace TauCeti.LocallyAnalyticDistribution

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K]
  [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- Compatible stage functionals form a closed submodule of the product of the Banach duals. -/
theorem isClosed_compatibleStageFunctionals :
    IsClosed (compatibleStageFunctionals p K : Set (∀ h : ℕ, AnalyticStage p h K →L[K] K)) := by
  have heq : (compatibleStageFunctionals p K : Set (∀ h : ℕ, AnalyticStage p h K →L[K] K)) =
      ⋂ h, {μ | μ (h + 1) ∘L AnalyticStage.transition K = μ h} := by
    ext μ
    simp
  rw [heq]
  refine isClosed_iInter fun h ↦ isClosed_eq ?_ (continuous_apply h)
  exact (continuous_apply (h + 1)).clm_comp continuous_const

/-- The projective-limit uniformity, pulled back from the compatible Banach-stage duals. -/
noncomputable instance uniformSpace : UniformSpace (LocallyAnalyticDistribution p K) :=
  UniformSpace.comap (fun μ : LocallyAnalyticDistribution p K ↦ fun h ↦ stage h μ) inferInstance

/-- Restriction to all stages induces the projective-limit uniformity. -/
theorem isUniformInducing_stageFamily :
    IsUniformInducing (fun μ : LocallyAnalyticDistribution p K ↦ fun h ↦ stage h μ) := ⟨rfl⟩

/-- Stage restriction is a uniform embedding into the product of the Banach duals. -/
theorem isUniformEmbedding_stageFamily :
    IsUniformEmbedding (fun μ : LocallyAnalyticDistribution p K ↦ fun h ↦ stage h μ) :=
  ⟨isUniformInducing_stageFamily, fun _ _ h ↦ ext fun k ↦ congrFun h k⟩

instance : IsUniformAddGroup (LocallyAnalyticDistribution p K) :=
  isUniformInducing_stageFamily.isUniformAddGroup (LinearMap.pi fun h ↦ stage h).toAddMonoidHom

instance : ContinuousSMul K (LocallyAnalyticDistribution p K) :=
  isUniformInducing_stageFamily.isInducing.continuousSMul continuous_id
    (map_smul (LinearMap.pi fun h ↦ stage h) _ _)

instance : T2Space (LocallyAnalyticDistribution p K) :=
  isUniformEmbedding_stageFamily.isEmbedding.t2Space

instance : MetrizableSpace (LocallyAnalyticDistribution p K) := by
  have (h : ℕ) : IsCompletelyMetrizableSpace (AnalyticStage p h K →L[K] K) :=
    @MetricSpace.toIsCompletelyMetrizableSpace (AnalyticStage p h K →L[K] K)
      inferInstance inferInstance
  exact isUniformEmbedding_stageFamily.isEmbedding.metrizableSpace

/-- The restriction image is exactly the compatible families. -/
theorem range_stageFamily :
    Set.range (fun μ : LocallyAnalyticDistribution p K ↦ fun h ↦ stage h μ) =
      compatibleStageFunctionals p K := by
  ext f
  constructor
  · rintro ⟨μ, rfl⟩
    exact mem_compatibleStageFunctionals_iff.mpr (stage_comp_transition μ)
  · intro hf
    exact ⟨stagesEquiv.symm ⟨f, hf⟩, funext fun h ↦ stage_stagesEquiv_symm _ h⟩

instance : CompleteSpace (LocallyAnalyticDistribution p K) := by
  apply isUniformInducing_stageFamily.completeSpace
  rw [range_stageFamily]
  exact isClosed_compatibleStageFunctionals.isComplete

/-- A map into distributions is continuous exactly when all its stage restrictions are. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    {f : X → LocallyAnalyticDistribution p K} :
    Continuous f ↔ ∀ h, Continuous fun x ↦ stage h (f x) := by
  rw [isUniformInducing_stageFamily.isInducing.continuous_iff, continuous_pi_iff]
  rfl

instance : ContinuousAdd (LocallyAnalyticDistribution p K) where
  continuous_add := continuous_iff.mpr fun h ↦ by
    exact ((((continuous_iff (p := p) (K := K)).mp continuous_id h).comp continuous_fst).add
      (((continuous_iff (p := p) (K := K)).mp continuous_id h).comp continuous_snd)).congr
        fun x ↦ ((stage h).map_add x.1 x.2).symm

/-- Convergence of distributions is operator-norm convergence on each analytic stage. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι} {f : ι → LocallyAnalyticDistribution p K}
    {μ : LocallyAnalyticDistribution p K} :
    Tendsto f l (𝓝 μ) ↔ ∀ h, Tendsto (fun i ↦ stage h (f i)) l (𝓝 (stage h μ)) := by
  rw [isUniformInducing_stageFamily.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- Each stage restriction is continuous for the projective-limit topology. -/
@[continuity]
theorem continuous_stage (h : ℕ) :
    Continuous (stage (p := p) (K := K) h) :=
  continuous_iff.mp continuous_id h

/-- Convergence can equivalently be tested by the stage seminorms of the differences. -/
theorem tendsto_iff_stageSeminorm_sub {ι : Type*} {l : Filter ι}
    {f : ι → LocallyAnalyticDistribution p K} {μ : LocallyAnalyticDistribution p K} :
    Tendsto f l (𝓝 μ) ↔ ∀ h, Tendsto (fun i ↦ stageSeminorm h (f i - μ)) l (𝓝 0) := by
  rw [tendsto_iff]
  simp_rw [stageSeminorm_apply]
  refine forall_congr' fun h ↦ ?_
  rw [tendsto_iff_norm_sub_tendsto_zero (f := fun i ↦ stage h (f i)) (a := l) (b := stage h μ)]
  simp only [map_sub (stage (p := p) (K := K) h)]

/-- The projective-limit topology is precisely the topology generated by the stage seminorms. -/
theorem withSeminorms_stageSeminorm :
    WithSeminorms (stageSeminorm (p := p) (K := K)) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf,
    isUniformInducing_stageFamily.isInducing.nhds_eq_comap, nhds_pi, Filter.pi,
    Filter.comap_iInf]
  apply iInf_congr
  intro h
  rw [Filter.comap_comap, map_zero,
    ← @comap_norm_nhds_zero (AnalyticStage p h K →L[K] K) inferInstance,
    Filter.comap_comap]
  congr 1
  funext μ
  exact (stageSeminorm_apply h μ).symm

/-- Integration of locally analytic functions sends norm-convergent measures to convergent
distributions. -/
@[continuity]
theorem continuous_ofMeasure_comp_toCLMEquiv_symm :
    Continuous (ofMeasure (p := p) (K := K) ∘ AbstractMeasure.toCLMEquiv.symm) := by
  refine continuous_iff.mpr fun h ↦ ?_
  simp_rw [Function.comp_apply, stage_ofMeasure, LinearEquiv.apply_symm_apply]
  exact continuous_id.clm_comp continuous_const

end TauCeti.LocallyAnalyticDistribution
