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
public import Mathlib.NumberTheory.Padics.Measure.Topology

/-!
# The projective-limit topology on locally analytic distributions

Distributions on `ℤ_p` carry the initial uniformity for restriction to the Banach duals of
all analytic stages. This is the topology of the stage seminorms, not a single Banach norm
and not the topology of pointwise convergence on test functions.

The compatible families form a closed submodule of the product of the stage duals.
Consequently the distribution space is complete and metrizable. The continuity and convergence
criteria below allow maps and limits to be checked one stage at a time. Measures with the
operator-norm topology `AbstractMeasure.StrongTopology` map continuously to distributions.

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
  UniformSpace.comap (LinearMap.pi (stage (p := p) (K := K))) inferInstance

/-- Restriction to all stages induces the projective-limit uniformity. -/
theorem isUniformInducing_pi_stage :
    IsUniformInducing (LinearMap.pi (stage (p := p) (K := K))) := ⟨rfl⟩

/-- Stage restriction is a uniform embedding into the product of the Banach duals. -/
theorem isUniformEmbedding_pi_stage :
    IsUniformEmbedding (LinearMap.pi (stage (p := p) (K := K))) :=
  ⟨isUniformInducing_pi_stage, fun _ _ h ↦ ext fun k ↦ congrFun h k⟩

instance : IsUniformAddGroup (LocallyAnalyticDistribution p K) :=
  isUniformInducing_pi_stage.isUniformAddGroup (LinearMap.pi stage).toAddMonoidHom

-- Instance search does not recover the additive group from the addition on the subtype.
instance : ContinuousAdd (LocallyAnalyticDistribution p K) :=
  (inferInstance : IsTopologicalAddGroup (LocallyAnalyticDistribution p K)).toContinuousAdd

instance : ContinuousSMul K (LocallyAnalyticDistribution p K) :=
  isUniformInducing_pi_stage.isInducing.continuousSMul continuous_id
    (map_smul (LinearMap.pi stage) _ _)

instance : T2Space (LocallyAnalyticDistribution p K) :=
  isUniformEmbedding_pi_stage.isEmbedding.t2Space

instance : (uniformity (LocallyAnalyticDistribution p K)).IsCountablyGenerated := by
  have (h : ℕ) : (uniformity (AnalyticStage p h K →L[K] K)).IsCountablyGenerated :=
    @EMetric.instIsCountablyGeneratedUniformity (AnalyticStage p h K →L[K] K) inferInstance
  exact Filter.comap.isCountablyGenerated _ _

/-- The restriction image is exactly the compatible families. -/
theorem range_pi_stage :
    Set.range (LinearMap.pi (stage (p := p) (K := K))) =
      compatibleStageFunctionals p K := by
  ext f
  constructor
  · rintro ⟨μ, rfl⟩
    exact mem_compatibleStageFunctionals_iff.mpr (stage_comp_transition μ)
  · intro hf
    exact ⟨stagesEquiv.symm ⟨f, hf⟩, funext fun h ↦ stage_stagesEquiv_symm _ h⟩

instance : CompleteSpace (LocallyAnalyticDistribution p K) := by
  apply isUniformInducing_pi_stage.completeSpace
  rw [range_pi_stage]
  exact isClosed_compatibleStageFunctionals.isComplete

/-- A map into distributions is continuous exactly when all its stage restrictions are. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X]
    {f : X → LocallyAnalyticDistribution p K} :
    Continuous f ↔ ∀ h, Continuous fun x ↦ stage h (f x) := by
  rw [isUniformInducing_pi_stage.isInducing.continuous_iff, continuous_pi_iff]
  rfl

/-- A map into distributions is uniformly continuous exactly when all its stage restrictions are. -/
theorem uniformContinuous_iff {X : Type*} [UniformSpace X]
    {f : X → LocallyAnalyticDistribution p K} :
    UniformContinuous f ↔ ∀ h, UniformContinuous fun x ↦ stage h (f x) := by
  rw [isUniformInducing_pi_stage.uniformContinuous_iff, uniformContinuous_pi]
  rfl

/-- Convergence of distributions is operator-norm convergence on each analytic stage. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι} {f : ι → LocallyAnalyticDistribution p K}
    {μ : LocallyAnalyticDistribution p K} :
    Tendsto f l (𝓝 μ) ↔ ∀ h, Tendsto (fun i ↦ stage h (f i)) l (𝓝 (stage h μ)) := by
  rw [isUniformInducing_pi_stage.isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- Each stage restriction is uniformly continuous for the projective-limit uniformity. -/
theorem uniformContinuous_stage (h : ℕ) :
    UniformContinuous (stage (p := p) (K := K) h) :=
  uniformContinuous_iff.mp uniformContinuous_id h

/-- Each stage restriction is continuous for the projective-limit topology. -/
@[continuity, fun_prop]
theorem continuous_stage (h : ℕ) :
    Continuous (stage (p := p) (K := K) h) :=
  (uniformContinuous_stage h).continuous

/-- The map taking a distribution to its compatible family of stage restrictions is continuous. -/
@[continuity, fun_prop]
theorem continuous_stagesEquiv : Continuous (stagesEquiv (p := p) (K := K)) := by
  refine continuous_induced_rng.mpr (continuous_pi fun h ↦ ?_)
  simpa only [Function.comp_apply, stagesEquiv_apply] using
    continuous_stage (p := p) (K := K) h

/-- Reconstructing a distribution from its compatible family of stage restrictions is continuous. -/
@[continuity, fun_prop]
theorem continuous_stagesEquiv_symm : Continuous (stagesEquiv (p := p) (K := K)).symm := by
  refine continuous_iff.mpr fun h ↦ ?_
  simp_rw [stage_stagesEquiv_symm]
  exact (_root_.continuous_apply h).comp continuous_subtypeVal

/-- Evaluation at a fixed locally analytic test function is continuous in the distribution. -/
@[continuity, fun_prop]
theorem continuous_apply (f : LocallyAnalytic p K K) :
    Continuous fun μ : LocallyAnalyticDistribution p K ↦
      (μ : Module.Dual K (LocallyAnalytic p K K)) f := by
  induction f using Module.DirectLimit.induction_on with
  | ih h c =>
    rw [← LocallyAnalytic.ofStage_def]
    simpa only [stage_apply] using (continuous_stage h).clm_apply (continuous_const (y := c))

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
    isUniformInducing_pi_stage.isInducing.nhds_eq_comap, nhds_pi, Filter.pi,
    Filter.comap_iInf]
  apply iInf_congr
  intro h
  rw [Filter.comap_comap, map_zero, Pi.zero_apply,
    ← @comap_norm_nhds_zero (AnalyticStage p h K →L[K] K) inferInstance,
    Filter.comap_comap]
  congr 1
  funext μ
  exact (stageSeminorm_apply h μ).symm

/-- The inclusion of measures with the operator-norm topology into distributions is continuous. -/
theorem continuous_ofMeasure_strong :
    @Continuous _ _ (AbstractMeasure.StrongTopology (X := ℤ_[p]) (R := K) (E := K)) _
      (ofMeasure (p := p) (K := K)) := by
  let := AbstractMeasure.StrongTopology (X := ℤ_[p]) (R := K) (E := K)
  have hc : Continuous (AbstractMeasure.toCLMEquiv (X := ℤ_[p]) (R := K) (E := K)) :=
    continuous_id.congr fun μ ↦
      ContinuousLinearMap.ext fun f ↦ (AbstractMeasure.coe_toCLMEquiv μ f).symm
  refine continuous_iff.mpr fun h ↦ ?_
  simp_rw [stage_ofMeasure]
  exact hc.clm_comp continuous_const

end TauCeti.LocallyAnalyticDistribution
