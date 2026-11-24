/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Statistics.Decision.Criteria
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Analysis.Convex.StdSimplex
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.MeasureTheory.Function.Lp.AeMem
import TauCeti.MeasureTheory.Function.LpSeminorm.RadonNikodym
import TauCeti.Probability.Distributions.Categorical.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Sion

/-!
# Finite statistical games

For finitely many actions and parameters, the risk vectors of the randomized rules form a
compact convex set, even for an arbitrary measurable observation space. To see compactness,
represent the rules by simplex-valued functions in `L²` of the sum of the sampling laws.
The feasible set is weakly compact. Integrating against the loss and the Radon–Nikodym
densities is a weakly continuous linear map to the space of risk vectors.

Sion's theorem applied to the risk set and the prior simplex gives a saddle point. Its rule
minimizes average risk under the saddle-point prior and has worst-case risk equal to that
average.

## References

* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press
  (1967), Lemma 1.7.1 and Theorem 2.9.1.
* J. O. Berger, *Statistical Decision Theory and Bayesian Analysis*, 2nd ed., Springer
  (1985), Theorem 15 and Lemmas 9–10.
-/

public section

open Convexity Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti

variable {Θ X A : Type*} [MeasurableSpace X]

section Representation

variable [Fintype A]

private noncomputable abbrev ActionL2 (A : Type*) [Fintype A] (μ : Measure X) :=
  Lp (EuclideanSpace ℝ A) 2 μ

private noncomputable def feasibleActions (A : Type*) [Fintype A] (μ : Measure X) :
    Set (ActionL2 A μ) :=
  {f | ∀ᵐ x ∂μ, WithLp.ofLp (f x) ∈ range (fun t : StdSimplex ℝ A ↦ (t.weights : A → ℝ))}

private theorem isClosed_feasibleActions (μ : Measure X) : IsClosed (feasibleActions A μ) :=
  Lp.isClosed_setOf_ae_mem <| (StdSimplex.isClosedEmbedding_toFun_comp_weights ℝ A).isClosed_range
    |>.preimage (PiLp.continuous_ofLp 2 _)

private theorem convex_feasibleActions (μ : Measure X) : Convex ℝ (feasibleActions A μ) :=
  Lp.convex_setOf_ae_mem <| (StdSimplex.convex_range_toFun_comp_weights ℝ _).linear_preimage
    (WithLp.linearEquiv 2 ℝ (A → ℝ)).toLinearMap

private theorem isBounded_feasibleActions (μ : Measure X) [IsFiniteMeasure μ] :
    Bornology.IsBounded (feasibleActions A μ) := by
  refine Metric.isBounded_closedBall.subset (s := feasibleActions A μ)
    (t := Metric.closedBall 0 ((measureUnivNNReal μ : ℝ) ^ (2 : ℝ)⁻¹)) ?_
  intro f hf
  rw [mem_closedBall_zero_iff]
  have hpoint : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1 := by
    filter_upwards [hf] with x hx
    obtain ⟨t, ht⟩ := hx
    simpa [ht] using t.norm_toLp_weights_le_one (p := 2)
  simpa using Lp.norm_le_of_ae_bound zero_le_one hpoint

variable [MeasurableSpace A] [MeasurableSingletonClass A]

private theorem exists_kernel_of_mem_feasibleActions [Nonempty A] {μ : Measure X}
    {f : ActionL2 A μ} (hf : f ∈ feasibleActions A μ) :
    ∃ κ : Kernel X A, IsMarkovKernel κ ∧
      ∀ᵐ x ∂μ, ∀ a, (κ x).real {a} = f x a := by
  let hm := Lp.aestronglyMeasurable f
  let g := hm.mk f
  let v : StdSimplex ℝ≥0 A := StdSimplex.single (Classical.arbitrary A)
  let w (x : X) := v.extendWeights fun a ↦ (g x a).toNNReal
  have hg (a : A) : Measurable fun x ↦ (g x a).toNNReal :=
    ((PiLp.continuous_apply 2 _ a).measurable.comp
      hm.stronglyMeasurable_mk.measurable).real_toNNReal
  let κ : Kernel X A := ⟨fun x ↦ Probability.categoricalMeasure (w x),
    Probability.measurable_categoricalMeasure.comp
      ((StdSimplex.measurable_extendWeights v).comp (Measurable.of_eval hg))⟩
  refine ⟨κ, ⟨fun x ↦ Probability.isProbabilityMeasure_categoricalMeasure (w x)⟩, ?_⟩
  filter_upwards [hf, hm.ae_eq_mk] with x hx hfg
  obtain ⟨t, ht⟩ := hx
  have heq : (fun a ↦ (g x a).toNNReal) = t.toNNReal.weights := by
    funext a
    apply NNReal.coe_injective
    rw [StdSimplex.coe_weights_toNNReal]
    have hta : t.weights a = g x a := (congrFun ht a).trans
      (congrArg (fun u : EuclideanSpace ℝ A ↦ u a) hfg)
    exact (Real.coe_toNNReal _ (hta ▸ t.weights_nonneg a)).trans hta.symm
  intro a
  have hta : t.weights a = f x a := congrFun ht a
  calc
    (κ x).real {a} = (w x).weights a := Probability.categoricalMeasure_real_singleton _ _
    _ = f x a := by
      simpa only [w, heq, StdSimplex.extendWeights_weights, StdSimplex.coe_weights_toNNReal]
        using hta

private theorem exists_mem_feasibleActions_of_kernel (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X A) [IsMarkovKernel κ] :
    ∃ f ∈ feasibleActions A μ, ∀ᵐ x ∂μ, ∀ a, (κ x).real {a} = f x a := by
  let w (x : X) : EuclideanSpace ℝ A := WithLp.toLp 2 ((κ x).real ∘ singleton)
  have hw : Measurable w :=
    (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval fun a ↦
      (κ.measurable_coe (measurableSet_singleton a)).ennreal_toReal)
  have hS (x : X) : WithLp.ofLp (w x) ∈ range (fun t : StdSimplex ℝ A ↦
      (t.weights : A → ℝ)) := by
    rw [StdSimplex.range_toFun_comp_weights, mem_inter_iff, mem_iInter]
    refine ⟨fun a ↦ measureReal_nonneg, ?_⟩
    simp [w]
  have hLp : MemLp w 2 μ := MemLp.of_bound hw.aestronglyMeasurable 1 <| ae_of_all _ fun x ↦ by
    obtain ⟨t, ht⟩ := hS x
    simpa [ht] using t.norm_toLp_weights_le_one (p := 2)
  refine ⟨hLp.toLp w, ?_, ?_⟩
  · filter_upwards [hLp.coeFn_toLp] with x hx
    simpa only [hx] using hS x
  · filter_upwards [hLp.coeFn_toLp] with x hx
    intro a
    simp [hx, w]

private noncomputable def riskLinearMap {μ : Measure X} [IsFiniteMeasure μ]
    {P : Θ → Measure X} (hP : ∀ θ, P θ ≤ μ) (L : Θ → A → ℝ) :
    ActionL2 A μ →L[ℝ] (Θ → ℝ) :=
  ContinuousLinearMap.pi fun θ ↦
    innerSL ℝ (((P θ).memLp_toReal_rnDeriv_smul_const (hP θ) 2 (WithLp.toLp 2 (L θ))).toLp _)

private theorem riskLinearMap_eq_risk {P : Θ → Measure X} [∀ θ, IsFiniteMeasure (P θ)]
    {μ : Measure X} [IsFiniteMeasure μ] (hP : ∀ θ, P θ ≤ μ) (L : Θ → A → ℝ)
    {κ : Kernel X A} [IsMarkovKernel κ] {f : ActionL2 A μ}
    (hf : ∀ᵐ x ∂μ, ∀ a, (κ x).real {a} = f x a) :
    riskLinearMap hP L f = risk P L κ := by
  funext θ
  rw [risk_eq_integral_integral Integrable.of_finite]
  simp_rw [integral_fintype (μ := κ _) (f := L θ) Integrable.of_finite]
  rw [← integral_toReal_rnDeriv_mul ((hP θ).absolutelyContinuous)]
  simp only [riskLinearMap, ContinuousLinearMap.pi_apply, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((P θ).memLp_toReal_rnDeriv_smul_const (hP θ) 2
    (WithLp.toLp 2 (L θ))).coeFn_toLp, hf] with x hfx hkx
  rw [hfx, inner_smul_left, EuclideanSpace.inner_eq_star_dotProduct, RCLike.conj_to_real]
  congr 1
  simp only [dotProduct, Pi.star_apply, star_trivial, hkx, smul_eq_mul]

end Representation

variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The set of attainable real risk vectors in a finite statistical game is compact and convex.
The sample space may be arbitrary, and finite sampling measures suffice. -/
theorem isCompact_convex_range_risk [Finite Θ] [Finite A] (P : Θ → Measure X)
    [∀ θ, IsFiniteMeasure (P θ)] (L : Θ → A → ℝ) :
    IsCompact (range (fun κ : {κ : Kernel X A // IsMarkovKernel κ} ↦ risk P L κ.val)) ∧
    Convex ℝ (range (fun κ : {κ : Kernel X A // IsMarkovKernel κ} ↦ risk P L κ.val)) := by
  classical
  let := Fintype.ofFinite Θ
  let := Fintype.ofFinite A
  rcases isEmpty_or_nonempty A with hA | hA
  · exact ⟨(Set.subsingleton_range _).isCompact, (Set.subsingleton_range _).convex⟩
  let μ := Measure.sum P
  have hP (θ : Θ) : P θ ≤ μ := Measure.le_sum _ θ
  let W := toWeakSpace ℝ (ActionL2 A μ)
  let T := riskLinearMap hP L
  have hrange : range (fun κ : {κ : Kernel X A // IsMarkovKernel κ} ↦ risk P L κ.val) =
      T '' feasibleActions A μ := by
    ext r
    constructor
    · rintro ⟨⟨κ, hκ⟩, rfl⟩
      obtain ⟨f, hf, hκf⟩ := exists_mem_feasibleActions_of_kernel μ κ
      exact ⟨f, hf, riskLinearMap_eq_risk hP L hκf⟩
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨κ, hκ, hk⟩ := exists_kernel_of_mem_feasibleActions hf
      exact ⟨⟨κ, hκ⟩, (riskLinearMap_eq_risk hP L hk).symm⟩
  have hconv := convex_feasibleActions (A := A) μ
  have hc : IsCompact (W '' feasibleActions A μ) :=
    isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded
      (surjective_inclusionInDoubleDual_of_uniformConvexSpace)
      (isClosed_feasibleActions μ) hconv (isBounded_feasibleActions μ)
  have hcont : Continuous (T ∘ W.symm) :=
    continuous_pi fun θ ↦ WeakBilin.eval_continuous _ ((ContinuousLinearMap.proj θ).comp T)
  rw [hrange]
  refine ⟨?_, hconv.linear_image T.toLinearMap⟩
  simpa only [image_image, comp_def, LinearEquiv.symm_apply_apply] using hc.image hcont

variable [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

/-- **Finite-game minimax theorem.** With finite sampling measures and finite nonempty parameter
and action sets, there is a saddle point consisting of a randomized Bayes rule and a probability
prior. The risk of the rule at every parameter is at most its average risk under that prior. -/
theorem exists_statistical_game_saddle_point [Finite Θ] [Finite A] [Nonempty Θ] [Nonempty A]
    (P : Θ → Measure X) [∀ θ, IsFiniteMeasure (P θ)] (L : Θ → A → ℝ) :
    ∃ δ : {κ : Kernel X A // IsMarkovKernel κ}, ∃ π : ProbabilityMeasure Θ,
      IsBayesRule (fun κ : {κ : Kernel X A // IsMarkovKernel κ} ↦ risk P L κ.val)
        (π : Measure Θ) δ ∧
      ∀ θ, risk P L δ.val θ ≤ ∫ t, risk P L δ.val t ∂(π : Measure Θ) := by
  classical
  let := Fintype.ofFinite Θ
  let C := range (fun κ : {κ : Kernel X A // IsMarkovKernel κ} ↦ risk P L κ.val)
  let S := range (fun t : StdSimplex ℝ Θ ↦ (t.weights : Θ → ℝ))
  let B (r w : Θ → ℝ) := ∑ θ, w θ * r θ
  have hC := isCompact_convex_range_risk P L
  have hS : IsCompact S :=
    isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ Θ).continuous
  have hnC : C.Nonempty := range_nonempty _
  have hnS : S.Nonempty := range_nonempty _
  have hbc w : Continuous fun r ↦ B r w := by fun_prop
  have hbw r : Continuous (B r) := by unfold B; fun_prop
  have hcv w : ConvexOn ℝ C (fun r ↦ B r w) := by
    refine ⟨hC.2, fun r _ s _ a b _ _ _ ↦ le_of_eq ?_⟩
    simp only [B, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  have hcc r : ConcaveOn ℝ S (B r) := by
    refine ⟨(StdSimplex.convex_range_toFun_comp_weights ℝ _), fun w _ v _ a b _ _ _ ↦ le_of_eq ?_⟩
    simp only [B, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun i _ ↦ by ring)
  obtain ⟨_, ⟨δ, rfl⟩, w, hw, hs⟩ := Sion.exists_isSaddlePointOn (f := B) hnC hC.2 hC.1
    (fun w _ ↦ (hbc w).lowerSemicontinuous.lowerSemicontinuousOn C)
    (fun w _ ↦ (hcv w).quasiconvexOn) (StdSimplex.convex_range_toFun_comp_weights ℝ _) hnS hS
    (fun r _ ↦ (hbw r).upperSemicontinuous.upperSemicontinuousOn S)
    (fun r _ ↦ (hcc r).quasiconcaveOn)
  obtain ⟨t, rfl⟩ := hw
  let π : ProbabilityMeasure Θ := (Probability.categoricalMeasure t.toNNReal).toProbabilityMeasure
  have havg (r : Θ → ℝ) : ∫ θ, r θ ∂(π : Measure Θ) = B r t.weights := by
    simp [π, B, Probability.integral_categoricalMeasure, smul_eq_mul]
  refine ⟨δ, π, ⟨Integrable.of_finite, fun δ' _ ↦ ?_⟩, fun θ ↦ ?_⟩
  · simpa only [havg] using hs _ (mem_range_self δ') t.weights (mem_range_self t)
  · let v := StdSimplex.single (R := ℝ) θ
    have h := hs _ (mem_range_self δ) v.weights (mem_range_self v)
    simpa [havg, B, v, StdSimplex.weights_single, Finsupp.single_apply] using h

/-- In a finite statistical game with finite sampling measures, the minimax and maximin values
of the real risk agree. -/
theorem iInf_iSup_risk_eq_iSup_iInf_integral_risk [Finite Θ] [Finite A] [Nonempty Θ] [Nonempty A]
    (P : Θ → Measure X) [∀ θ, IsFiniteMeasure (P θ)] (L : Θ → A → ℝ) :
    (⨅ δ : {κ : Kernel X A // IsMarkovKernel κ}, ⨆ θ, risk P L δ.val θ) =
      ⨆ π : ProbabilityMeasure Θ, ⨅ δ : {κ : Kernel X A // IsMarkovKernel κ},
        ∫ θ, risk P L δ.val θ ∂(π : Measure Θ) := by
  obtain ⟨δ, π, hbayes, hs⟩ := exists_statistical_game_saddle_point P L
  let D := {κ : Kernel X A // IsMarkovKernel κ}
  let R (d : D) := risk P L d.val
  let B (ν : ProbabilityMeasure Θ) (d : D) := ∫ θ, R d θ ∂(ν : Measure Θ)
  let M (d : D) := ⨆ θ, R d θ
  let : Nonempty D := ⟨δ⟩
  let : Nonempty (ProbabilityMeasure Θ) := ⟨π⟩
  have hle (ν : ProbabilityMeasure Θ) (d : D) : B ν d ≤ M d := by
    have hθ (θ : Θ) : R d θ ≤ M d := le_ciSup (Set.finite_range (R d)).bddAbove θ
    simpa using integral_mono (μ := (ν : Measure Θ)) Integrable.of_finite
      (integrable_const (M d)) hθ
  have hM : M δ = B π δ := le_antisymm (ciSup_le hs) (hle π δ)
  have hmin (d : D) : M δ ≤ M d :=
    hM.le.trans ((hbayes.integral_le d Integrable.of_finite).trans (hle π d))
  have hleft : (⨅ d, M d) = M δ :=
    le_antisymm (ciInf_le ⟨_, forall_mem_range.mpr hmin⟩ _) (le_ciInf hmin)
  have hπ : (⨅ d, B π d) = B π δ := by
    have hb (d : D) : B π δ ≤ B π d := hbayes.integral_le d Integrable.of_finite
    exact le_antisymm (ciInf_le ⟨_, forall_mem_range.mpr hb⟩ _) (le_ciInf hb)
  have hbdd (ν : ProbabilityMeasure Θ) : BddBelow (range (B ν)) := by
    let := Fintype.ofFinite Θ
    have hcont : Continuous fun r : Θ → ℝ ↦ ∫ θ, r θ ∂(ν : Measure Θ) := by
      simp_rw [integral_fintype Integrable.of_finite]
      fun_prop
    have hcomp : B ν = (fun r ↦ ∫ θ, r θ ∂(ν : Measure Θ)) ∘ R := rfl
    rw [hcomp, range_comp]
    exact ((isCompact_convex_range_risk P L).1.image hcont).bddBelow
  have hupper (ν : ProbabilityMeasure Θ) : (⨅ d, B ν d) ≤ B π δ :=
    (ciInf_le (hbdd ν) δ).trans ((hle ν δ).trans_eq hM)
  have hright : (⨆ ν, ⨅ d, B ν d) = B π δ :=
    le_antisymm (ciSup_le hupper)
      (hπ.ge.trans (le_ciSup ⟨_, forall_mem_range.mpr hupper⟩ π))
  exact hleft.trans (hM.trans hright.symm)

end TauCeti
