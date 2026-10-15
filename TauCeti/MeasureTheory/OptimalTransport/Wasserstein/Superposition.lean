/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Space
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Measure.ContinuousMap
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map
import TauCeti.MeasureTheory.Measure.Tight.Basic
import TauCeti.MeasureTheory.Measure.Tight.CurveAction
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.AbsolutelyContinuous
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PolygonalPlan
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward
import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.WeakConvergence
import TauCeti.Topology.Instances.Real.DyadicGrid
import TauCeti.Topology.MetricSpace.Kuratowski

/-!
# Lisini's superposition principle

Let `X` be a complete separable metric space and `1 < p < ∞`. A curve `μ` in the finite-moment
Wasserstein space `P_p(X)` that is absolutely continuous on `[a, b]` with finite `p`-action
`A_p(μ)` is the curve of time marginals of a law on paths: there is a probability measure `η` on
the path space `C([a, b], X)`, concentrated on absolutely continuous paths, such that

* the law of `γ t` under `η` is `μ t` for every `t ∈ [a, b]`;
* the expected `p`-action of the paths is the `p`-action of the curve, `∫ A_p(γ) dη = A_p(μ)`;
* the averaged speed of the paths is the metric speed of the curve,
  `|μ'|(t) ^ p = ∫ |γ'|(t) ^ p dη(γ)` for almost every `t ∈ [a, b]`.

Every law on absolutely continuous paths with time marginals `μ` has expected action at least
`A_p(μ)` (`TauCeti.curveAction_le_lintegral_of_coe_eq_map_IccExtend`), so `η` is a representation
of minimal action.

The theorem is first proved in a separable Banach space `E`. There `η` is a narrow limit of the
polygonal laws on the dyadic grids of `[a, b]`
(`TauCeti.exists_map_IccExtend_eq_lintegral_curveAction_le`), whose expected actions are at most
`A_p(μ)` and whose time marginals at each dyadic time are eventually the value of `μ` there. For
`1 < p` this family is tight
(`isTightMeasureSet_of_map_eval_of_absolutelyContinuousOnInterval_of_lintegral_curveAction_le`),
and the laws concentrated on absolutely continuous paths with expected action at most `A_p(μ)`
form a weakly closed set
(`isClosed_setOfPred_ae_absolutelyContinuousOnInterval_and_lintegral_le`), so Prokhorov's theorem
provides a limit law with the same properties. Its time marginals agree with
`μ` at the dyadic times, hence everywhere on `[a, b]` by continuity.

A complete separable metric space `X` embeds isometrically, as a closed subset, into a separable
Banach space `E` (`TauCeti.exists_isometry_separableSpace_completeSpace`). Pushforward along the
embedding is an isometry of Wasserstein spaces, so it carries `μ` to a curve in `P_p(E)` with the
same metric derivative and action. The law on paths in `E` that represents this curve is
concentrated on paths with values in the closed image of `X`, because its time marginals are, and
so it is the image of a law on `C([a, b], X)`, which represents `μ`.

## Main results

* `TauCeti.exists_map_IccExtend_eq_lintegral_curveAction_eq`: **Lisini's superposition
  principle** in a complete separable metric space.

## References

* S. Lisini, *Characterization of absolutely continuous curves in Wasserstein spaces*, Calc. Var.
  Partial Differential Equations 28 (2007), 85--120, Theorem 5.
* L. Ambrosio, N. Gigli and G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 8.2.1, for the Euclidean case.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Interval

namespace TauCeti

section Superposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- In a separable Banach space `E`, a curve `μ` in `P_p(E)`, absolutely continuous on `[a, b]` with
finite `p`-action, is the curve of time marginals of a probability measure on `C([a, b], E)`
concentrated on absolutely continuous paths, whose expected `p`-action is the `p`-action of `μ`.
The metric version `TauCeti.exists_map_IccExtend_eq_lintegral_curveAction_eq` follows by an
isometric embedding, and also adds the averaged-speed identity. -/
private theorem exists_map_IccExtend_eq_lintegral_curveAction_eq_of_normedSpace (hp1 : 1 < p)
    (hp : p ≠ ∞)
    {μ : ℝ → WassersteinSpace p E} {a b : ℝ} (hab : a < b)
    (hμ : AbsolutelyContinuousOnInterval μ a b) (hA : curveAction p.toReal μ a b ≠ ∞) :
    ∃ η : Measure C(Icc a b, E), IsProbabilityMeasure η ∧
      (∀ᵐ γ : C(Icc a b, E) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab.le γ) a b) ∧
      (∀ t ∈ Icc a b, η.map (fun γ : C(Icc a b, E) ↦ IccExtend hab.le γ t) =
        ((μ t : ProbabilityMeasure E) : Measure E)) ∧
      ∫⁻ γ, curveAction p.toReal (IccExtend hab.le γ) a b ∂η = curveAction p.toReal μ a b := by
  have hr : 1 < p.toReal := by simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  -- The polygonal laws on the dyadic grids of `[a, b]`.
  choose η hηP hηAC hηgrid hηA using fun n : ℕ ↦
    exists_map_IccExtend_eq_lintegral_curveAction_le hp hab hμ (N := 2 ^ n) (by positivity)
  set ηs : ℕ → ProbabilityMeasure C(Icc a b, E) := fun n ↦ ⟨η n, hηP n⟩
  set D := {t : Icc a b | ∃ n k : ℕ, k ≤ 2 ^ n ∧ (t : ℝ) = a + k * ((b - a) / 2 ^ n)}
  have hDd : Dense D := dense_setOfPred_eq_add_mul_div_two_pow hab
  -- At a dyadic time, the time marginals of the polygonal laws are eventually the value of `μ`.
  have hD (t : Icc a b) (ht : t ∈ D) : ∃ m, ∀ n ≥ m,
      (η n).map (fun γ : C(Icc a b, E) ↦ γ t) = ((μ t : ProbabilityMeasure E) : Measure E) := by
    obtain ⟨m, k, hk, htk⟩ := ht
    refine ⟨m, fun n hn ↦ ?_⟩
    obtain ⟨j, hj, htj⟩ := exists_eq_add_mul_div_two_pow_of_le hk htk hn
    have := hηgrid n j (by exact_mod_cast hj)
    push_cast at this
    rw [← htj] at this
    simpa only [IccExtend_val] using this
  -- The polygonal laws form a tight family.
  have htight : IsTightMeasureSet (range η) := by
    refine
      isTightMeasureSet_of_map_eval_of_absolutelyContinuousOnInterval_of_lintegral_curveAction_le
        hab.le hr hDd (fun t ht ↦ ?_) hA (by rintro _ ⟨n, rfl⟩; exact hηAC n)
        (by rintro _ ⟨n, rfl⟩; exact hηA n)
    obtain ⟨m, hm⟩ := hD t ht
    refine (isTightMeasureSet_of_finite (((finite_Iio m).image fun n ↦
      (η n).map fun γ : C(Icc a b, E) ↦ γ t).insert ((μ t : ProbabilityMeasure E) : Measure E))
      ?_).subset ?_
    · rintro ν (rfl | ⟨n, -, rfl⟩) <;> infer_instance
    · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      dsimp only
      rcases lt_or_ge n m with hn | hn
      · exact mem_insert_of_mem _ ⟨n, hn, rfl⟩
      · rw [hm n hn]
        exact mem_insert _ _
  -- By Prokhorov's theorem, a subsequence converges to a law `ηlim`.
  have hcpt : IsCompact (closure (range ηs)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight
    ext ν
    simp only [exists_range_iff]
    simp only [mem_ofPred_eq, mem_range, ηs, ProbabilityMeasure.coe_mk]
  obtain ⟨ηlim, -, φ, hφ, hconv⟩ := hcpt.tendsto_subseq fun n ↦ subset_closure (mem_range_self n)
  -- The limit is concentrated on absolutely continuous paths, with expected action at most
  -- `A_p(μ)`.
  obtain ⟨hAClim, hlelim⟩ : (∀ᵐ γ : C(Icc a b, E) ∂(ηlim : Measure C(Icc a b, E)),
      AbsolutelyContinuousOnInterval (IccExtend hab.le γ) a b) ∧
        ∫⁻ γ, curveAction p.toReal (IccExtend hab.le γ) a b ∂(ηlim : Measure C(Icc a b, E)) ≤
          curveAction p.toReal μ a b :=
    (isClosed_setOfPred_ae_absolutelyContinuousOnInterval_and_lintegral_le hab.le hr
      hA).mem_of_tendsto hconv (Eventually.of_forall fun n ↦ ⟨hηAC (φ n), hηA (φ n)⟩)
  -- The time marginals of `ηlim` are those of `μ` at the dyadic times.
  have hmargD : EqOn (fun t : Icc a b ↦ ηlim.map fun γ : C(Icc a b, E) ↦ γ t)
      (fun t ↦ (μ t : ProbabilityMeasure E)) D := by
    intro t ht
    obtain ⟨m, hm⟩ := hD t ht
    refine tendsto_nhds_unique
      (((ProbabilityMeasure.continuous_map (continuous_eval_const t)).tendsto ηlim).comp hconv)
      (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop m] with n hn
    refine ProbabilityMeasure.toMeasure_injective ?_
    simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map]
    exact (hm (φ n) (hn.trans (hφ.id_le n))).symm
  -- Both curves of time marginals are continuous, so they agree on `[a, b]`.
  have hcont_η : Continuous fun t : Icc a b ↦ ηlim.map fun γ : C(Icc a b, E) ↦ γ t :=
    ηlim.continuous_map_of_forall_continuous (fun s ↦ (continuous_eval_const s).aemeasurable)
      fun γ ↦ γ.continuous
  have hcont_μ : Continuous fun t : Icc a b ↦ (μ t : ProbabilityMeasure E) :=
    WassersteinSpace.continuous_toProbabilityMeasure.comp
      (hμ.continuousOn'.comp_continuous continuous_subtype_val fun t ↦ by
        rw [uIcc_of_le hab.le]
        exact t.2)
  have hmarg (t : ℝ) (ht : t ∈ Icc a b) :
      (ηlim : Measure C(Icc a b, E)).map (fun γ : C(Icc a b, E) ↦ IccExtend hab.le γ t) =
        ((μ t : ProbabilityMeasure E) : Measure E) := by
    have := congrArg (fun ν : ProbabilityMeasure E ↦ (ν : Measure E))
      (congrFun (hcont_η.ext_on hDd hcont_μ hmargD) ⟨t, ht⟩)
    simpa [IccExtend_of_mem hab.le _ ht] using this
  -- By minimality of the action of `μ`, the expected action of `ηlim` is exactly `A_p(μ)`.
  refine ⟨ηlim, inferInstance, hAClim, hmarg, le_antisymm hlelim
    (curveAction_le_lintegral_of_coe_eq_map_IccExtend hab.le hAClim hp fun t ht ↦
      (hmarg t (uIcc_of_le hab.le ▸ ht)).symm)⟩

end Superposition

section MetricSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompleteSpace X] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Lisini's superposition principle** in a complete separable metric space. Let `1 < p < ∞`
and let `μ` be a curve in `P_p(X)`, absolutely continuous on `[a, b]` with finite `p`-action,
where `a < b`. There is a probability measure `η` on `C([a, b], X)`, concentrated on absolutely
continuous paths, whose law at each time `t ∈ [a, b]` is `μ t`, whose expected `p`-action is the
`p`-action of `μ`, and whose averaged speed is the metric speed of `μ`:
`|μ'|(t) ^ p = ∫ |γ'|(t) ^ p dη` at almost every `t ∈ [a, b]`. -/
theorem exists_map_IccExtend_eq_lintegral_curveAction_eq (hp1 : 1 < p) (hp : p ≠ ∞)
    {μ : ℝ → WassersteinSpace p X} {a b : ℝ} (hab : a < b)
    (hμ : AbsolutelyContinuousOnInterval μ a b) (hA : curveAction p.toReal μ a b ≠ ∞) :
    ∃ η : Measure C(Icc a b, X), IsProbabilityMeasure η ∧
      (∀ᵐ γ : C(Icc a b, X) ∂η, AbsolutelyContinuousOnInterval (IccExtend hab.le γ) a b) ∧
      (∀ t ∈ Icc a b, η.map (fun γ : C(Icc a b, X) ↦ IccExtend hab.le γ t) =
        ((μ t : ProbabilityMeasure X) : Measure X)) ∧
      ∫⁻ γ, curveAction p.toReal (IccExtend hab.le γ) a b ∂η = curveAction p.toReal μ a b ∧
      ∀ᵐ t, t ∈ Icc a b → metricDerivative μ t ^ p.toReal =
        ∫⁻ γ, metricDerivative (IccExtend hab.le γ) t ^ p.toReal ∂η := by
  -- Embed `X` isometrically into a separable Banach space `E`.
  obtain ⟨E, _, _, _, _, ι, hι⟩ := exists_isometry_separableSpace_completeSpace X
  borelize E
  have hιm : MeasurableEmbedding ι := hι.isClosedEmbedding.measurableEmbedding
  -- Pushforward along `ι` is an isometry `P_p(X) → P_p(E)`, so `ι_# μ` is a curve in `P_p(E)`
  -- with the same regularity and action as `μ`; it has a representing law `η` on paths in `E`.
  set ιW := WassersteinSpace.map (p := p) ι (fun _ ↦ measurable_edist_right) hιm.measurable
    hι.lipschitzWith
  have hιW : Isometry ιW := WassersteinSpace.isometry_map hιm hι
  have hιWμ (t : ℝ) : (((ιW ∘ μ) t : ProbabilityMeasure E) : Measure E) =
      ((μ t : ProbabilityMeasure X) : Measure X).map ι := by
    simp [ιW, ProbabilityMeasure.toMeasure_map]
  obtain ⟨η, hηP, hηAC, hηmarg, hηA⟩ :=
    exists_map_IccExtend_eq_lintegral_curveAction_eq_of_normedSpace hp1 hp hab
      (hιW.absolutelyContinuousOnInterval_comp_iff.2 hμ) (by rwa [hιW.curveAction_comp])
  -- `η` is concentrated on the paths with values in the closed set `range ι`: it is so at the
  -- times of a countable dense subset of `[a, b]`, because the time marginals of `η` are images
  -- of laws on `X`, hence at all times by continuity of the paths.
  have hD (t : Icc a b) : ∀ᵐ γ ∂η, γ t ∈ range ι := by
    have := ae_map_mem_range hιm.measurableSet_range hιm.measurable.aemeasurable
      (μ := ((μ t : ProbabilityMeasure X) : Measure X))
    rw [← hιWμ, ← hηmarg t t.2] at this
    filter_upwards [ae_of_ae_map (measurable_IccExtend_apply hab.le _).aemeasurable this]
      with γ hγ
    rwa [IccExtend_val] at hγ
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc a b)
  -- The pullback of `η` along postcomposition with `ι` to the paths in `X` represents `μ`.
  obtain ⟨hprob, hηX⟩ := isProbabilityMeasure_comap_postcomp ι hι.isClosedEmbedding η hηP
    hDc hDd fun t _ ↦ hD t
  set Φ : C(Icc a b, X) → C(Icc a b, E) := (⟨ι, hι.continuous⟩ : C(X, E)).comp
  have hΦ : MeasurableEmbedding Φ := (ContinuousMap.continuous_postcomp _).measurableEmbedding
    (ContinuousMap.postcomp_injective _ hι.injective)
  have hΦIcc (γ : C(Icc a b, X)) : IccExtend hab.le (Φ γ) = ι ∘ IccExtend hab.le γ := by
    ext t
    simp [Φ, IccExtend_apply]
  set ηX := η.comap Φ
  have hAC : ∀ᵐ γ : C(Icc a b, X) ∂ηX,
      AbsolutelyContinuousOnInterval (IccExtend hab.le γ) a b := by
    rw [← hηX, hΦ.ae_map_iff] at hηAC
    simpa only [hΦIcc, hι.absolutelyContinuousOnInterval_comp_iff] using hηAC
  have hmarg (t : ℝ) (ht : t ∈ Icc a b) :
      ηX.map (fun γ : C(Icc a b, X) ↦ IccExtend hab.le γ t) =
        ((μ t : ProbabilityMeasure X) : Measure X) := by
    have h := hηmarg t ht
    rw [← hηX, Measure.map_map (measurable_IccExtend_apply hab.le t) hΦ.measurable, hιWμ] at h
    simp only [Function.comp_def, hΦIcc] at h
    have h' : (ηX.map fun γ : C(Icc a b, X) ↦ IccExtend hab.le γ t).map ι =
        ((μ t : ProbabilityMeasure X) : Measure X).map ι := by
      rwa [Measure.map_map hιm.measurable (measurable_IccExtend_apply hab.le t)]
    exact hιm.map_injective h'
  have heq : ∫⁻ γ, curveAction p.toReal (IccExtend hab.le γ) a b ∂ηX =
      curveAction p.toReal μ a b := by
    rw [← hιW.curveAction_comp, ← hηA, ← hηX, hΦ.lintegral_map]
    simp only [hΦIcc, hι.curveAction_comp]
  have hmarg' (t : ℝ) (ht : t ∈ uIcc a b) := (hmarg t (uIcc_of_le hab.le ▸ ht)).symm
  refine ⟨ηX, hprob, hAC, hmarg, heq, ?_⟩
  filter_upwards [ae_metricDerivative_rpow_eq_lintegral_of_coe_eq_map_IccExtend hab.le hAC hp
    (heq ▸ hA) hmarg' heq] with t ht htab
  exact ht (uIcc_of_le hab.le ▸ htab)

end MetricSpace

end TauCeti
