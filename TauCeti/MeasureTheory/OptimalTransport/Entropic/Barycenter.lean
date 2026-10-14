/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Entropic.ZeroTemperature
public import TauCeti.Topology.Semicontinuity.GammaConvergence
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.Data.EReal.Operations
import TauCeti.MeasureTheory.OptimalTransport.Entropic.Stability

/-!
# Entropic Wasserstein barycenters and their zero-temperature limit

For laws `μ i` on a metric space, weights `w i` and a temperature `ε`, the *entropic barycenter
cost* of a law `ν` is

`F_ε(ν) = ∑ i, w i * inf_{π ∈ Π(ν, μ i)} (∫ d(x, y) ^ p dπ + ε * klDiv π (ν ⊗ μ i))`,

the weighted sum of the entropically regularised transport costs from `ν` to the `μ i`. Each
entropy term is taken relative to the product of the two marginals of its own transport problem.
Other functionals go by the same name and have different minimizers: regularising the entropy of
the barycenter itself, taking the entropy relative to a fixed ambient reference measure, or
replacing each regularised cost by its debiased Sinkhorn divergence. They are not treated here.

At `ε = 0` the cost is the weighted Wasserstein cost `ν ↦ ∑ i, w i * W_p(ν, μ i) ^ p`, whose
minimizers are the Wasserstein barycenters of the weighted family `μ i` in the sense of Agueh and
Carlier. As `ε → 0⁺` the costs decrease to it pointwise, and they *Γ-converge* to it for the weak
topology on probability measures over a Polish metric space, as soon as every `μ i` has finite
`p`-moment. Each `F_ε` is weakly lower semicontinuous, by
`TauCeti.lowerSemicontinuous_entropicTransportCost`, so on a compact space it has a minimizer, an
*entropic barycenter*. The fundamental theorem of Γ-convergence then says that, on a compact metric
space, the minimal entropic costs converge to the minimal Wasserstein cost, every weak cluster point
of entropic barycenters is a Wasserstein barycenter, and the entropic barycenters converge to the
Wasserstein barycenter when it is unique.

## Main definitions

* `TauCeti.entropicBarycenterCost p ε w μ ν`: the entropic barycenter cost of `ν`.

## Main statements

* `TauCeti.entropicBarycenterCost_zero`: at zero temperature, the entropic barycenter cost is the
  weighted Wasserstein cost.
* `TauCeti.tendsto_entropicBarycenterCost`: the zero-temperature limit of the entropic barycenter
  cost of a fixed law.
* `TauCeti.lowerSemicontinuous_entropicBarycenterCost`: the entropic barycenter cost is weakly
  lower semicontinuous.
* `TauCeti.tendstoGamma_entropicBarycenterCost`: the entropic barycenter costs Γ-converge to the
  weighted Wasserstein cost as the temperature decreases to `0`.
* `TauCeti.exists_isMinOn_entropicBarycenterCost`: entropic barycenters exist on compact spaces.
* `TauCeti.isMinOn_sum_mul_wassersteinEDist_rpow_of_tendsto`: weak cluster points of entropic
  barycenters are Wasserstein barycenters.
* `TauCeti.tendsto_iInf_entropicBarycenterCost` and
  `TauCeti.tendsto_of_isMinOn_entropicBarycenterCost`: on a compact space the minimal values
  converge, and the entropic barycenters converge to the Wasserstein barycenter when it is unique.

## References

* M. Cuturi and A. Doucet, *Fast computation of Wasserstein barycenters*, Proceedings of the 31st
  International Conference on Machine Learning, PMLR 32 (2014), 685--693, for barycenters of
  entropically regularised transport costs.
* L. Chizat, *Doubly regularized entropic Wasserstein barycenters*, arXiv:2303.11844, 2023, for
  the entropic barycenter functional with the entropy of each plan relative to its marginals, and
  the other regularisations it is compared with.
* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43 (2011),
  904--924, for Wasserstein barycenters.
* A. Braides, *Γ-convergence for Beginners*, Oxford University Press 2002, Chapter 1.
-/

public section

noncomputable section

open Filter InformationTheory MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

/-! ### The entropic barycenter cost -/

section Definition

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [PseudoEMetricSpace X]

/-- The *entropic barycenter cost* `∑ i, w i * OT_ε(ν, μ i)` of a law `ν`, where `OT_ε(ν, μ i)` is
the infimum over the couplings `π` of `ν` and `μ i` of
`∫⁻ z, edist z.1 z.2 ^ p ∂π + ε * klDiv π (ν ⊗ μ i)`. Each relative entropy is taken against the
product of the two marginals of its own transport problem. The definition is meant for
`0 < p < ∞`: it uses `p.toReal`, so at `p = ∞` the integrand is the trivial cost `d ^ 0`. For
`0 < p < ∞` and a measurable extended distance, at `ε = 0` this is the weighted Wasserstein cost
`∑ i, w i * W_p(ν, μ i) ^ p` (`TauCeti.entropicBarycenterCost_zero`). -/
def entropicBarycenterCost (p : ℝ≥0∞) (ε : ℝ≥0) (w : ι → ℝ≥0) (μ : ι → Measure X)
    (ν : Measure X) : ℝ≥0∞ :=
  ∑ i, (w i : ℝ≥0∞) * entropicTransportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) ε ν (μ i)

variable {p : ℝ≥0∞} {ε ε' : ℝ≥0} {w : ι → ℝ≥0} {μ : ι → Measure X} {ν : Measure X}

/-- The entropic barycenter cost as a weighted sum of entropic transport costs. -/
theorem entropicBarycenterCost_def :
    entropicBarycenterCost p ε w μ ν =
      ∑ i, (w i : ℝ≥0∞) *
        entropicTransportCost (fun z : X × X ↦ edist z.1 z.2 ^ p.toReal) ε ν (μ i) :=
  (rfl)

/-- The entropic barycenter cost is monotone in the temperature. -/
theorem entropicBarycenterCost_mono (h : ε ≤ ε') :
    entropicBarycenterCost p ε w μ ν ≤ entropicBarycenterCost p ε' w μ ν :=
  Finset.sum_le_sum fun _ _ ↦ by gcongr; exact entropicTransportCost_mono le_rfl h

/-- **At zero temperature the entropic barycenter cost is the weighted Wasserstein cost**
`∑ i, w i * W_p(ν, μ i) ^ p`, whose minimizers are the Wasserstein barycenters of the `μ i`. -/
theorem entropicBarycenterCost_zero (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp0 : p ≠ 0)
    (hp : p ≠ ∞) :
    entropicBarycenterCost p 0 w μ ν =
      ∑ i, (w i : ℝ≥0∞) * wassersteinEDist p ν (μ i) ^ p.toReal := by
  simp only [entropicBarycenterCost, entropicTransportCost_zero,
    wassersteinEDist_rpow_eq_transportCost hd hp0 hp]

/-- The entropic barycenter cost dominates the weighted Wasserstein cost. -/
theorem sum_mul_wassersteinEDist_rpow_le_entropicBarycenterCost
    (hd : Measurable fun z : X × X ↦ edist z.1 z.2) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    ∑ i, (w i : ℝ≥0∞) * wassersteinEDist p ν (μ i) ^ p.toReal ≤
      entropicBarycenterCost p ε w μ ν :=
  (entropicBarycenterCost_zero hd hp0 hp).symm.trans_le (entropicBarycenterCost_mono bot_le)

end Definition

/-! ### The zero-temperature limit -/

section Metric

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] [PolishSpace X] [BorelSpace X]
  {p : ℝ≥0∞} {ι : Type*} [Fintype ι] {w : ι → ℝ≥0} {μ : ι → Measure X}
  [∀ i, IsProbabilityMeasure (μ i)]

/-- **The zero-temperature limit of the entropic barycenter cost.** On a Polish metric space, for
`0 < p < ∞` and laws `μ i` of finite `p`-moment, the entropic barycenter cost of every probability
law `ν` converges to its weighted Wasserstein cost as `ε → 0⁺`. -/
theorem tendsto_entropicBarycenterCost (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hμ : ∀ i, HasFiniteMoment p (μ i)) (ν : Measure X) [IsProbabilityMeasure ν] :
    Tendsto (fun ε ↦ entropicBarycenterCost p ε w μ ν) (𝓝[>] 0)
      (𝓝 (∑ i, (w i : ℝ≥0∞) * wassersteinEDist p ν (μ i) ^ p.toReal)) :=
  tendsto_finsetSum _ fun i _ ↦ ENNReal.Tendsto.const_mul
    (tendsto_entropicTransportCost_wassersteinEDist_rpow hp0 hp ν (μ i) (hμ i))
    (Or.inr ENNReal.coe_ne_top)

/-! ### Γ-convergence and entropic barycenters -/

/-- The entropic barycenter cost is weakly lower semicontinuous on the probability laws over a
Polish metric space, at every temperature. -/
theorem lowerSemicontinuous_entropicBarycenterCost (p : ℝ≥0∞) (ε : ℝ≥0) :
    LowerSemicontinuous fun ν : ProbabilityMeasure X ↦ entropicBarycenterCost p ε w μ ν := by
  refine lowerSemicontinuous_sum fun i _ ↦
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp_lowerSemicontinuous ?_
      fun _ _ h ↦ mul_le_mul_right h _
  have hc : LowerSemicontinuous fun z : X × X ↦ edist z.1 z.2 ^ p.toReal :=
    (ENNReal.continuous_rpow_const.comp continuous_edist).lowerSemicontinuous
  let μi : ProbabilityMeasure X := ⟨μ i, inferInstance⟩
  exact (lowerSemicontinuous_entropicTransportCost hc ε).comp
    (continuous_id.prodMk (continuous_const (y := μi)))

/-- **Γ-convergence of entropic barycenter costs.** On a Polish metric space, for `0 < p < ∞` and
laws `μ i` of finite `p`-moment, the entropic barycenter costs at temperatures `ε n → 0⁺`
Γ-converge, for the weak topology on probability laws, to the weighted Wasserstein cost
`ν ↦ ∑ i, w i * W_p(ν, μ i) ^ p`. The costs are viewed as `EReal`-valued functionals, as in
`TauCeti.TendstoGamma`. -/
theorem tendstoGamma_entropicBarycenterCost (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hμ : ∀ i, HasFiniteMoment p (μ i)) {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (𝓝[>] 0)) :
    TendstoGamma (fun n (ν : ProbabilityMeasure X) ↦ (entropicBarycenterCost p (ε n) w μ ν : EReal))
      fun ν ↦ ((∑ i, (w i : ℝ≥0∞) * wassersteinEDist p ν.toMeasure (μ i) ^ p.toReal : ℝ≥0∞) :
        EReal) := by
  have hd : Measurable fun z : X × X ↦ edist z.1 z.2 := measurable_edist
  have hmono : Monotone fun a : ℝ≥0∞ ↦ (a : EReal) := fun _ _ h ↦
    EReal.coe_ennreal_le_coe_ennreal_iff.2 h
  have hlsc : LowerSemicontinuous fun ν : ProbabilityMeasure X ↦
      ((∑ i, (w i : ℝ≥0∞) * wassersteinEDist p ν.toMeasure (μ i) ^ p.toReal : ℝ≥0∞) : EReal) := by
    simp_rw [← entropicBarycenterCost_zero hd hp0 hp]
    exact continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      (lowerSemicontinuous_entropicBarycenterCost p 0) hmono
  refine ⟨fun ν u hu ↦ ?_, fun ν ↦ ⟨fun _ ↦ ν, tendsto_const_nhds, ?_⟩⟩
  · -- The liminf inequality: the Wasserstein cost is lower semicontinuous and smaller.
    refine (hlsc.le_liminf ν).trans ((hu.liminf_le_liminf_comp).trans
      (liminf_le_liminf (Eventually.of_forall fun n ↦ hmono ?_)))
    exact sum_mul_wassersteinEDist_rpow_le_entropicBarycenterCost hd hp0 hp
  · -- The constant recovery sequence: the costs of a fixed law converge.
    have h := (continuous_coe_ennreal_ereal.tendsto _).comp
      ((tendsto_entropicBarycenterCost hp0 hp hμ (w := w) ν.toMeasure).comp hε)
    exact h.limsup_eq.le

/-- **Existence of entropic barycenters.** On a nonempty compact metric space, the entropic
barycenter cost attains its minimum over the probability laws, at every temperature. -/
theorem exists_isMinOn_entropicBarycenterCost [CompactSpace X] [Nonempty X] (p : ℝ≥0∞)
    (ε : ℝ≥0) :
    ∃ ν : ProbabilityMeasure X, IsMinOn (fun ν : ProbabilityMeasure X ↦
      entropicBarycenterCost p ε w μ ν) univ ν :=
  let ν₀ : ProbabilityMeasure X := ⟨Measure.dirac (Classical.arbitrary X), inferInstance⟩
  let ⟨ν, _, hν⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨ν₀, mem_univ _⟩ isCompact_univ
    ((lowerSemicontinuous_entropicBarycenterCost (μ := μ) (w := w) p ε).lowerSemicontinuousOn univ)
  ⟨ν, hν⟩

/-- **Cluster points of entropic barycenters are Wasserstein barycenters.** On a Polish metric
space, for `0 < p < ∞` and laws `μ i` of finite `p`-moment, let `ν n` minimize the entropic
barycenter cost at temperature `ε n`, with `ε n → 0⁺`. Then every weak limit of a subsequence of
`ν n` minimizes the weighted Wasserstein cost `ν ↦ ∑ i, w i * W_p(ν, μ i) ^ p`. -/
theorem isMinOn_sum_mul_wassersteinEDist_rpow_of_tendsto (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hμ : ∀ i, HasFiniteMoment p (μ i)) {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (𝓝[>] 0))
    {ν : ℕ → ProbabilityMeasure X}
    (hν : ∀ n, IsMinOn (fun ν : ProbabilityMeasure X ↦ entropicBarycenterCost p (ε n) w μ ν)
      univ (ν n))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {ν₀ : ProbabilityMeasure X}
    (hν₀ : Tendsto (ν ∘ φ) atTop (𝓝 ν₀)) :
    IsMinOn (fun ν : ProbabilityMeasure X ↦
      ∑ i, (w i : ℝ≥0∞) * wassersteinEDist p ν.toMeasure (μ i) ^ p.toReal) univ ν₀ := by
  have h := (tendstoGamma_entropicBarycenterCost hp0 hp hμ hε).isMinOn_of_tendsto
    (fun n ↦ isMinOn_univ_iff.2 fun ν' ↦
      EReal.coe_ennreal_le_coe_ennreal_iff.2 (isMinOn_univ_iff.1 (hν n) ν')) hφ hν₀
  exact isMinOn_univ_iff.2 fun ν' ↦
    EReal.coe_ennreal_le_coe_ennreal_iff.1 (isMinOn_univ_iff.1 h ν')

section Compact

variable [CompactSpace X]

/-- **Convergence of the minimal entropic barycenter costs.** On a compact metric space, for
`0 < p < ∞`, the minimal entropic barycenter costs at temperatures `ε n → 0⁺` converge to the
minimal weighted Wasserstein cost. No moment hypothesis is needed: on a compact space every law
has finite `p`-moment. -/
theorem tendsto_iInf_entropicBarycenterCost (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (𝓝[>] 0)) :
    Tendsto (fun n ↦ ⨅ ν : ProbabilityMeasure X, entropicBarycenterCost p (ε n) w μ ν) atTop
      (𝓝 (⨅ ν : ProbabilityMeasure X,
        ∑ i, (w i : ℝ≥0∞) * wassersteinEDist p ν.toMeasure (μ i) ^ p.toReal)) := by
  -- On a compact space every law has finite `p`-moment.
  have hμ (i : ι) : HasFiniteMoment p (μ i) :=
    have := nonempty_of_isProbabilityMeasure (μ i)
    hasFiniteMoment_of_boundedSpace (μ i)
  -- In a compact space every sequence of functionals is equicoercive.
  have h := (tendstoGamma_entropicBarycenterCost (w := w) hp0 hp hμ hε).tendsto_iInf
    (equicoercive_def.2 fun _ ↦ ⟨univ, isCompact_univ, fun _ _ _ ↦ mem_univ _⟩)
  simp_rw [← EReal.coe_ennreal_iInf] at h
  exact EReal.tendsto_coe_ennreal.1 h

/-- **Convergence of entropic barycenters.** On a compact metric space, for `0 < p < ∞`, if the
weighted Wasserstein cost `ν ↦ ∑ i, w i * W_p(ν, μ i) ^ p` has a unique minimizer `ν₀`, then
minimizers `ν n` of the entropic barycenter costs at temperatures `ε n → 0⁺` converge weakly to
`ν₀`. -/
theorem tendsto_of_isMinOn_entropicBarycenterCost (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {ε : ℕ → ℝ≥0} (hε : Tendsto ε atTop (𝓝[>] 0))
    {ν : ℕ → ProbabilityMeasure X}
    (hν : ∀ n, IsMinOn (fun ν : ProbabilityMeasure X ↦ entropicBarycenterCost p (ε n) w μ ν)
      univ (ν n))
    {ν₀ : ProbabilityMeasure X}
    (huniq : ∀ ν' : ProbabilityMeasure X, IsMinOn (fun ν : ProbabilityMeasure X ↦
      ∑ i, (w i : ℝ≥0∞) * wassersteinEDist p ν.toMeasure (μ i) ^ p.toReal) univ ν' → ν' = ν₀) :
    Tendsto ν atTop (𝓝 ν₀) := by
  -- On a compact space every law has finite `p`-moment.
  have hμ (i : ι) : HasFiniteMoment p (μ i) :=
    have := nonempty_of_isProbabilityMeasure (μ i)
    hasFiniteMoment_of_boundedSpace (μ i)
  -- Every subsequence has a further convergent subsequence, whose limit is a minimizer.
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ν', -, ψ, hψ, hν'⟩ := isCompact_univ.tendsto_subseq fun n ↦ mem_univ (ν (ns n))
  refine ⟨ψ, ?_⟩
  rwa [huniq ν' (isMinOn_sum_mul_wassersteinEDist_rpow_of_tendsto hp0 hp hμ hε hν
    (hns.comp hψ.tendsto_atTop) hν')] at hν'

end Compact

end Metric

end TauCeti
