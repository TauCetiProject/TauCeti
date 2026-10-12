/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import TauCeti.MeasureTheory.Function.Lusin
public import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Convergence of transport maps and of their graph plans

Fix a probability measure `μ` on `X`, and let `T n, T₀ : X → Y` be almost-everywhere measurable
maps into a second-countable pseudo-emetric space. Their graph plans `TauCeti.graphPlan (T n) μ`
are probability measures on `X × Y`, and the question is how the convergence of the plans is
related to the convergence of the maps. The answer is that **narrow convergence is convergence in
measure**, which turns statements about deterministic transport plans into statements about the
maps inducing them and back.

The graph plans of `T n` converge weakly to the graph plan of `T₀` exactly when `T n` converges to
`T₀` in `μ`-measure. From convergence in measure, a subsequence converges almost everywhere, and
almost-everywhere convergence gives the convergence in distribution of the graph maps along it;
the full sequence follows because every subsequence has such a further subsequence. Conversely,
Lusin's theorem makes `T₀` continuous on a closed set `F` of nearly full measure, so that
`{(x, y) | x ∈ F, ε ≤ edist y (T₀ x)}` is a closed subset of `X × Y` carrying no mass under the
limit graph plan; the portmanteau theorem bounds the mass the plans of `T n` give it, and that
mass is exactly `μ {x ∈ F | ε ≤ edist (T n x) (T₀ x)}`.

The weak topology on `ProbabilityMeasure (X × Y)` is the one Mathlib puts on probability measures,
and graph plans are bundled through `MeasureTheory.ProbabilityMeasure.map` along `x ↦ (x, T x)`,
whose underlying measure is `TauCeti.graphPlan` by `TauCeti.toMeasure_map_prodMk_self`.

The `Lᵖ` refinement, that under convergence in measure the distances `dist (T n ·) (T₀ ·)` converge
in `Lᵖ(μ)` exactly when the family `dist (T n ·) y₀` is uniformly integrable, is Vitali's theorem
for maps into a pseudometric space and mentions no graph plan; it is
`TauCeti.tendsto_eLpNorm_dist_iff_tendstoInMeasure_and_unifIntegrable` in
`TauCeti/MeasureTheory/Function/UniformIntegrable.lean`.

## Main statements

* `TauCeti.tendsto_map_prodMk_self_iff_tendstoInMeasure` — the graph plans of `T n` converge
  weakly to the graph plan of `T₀` if and only if `T n` converges to `T₀` in `μ`-measure; the two
  implications are `TauCeti.tendsto_map_prodMk_self_of_tendstoInMeasure`, valid on any
  topological source, and `TauCeti.tendstoInMeasure_of_tendsto_map_prodMk_self`, which needs `μ`
  weakly regular for Lusin's theorem and `X × Y` with outer approximation of closed sets for the
  portmanteau theorem; a probability measure on a pseudo-metrizable Borel source has both.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, second edition, Birkhäuser 2008, Lemma 5.4.1, the equivalence between
  narrow convergence of graph plans and convergence in measure.
-/
public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

section Narrow

variable {μ : ProbabilityMeasure X} {T : ℕ → X → Y} {T₀ : X → Y}

section OfTendstoInMeasure

variable [TopologicalSpace X] [OpensMeasurableSpace X] [PseudoEMetricSpace Y]
  [OpensMeasurableSpace Y] [SecondCountableTopologyEither X Y]

/-- If the maps `T n` converge to `T₀` in `μ`-measure, then their graph plans converge weakly to
the graph plan of `T₀`. -/
theorem tendsto_map_prodMk_self_of_tendstoInMeasure (hT : ∀ n, AEMeasurable (T n) μ)
    (hT₀ : AEMeasurable T₀ μ) (h : TendstoInMeasure (μ : Measure X) T atTop T₀) :
    Tendsto (fun n ↦ μ.map fun x ↦ (x, T n x)) atTop (𝓝 (μ.map fun x ↦ (x, T₀ x))) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ms, -, hms⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε ↦ (h ε hε).comp hns
  -- `TendstoInDistribution.tendsto` is stated with the structure literal
  -- `⟨(μ : Measure X).map _, inferInstance⟩`, which is the definition of `ProbabilityMeasure.map`
  exact ⟨ms, (tendstoInDistribution_of_ae_tendsto (fun k ↦ aemeasurable_prodMk_self (hT _))
    (aemeasurable_prodMk_self hT₀) (hms.mono fun x hx ↦ tendsto_const_nhds.prodMk_nhds hx)).tendsto⟩

end OfTendstoInMeasure

variable [TopologicalSpace X] [OpensMeasurableSpace X] [(μ : Measure X).WeaklyRegular]
  [PseudoEMetricSpace Y] [SecondCountableTopology Y] [OpensMeasurableSpace Y]
  [HasOuterApproxClosed (X × Y)]

/-- If the graph plans of `T n` converge weakly to the graph plan of `T₀`, then `T n` converges
to `T₀` in `μ`-measure. -/
theorem tendstoInMeasure_of_tendsto_map_prodMk_self (hT : ∀ n, AEMeasurable (T n) μ)
    (hT₀ : AEMeasurable T₀ μ)
    (h : Tendsto (fun n ↦ μ.map fun x ↦ (x, T n x)) atTop (𝓝 (μ.map fun x ↦ (x, T₀ x)))) :
    TendstoInMeasure (μ : Measure X) T atTop T₀ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨F, -, hF, hFμ, hFcont⟩ := hT₀.exists_isClosed_measure_sdiff_lt_continuousOn
    MeasurableSet.univ (measure_ne_top _ _) hδ2.ne'
  rw [← compl_eq_univ_sdiff] at hFμ
  set C : Set (X × Y) := F ×ˢ univ ∩ {z | ε ≤ edist z.2 (T₀ z.1)} with hC
  have hCclosed : IsClosed C := by
    refine ContinuousOn.preimage_isClosed_of_isClosed (t := Ici ε) ?_ (hF.prod isClosed_univ)
      isClosed_Ici
    exact continuous_edist.comp_continuousOn
      (continuous_snd.continuousOn.prodMk (hFcont.comp continuous_fst.continuousOn fun z hz ↦ hz.1))
  have hCmeas : MeasurableSet C := hCclosed.measurableSet
  have hlim : ((μ.map fun x ↦ (x, T₀ x) : ProbabilityMeasure (X × Y)) : Measure (X × Y)) C = 0 := by
    have hempty : {x | (x, T₀ x) ∈ C} = ∅ := by ext x; simp [hC, hε.ne']
    rw [toMeasure_map_prodMk_self, graphPlan_apply hT₀ hCmeas, hempty, measure_empty]
  have hCn : Tendsto
      (fun n ↦ ((μ.map fun x ↦ (x, T n x) : ProbabilityMeasure (X × Y)) : Measure (X × Y)) C)
      atTop (𝓝 0) := by
    refine tendsto_of_le_liminf_of_limsup_le zero_le ?_
    rw [← hlim]
    exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hCclosed
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hCn (δ / 2) hδ2] with n hn
  rw [toMeasure_map_prodMk_self, graphPlan_apply (hT n) hCmeas] at hn
  calc (μ : Measure X) {x | ε ≤ edist (T n x) (T₀ x)}
      ≤ (μ : Measure X) ({x | (x, T n x) ∈ C} ∪ Fᶜ) := by
        refine measure_mono fun x hx ↦ ?_
        by_cases hxF : x ∈ F
        · exact Or.inl ⟨⟨hxF, mem_univ _⟩, hx⟩
        · exact Or.inr hxF
    _ ≤ (μ : Measure X) {x | (x, T n x) ∈ C} + (μ : Measure X) Fᶜ := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hn hFμ.le
    _ = δ := ENNReal.add_halves δ

/-- **Narrow convergence of graph plans is convergence in measure.** For a weakly regular
probability measure `μ` on a space `X` with measurable opens and almost-everywhere measurable maps
into a second-countable pseudo-emetric space `Y` such that closed subsets of `X × Y` are outer
approximable, the graph plans of `T n` converge weakly to the graph plan of `T₀` if and only if
`T n` converges to `T₀` in `μ`-measure. Both instance hypotheses hold when `X` is a
pseudo-metrizable Borel space. -/
theorem tendsto_map_prodMk_self_iff_tendstoInMeasure (hT : ∀ n, AEMeasurable (T n) μ)
    (hT₀ : AEMeasurable T₀ μ) :
    Tendsto (fun n ↦ μ.map fun x ↦ (x, T n x)) atTop (𝓝 (μ.map fun x ↦ (x, T₀ x))) ↔
      TendstoInMeasure (μ : Measure X) T atTop T₀ :=
  ⟨tendstoInMeasure_of_tendsto_map_prodMk_self hT hT₀,
    tendsto_map_prodMk_self_of_tendstoInMeasure hT hT₀⟩

end Narrow

end TauCeti
