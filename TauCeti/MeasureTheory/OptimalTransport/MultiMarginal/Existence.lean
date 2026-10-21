/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map

/-!
# Existence of optimal multi-marginal couplings

The multi-marginal couplings of finitely many tight probability measures `μ i` on spaces `X i`
(for instance, any probability measures on Polish spaces) form, under the separation hypotheses
of Prokhorov's theorem, a weakly compact set of probability measures on the product `∀ i, X i`.
If moreover the spaces `X i` are second countable metrizable Borel spaces, a lower semicontinuous
cost `c : (∀ i, X i) → ℝ≥0∞` attains its infimum on it. This is the multi-marginal form of the
existence theorem for optimal transport plans, and the argument is the same.

* *Closedness*: being a multi-coupling says that each coordinate pushforward `π.map (eval i)` is
  `μ i`, and pushing forward along a continuous coordinate projection is weakly continuous.
* *Tightness*: for `n` marginals, if `K i` is a compact set missing at most `ε / n` of the mass of
  `μ i`, the compact box `univ.pi K` misses at most `ε` of the mass of every multi-coupling,
  because the complement of the box is covered by the preimages of the complements of its sides.
* *Compactness* then follows from Prokhorov's theorem, and existence of a minimizer from the lower
  semicontinuity of `π ↦ ∫⁻ c ∂π` for the weak topology.

The index type is finite, and the minimum value may be `∞`.

## Main statements

* `TauCeti.isClosed_setOfPred_isMultiCoupling`: the multi-couplings are weakly closed;
* `TauCeti.isTightMeasureSet_setOfPred_isMultiCoupling`: the multi-couplings of tight measures
  form a tight family;
* `TauCeti.isCompact_setOfPred_isMultiCoupling`: Prokhorov's theorem for multi-couplings;
* `TauCeti.exists_isMultiCoupling_isMinOn_lintegral`: a lower semicontinuous cost has an optimal
  multi-coupling.

## References

* B. Pass, *Multi-marginal optimal transport: theory and applications*, ESAIM Math. Model. Numer.
  Anal. 49 (2015), 1771--1790, Section 2, for existence of optimal multi-marginal plans.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]

/-- **The multi-couplings of probability measures are weakly closed.** The multi-coupling set is
the intersection, over the coordinates `i`, of the preimages of `{μ i}` under the weakly continuous
coordinate pushforwards. The `T1Space` hypotheses make these singletons closed. -/
theorem isClosed_setOfPred_isMultiCoupling [∀ i, OpensMeasurableSpace (X i)]
    [OpensMeasurableSpace (∀ i, X i)] [∀ i, T1Space (ProbabilityMeasure (X i))]
    (μ : ∀ i, ProbabilityMeasure (X i)) :
    IsClosed {π : ProbabilityMeasure (∀ i, X i) |
      Measure.IsMultiCoupling π.toMeasure fun i ↦ (μ i).toMeasure} := by
  have h : {π : ProbabilityMeasure (∀ i, X i) |
      Measure.IsMultiCoupling π.toMeasure fun i ↦ (μ i).toMeasure} =
      ⋂ i, (fun π : ProbabilityMeasure (∀ i, X i) ↦ π.map (Function.eval i)) ⁻¹' {μ i} := by
    ext π
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, mem_singleton_iff,
      ← ProbabilityMeasure.toMeasure_injective.eq_iff, ProbabilityMeasure.toMeasure_map]
    exact ⟨fun h ↦ h.marginal_eq, fun h ↦ ⟨h⟩⟩
  rw [h]
  exact isClosed_iInter fun i ↦ isClosed_singleton.preimage
    (ProbabilityMeasure.continuous_map_of_measurable (continuous_apply i)
      (measurable_pi_apply i))

/-- **The multi-couplings of finitely many tight measures form a tight family.** A compact box
`univ.pi K` misses, for every multi-coupling, at most the total mass that the marginals give the
complements of its sides. No hypothesis beyond the topologies is needed. -/
theorem isTightMeasureSet_setOfPred_isMultiCoupling [Finite ι] {μ : ∀ i, Measure (X i)}
    (hμ : ∀ i, IsTightMeasureSet {μ i}) :
    IsTightMeasureSet {π : Measure (∀ i, X i) | Measure.IsMultiCoupling π μ} := by
  have := Fintype.ofFinite ι
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hε' : 0 < ε / Fintype.card ι := ENNReal.div_pos hε.ne' (ENNReal.natCast_ne_top _)
  choose K hK hKμ using fun i ↦
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 (hμ i)) _ hε'
  refine ⟨univ.pi K, isCompact_univ_pi hK, fun π (hπ : Measure.IsMultiCoupling π μ) ↦ ?_⟩
  have hsub : (univ.pi K)ᶜ ⊆ ⋃ i, Function.eval i ⁻¹' (K i)ᶜ := by
    intro x hx
    simpa only [mem_pi, mem_univ, true_implies, not_forall, mem_iUnion, mem_preimage,
      mem_compl_iff, Function.eval] using hx
  calc π (univ.pi K)ᶜ ≤ ∑ i, π (Function.eval i ⁻¹' (K i)ᶜ) :=
        (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _i : ι, ε / Fintype.card ι := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        refine (Measure.le_map_apply (measurable_pi_apply i).aemeasurable _).trans ?_
        rw [hπ.marginal_eq i]
        exact hKμ i _ rfl
    _ ≤ ε := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact ENNReal.mul_div_le

/-- **Prokhorov's theorem for multi-couplings.** The multi-couplings of finitely many tight
probability measures form a weakly compact set: it is tight, hence relatively compact, and
closed. -/
theorem isCompact_setOfPred_isMultiCoupling [Finite ι] [∀ i, OpensMeasurableSpace (X i)]
    [∀ i, T1Space (ProbabilityMeasure (X i))] [BorelSpace (∀ i, X i)] [T2Space (∀ i, X i)]
    {μ : ∀ i, ProbabilityMeasure (X i)} (hμ : ∀ i, IsTightMeasureSet {(μ i).toMeasure}) :
    IsCompact {π : ProbabilityMeasure (∀ i, X i) |
      Measure.IsMultiCoupling π.toMeasure fun i ↦ (μ i).toMeasure} := by
  have htight := isTightMeasureSet_setOfPred_isMultiCoupling hμ
  rw [← (isClosed_setOfPred_isMultiCoupling μ).closure_eq]
  exact isCompact_closure_of_isTightMeasureSet (htight.subset (by rintro - ⟨π, hπ, rfl⟩; exact hπ))

/-- **Existence of an optimal multi-coupling.** For finitely many tight probability measures on
second countable metrizable Borel spaces, for instance Polish spaces, a lower semicontinuous cost
`c : (∀ i, X i) → ℝ≥0∞` attains its infimum over the multi-couplings: some multi-coupling `γ`
satisfies `∫⁻ c ∂γ ≤ ∫⁻ c ∂γ'` for every multi-coupling `γ'`. The minimum may be `∞`. The index
type is nonempty, so that every multi-coupling is a probability measure. -/
theorem exists_isMultiCoupling_isMinOn_lintegral [Finite ι] [Nonempty ι]
    [∀ i, TopologicalSpace.MetrizableSpace (X i)] [∀ i, SecondCountableTopology (X i)]
    [∀ i, BorelSpace (X i)] {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, IsTightMeasureSet {μ i}) {c : (∀ i, X i) → ℝ≥0∞} (hc : LowerSemicontinuous c) :
    ∃ γ : Measure (∀ i, X i), Measure.IsMultiCoupling γ μ ∧
      IsMinOn (fun γ' ↦ ∫⁻ x, c x ∂γ') {γ' | Measure.IsMultiCoupling γ' μ} γ := by
  have := Fintype.ofFinite ι
  -- The direct method `TauCeti.exists_isMinOn_lintegral` runs on a pseudometric space.
  let : PseudoMetricSpace (∀ i, X i) :=
    TopologicalSpace.pseudoMetrizableSpacePseudoMetric (∀ i, X i)
  let μ' : ∀ i, ProbabilityMeasure (X i) := fun i ↦ ⟨μ i, inferInstance⟩
  obtain ⟨γ, hγ, hγmin⟩ := exists_isMinOn_lintegral ⟨_, (MultiCoupling.pi μ').2⟩
    (isCompact_setOfPred_isMultiCoupling (μ := μ') hμ) hc
  refine ⟨γ.toMeasure, hγ, fun γ' (hγ' : Measure.IsMultiCoupling γ' μ) ↦ ?_⟩
  have := hγ'.isProbabilityMeasure (Classical.arbitrary ι)
  exact isMinOn_iff.1 hγmin ⟨γ', inferInstance⟩ hγ'

end TauCeti
