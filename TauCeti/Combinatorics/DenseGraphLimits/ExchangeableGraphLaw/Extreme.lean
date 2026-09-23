/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.ArrayLaw
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.InfiniteSampling
public import Mathlib.Probability.Kernel.Composition.MeasureComp
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# Extreme exchangeable graph laws

The exchangeable probability measures on the graphs on `ℕ` form a convex set,
`exchangeableGraphProbabilityMeasures`. Its extreme points are the dissociated laws: an
exchangeable law on infinite graphs is an extreme point if and only if its finite law is
dissociated (`mem_extremePoints_iff_isDissociated`). This is the graph-side form of the
characterisation of joint dissociation as extremality among jointly exchangeable array laws, for
callers who work with graph laws; the two convex sets correspond under the graph-law/array-law
adapter (`arrayLaw_mem_iff`, `mem_extremePoints_iff_arrayLaw_mem_extremePoints`).

Two consequences. The infinite sampling law of a graphon is an extreme exchangeable graph measure
(`infiniteSampleLaw_mem_extremePoints`). And a dissociated exchangeable graph law does not mix:
a mixture of exchangeable graph laws equal to it has almost every component equal to it
(`InfiniteExchangeableGraphLaw.ae_eq_of_comp_eq`), the graph counterpart of
`JointlyDissociated.ae_eq_of_comp_eq`; it is the uniqueness input for representing an
exchangeable graph law as a mixture of dissociated ones. Both conclude equality of laws.

## Main results

* `TauCeti.DenseGraphLimits.exchangeableGraphProbabilityMeasures` — the convex set, with its
  membership and convexity lemmas and its identification with the carried array laws through the
  adapter (`arrayLaw_mem_iff`).
* `TauCeti.DenseGraphLimits.mem_extremePoints_iff_isDissociated` — **extremality is
  dissociation** for exchangeable graph laws.
* `TauCeti.DenseGraphLimits.infiniteSampleLaw_mem_extremePoints` — the infinite sampling law of
  a graphon is extreme.
* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw.ae_eq_of_comp_eq` — a dissociated
  exchangeable graph law does not mix.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33–61, Section 5.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open MeasureTheory ProbabilityTheory Set TauCeti.Probability
open scoped ENNReal

namespace TauCeti

namespace DenseGraphLimits

/-- The convex set of exchangeable probability measures on the graphs on `ℕ`. -/
def exchangeableGraphProbabilityMeasures : Set (Measure (SimpleGraph ℕ)) :=
  {μ | (∀ σ : Equiv.Perm ℕ, μ.map (SimpleGraph.comap ⇑σ) = μ) ∧ IsProbabilityMeasure μ}

/-- Membership in the exchangeable probability measures on graphs. -/
@[simp]
theorem mem_exchangeableGraphProbabilityMeasures_iff {μ : Measure (SimpleGraph ℕ)} :
    μ ∈ exchangeableGraphProbabilityMeasures
      ↔ (∀ σ : Equiv.Perm ℕ, μ.map (SimpleGraph.comap ⇑σ) = μ) ∧ IsProbabilityMeasure μ :=
  Iff.rfl

/-- A law on graphs is an exchangeable probability measure exactly when its array law is a
jointly exchangeable probability law carried by the symmetric `false`-diagonal arrays. -/
theorem arrayLaw_mem_iff {μ : Measure (SimpleGraph ℕ)} :
    arrayLaw μ ∈ jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false
      ↔ μ ∈ exchangeableGraphProbabilityMeasures := by
  constructor
  · rintro h
    obtain ⟨hmem, -⟩ :=
      mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.1 h
    obtain ⟨hexch, hp⟩ := mem_jointlyExchangeableProbabilityMeasures_iff.1 hmem
    have hp' : IsProbabilityMeasure μ := by
      constructor
      have := hp.measure_univ
      rwa [arrayLaw_def, Measure.map_apply SimpleGraph.measurable_adjArray MeasurableSet.univ,
        Set.preimage_univ] at this
    refine ⟨fun σ => ?_, hp'⟩
    -- relabelling invariance of `μ` from joint exchangeability of its array law, through the
    -- inverse
    rw [← graphLawOfArray_arrayLaw μ]
    exact map_comap_graphLawOfArray σ (hexch.map_pairReindex σ)
  · rintro ⟨hexch, hp⟩
    exact mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.2
      ⟨mem_jointlyExchangeableProbabilityMeasures_iff.2
        ⟨jointlyExchangeable_arrayLaw hexch, inferInstance⟩,
        arrayLaw_compl_symmetricArraysWithDiag_eq_zero _⟩

/-- The exchangeable probability measures on graphs form a convex set. -/
theorem convex_exchangeableGraphProbabilityMeasures :
    Convex ℝ≥0∞ exchangeableGraphProbabilityMeasures := by
  rintro μ ⟨hμ, hμp⟩ ν ⟨hν, hνp⟩ a b ha hb hab
  have := hμp; have := hνp
  refine ⟨fun σ => ?_, TauCeti.MeasureTheory.isProbabilityMeasure_smul_add_smul hab μ ν⟩
  rw [Measure.map_add _ _ (SimpleGraph.measurable_comap _),
    Measure.map_smul a (SimpleGraph.measurable_comap _).aemeasurable,
    Measure.map_smul b (SimpleGraph.measurable_comap _).aemeasurable, hμ σ, hν σ]

/-- **Extremality transports along the adapter**: a law on graphs is extreme among exchangeable
probability measures exactly when its array law is extreme among the jointly exchangeable laws
carried by the symmetric arrays. The array law and the graph law are mutually inverse affine maps
between the two convex sets. -/
theorem mem_extremePoints_iff_arrayLaw_mem_extremePoints {μ : Measure (SimpleGraph ℕ)} :
    μ ∈ extremePoints ℝ≥0∞ exchangeableGraphProbabilityMeasures ↔
      arrayLaw μ ∈ extremePoints ℝ≥0∞
        (jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag Bool false) := by
  simp only [mem_extremePoints_iff_left]
  constructor
  · rintro ⟨hμ, h⟩
    refine ⟨arrayLaw_mem_iff.2 hμ, ?_⟩
    rintro ρ₁ hρ₁ ρ₂ hρ₂ ⟨a, b, ha, hb, hab, hmix⟩
    -- pull the two ends back to graph laws
    have hs₁ := (mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.1 hρ₁).2
    have hs₂ := (mem_jointlyExchangeableProbabilityMeasuresOnSymmetricArraysWithDiag_iff.1 hρ₂).2
    have e₁ : arrayLaw (graphLawOfArray ρ₁) = ρ₁ := arrayLaw_graphLawOfArray hs₁
    have e₂ : arrayLaw (graphLawOfArray ρ₂) = ρ₂ := arrayLaw_graphLawOfArray hs₂
    have h₁ : graphLawOfArray ρ₁ ∈ exchangeableGraphProbabilityMeasures := by
      rw [← arrayLaw_mem_iff, e₁]; exact hρ₁
    have h₂ : graphLawOfArray ρ₂ ∈ exchangeableGraphProbabilityMeasures := by
      rw [← arrayLaw_mem_iff, e₂]; exact hρ₂
    have hμeq : μ = a • graphLawOfArray ρ₁ + b • graphLawOfArray ρ₂ := by
      rw [← graphLawOfArray_arrayLaw μ, ← hmix, graphLawOfArray_add, graphLawOfArray_smul,
        graphLawOfArray_smul]
    have := h _ h₁ _ h₂ ⟨a, b, ha, hb, hab, hμeq.symm⟩
    rw [← e₁, ← this]
  · rintro ⟨hρ, h⟩
    refine ⟨arrayLaw_mem_iff.1 hρ, ?_⟩
    rintro μ₁ hμ₁ μ₂ hμ₂ ⟨a, b, ha, hb, hab, hmix⟩
    have hmix' : a • arrayLaw μ₁ + b • arrayLaw μ₂ = arrayLaw μ := by
      rw [← hmix, arrayLaw_add, arrayLaw_smul, arrayLaw_smul]
    have := h _ (arrayLaw_mem_iff.2 hμ₁) _ (arrayLaw_mem_iff.2 hμ₂) ⟨a, b, ha, hb, hab, hmix'⟩
    rw [← graphLawOfArray_arrayLaw μ₁, this, graphLawOfArray_arrayLaw]

/-- **Extremality is dissociation**: an exchangeable law on infinite graphs is an extreme point of
the exchangeable probability measures on graphs if and only if its finite law is dissociated. -/
@[simp]
theorem mem_extremePoints_iff_isDissociated (L : InfiniteExchangeableGraphLaw) :
    L.law ∈ extremePoints ℝ≥0∞ exchangeableGraphProbabilityMeasures ↔
      (exchangeableGraphLawEquivInfinite.symm L).IsDissociated := by
  rw [mem_extremePoints_iff_arrayLaw_mem_extremePoints,
    isDissociated_iff_arrayLaw_mem_extremePoints]


/-- The infinite sampling law of a graphon is an extreme exchangeable graph measure. -/
theorem infiniteSampleLaw_mem_extremePoints {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (W : Graphon Ω μ) :
    infiniteSampleLaw W ∈ extremePoints ℝ≥0∞ exchangeableGraphProbabilityMeasures := by
  rw [infiniteSampleLaw_eq_extension, mem_extremePoints_iff_isDissociated,
    Equiv.symm_apply_apply]
  exact isDissociated_sampleExchangeableLaw W

/-- **A dissociated graph law does not mix**: a mixture of exchangeable graph laws equal to a
dissociated exchangeable graph law has almost every component equal to that law. -/
theorem InfiniteExchangeableGraphLaw.ae_eq_of_comp_eq {Z : Type*} [MeasurableSpace Z]
    (L : InfiniteExchangeableGraphLaw)
    (hL : (exchangeableGraphLawEquivInfinite.symm L).IsDissociated)
    {π : Measure Z} {κ : Kernel Z (SimpleGraph ℕ)} [IsMarkovKernel κ]
    (hκ : ∀ᵐ z ∂π, ∀ σ : Equiv.Perm ℕ, (κ z).map (SimpleGraph.comap ⇑σ) = κ z)
    (hmix : κ ∘ₘ π = L.law) : ∀ᵐ z ∂π, κ z = L.law := by
  -- push the mixture through the adjacency array and apply the array theorem
  have hdiss : JointlyDissociated (arrayLaw L.law) fun p x => x p :=
    (isDissociated_iff_jointlyDissociated L).1 hL
  have hκ' : ∀ᵐ z ∂π, JointlyExchangeable ((κ.map SimpleGraph.adjArray) z) fun p x => x p := by
    filter_upwards [hκ] with z hz
    rw [Kernel.map_apply _ SimpleGraph.measurable_adjArray, ← arrayLaw_def]
    exact jointlyExchangeable_arrayLaw hz
  have : IsMarkovKernel (κ.map SimpleGraph.adjArray) :=
    Kernel.IsMarkovKernel.map κ SimpleGraph.measurable_adjArray
  have hmix' : κ.map SimpleGraph.adjArray ∘ₘ π = arrayLaw L.law := by
    rw [← Measure.map_comp _ _ SimpleGraph.measurable_adjArray, hmix, arrayLaw_def]
  have := JointlyDissociated.ae_eq_of_comp_eq hdiss hκ' hmix'
  filter_upwards [this] with z hz
  -- recover equality of graph laws through the inverse identity
  rw [Kernel.map_apply _ SimpleGraph.measurable_adjArray] at hz
  have := congrArg graphLawOfArray hz
  rwa [← arrayLaw_def, graphLawOfArray_arrayLaw, graphLawOfArray_arrayLaw] at this

end DenseGraphLimits

end TauCeti
