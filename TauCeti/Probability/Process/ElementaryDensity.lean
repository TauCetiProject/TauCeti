/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Basic
public import TauCeti.MeasureTheory.Function.L2Space

/-!
# Density of elementary predictable integrands

Initial slices and bounded predictable rectangles generate the predictable sigma-algebra
for a linearly ordered time index with a bottom element and a countable cofinal sequence.
Their indicators have dense real linear span in L² of any predictable measure finite on
these elementary sets.
If the initial slice is null, bounded rectangles alone suffice. Thus finite sums of bounded
predictable step processes suffice for completion of an elementary stochastic integral.
For nonnegative real time, the measure can be Brownian expected energy (`dt ⊗ P`),
its finite-horizon restriction, or a Doléans measure finite on elementary sets; no Brownian
law or usual-filtration assumptions are needed.

The proof also gives an integral testing criterion: a predictable function integrable on
each elementary set with zero integral on all elementary sets is zero almost everywhere.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2, elementary predictable processes and completion.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] {m : MeasurableSpace Ω}
    (ℱ : Filtration ι m) [(atTop : Filter ι).IsCountablyGenerated]

/-- Testing integrals against all elementary predictable sets, including initial slices,
determines a function integrable on each elementary set. -/
theorem ae_eq_zero_of_setIntegral_elementarySets_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : @Measure (ι × Ω) ℱ.predictable) {f : ι × Ω → E}
    (hf : ∀ u ∈ ℱ.elementarySets, Integrable[ℱ.predictable] f (μ.restrict u))
    (helem : ∀ u ∈ ℱ.elementarySets, ∫ p in u, f p ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  exact TauCeti.ae_eq_zero_of_setIntegral_eq_zero_of_isPiSystem
    ℱ.predictable_eq_generateFrom_elementarySets ℱ.isPiSystem_elementarySets
    ℱ.isCountablySpanning_elementarySets hf helem

/-- Testing integrals against bounded predictable rectangles determines a function integrable
on each such rectangle, provided the initial slice has zero measure. -/
theorem ae_eq_zero_of_setIntegral_Ioc_prod_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : @Measure (ι × Ω) ℱ.predictable) {f : ι × Ω → E}
    (hf : ∀ s t A, MeasurableSet[ℱ s] A →
      Integrable[ℱ.predictable] f (μ.restrict (Ioc s t ×ˢ A)))
    (hzero : μ ({⊥} ×ˢ (univ : Set Ω)) = 0)
    (hrect : ∀ s t A, MeasurableSet[ℱ s] A → ∫ p in Ioc s t ×ˢ A, f p ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  apply ℱ.ae_eq_zero_of_setIntegral_elementarySets_eq_zero μ
  · intro u hu
    rcases (ℱ.mem_elementarySets_iff.mp hu) with ⟨A, _, rfl⟩ | ⟨s, t, A, hA, rfl⟩
    · exact IntegrableOn.of_measure_zero
        (ℱ.measure_singleton_bot_prod_eq_zero μ hzero A)
    · exact hf s t A hA
  · intro u hu
    rcases (ℱ.mem_elementarySets_iff.mp hu) with ⟨A, _, rfl⟩ | ⟨s, t, A, hA, rfl⟩
    · exact setIntegral_measure_zero _
        (ℱ.measure_singleton_bot_prod_eq_zero μ hzero A)
    · exact hrect s t A hA

/-- Indicators of elementary predictable sets have dense real linear span in L² of any
predictable measure finite on elementary sets, whether or not its initial slice is null. -/
theorem topologicalClosure_span_indicatorConstLp_elementarySets_eq_top
    (μ : @Measure (ι × Ω) ℱ.predictable)
    (hfin : ∀ u ∈ ℱ.elementarySets, μ u ≠ ∞) :
    letI : MeasurableSpace (ι × Ω) := ℱ.predictable
    (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ (u : Set (ι × Ω)) (hu : u ∈ ℱ.elementarySets),
      g = indicatorConstLp 2 (ℱ.measurableSet_predictable_of_mem_elementarySets hu)
        (hfin u hu) 1}).topologicalClosure = ⊤ := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  exact TauCeti.topologicalClosure_span_indicatorConstLp_eq_top_of_isPiSystem
    ℱ.predictable_eq_generateFrom_elementarySets ℱ.isPiSystem_elementarySets
    ℱ.isCountablySpanning_elementarySets hfin

/-- Indicators of bounded predictable rectangles have dense real linear span in L² of any
predictable measure finite on these rectangles with no mass at the initial time. -/
theorem topologicalClosure_span_indicatorConstLp_Ioc_prod_eq_top
    (μ : @Measure (ι × Ω) ℱ.predictable)
    (hfin : ∀ s t A, MeasurableSet[ℱ s] A → μ (Ioc s t ×ˢ A) ≠ ∞)
    (hzero : μ ({⊥} ×ˢ (univ : Set Ω)) = 0) :
    letI : MeasurableSpace (ι × Ω) := ℱ.predictable
    (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ (s t : ι) (A : Set Ω)
      (hA : MeasurableSet[ℱ s] A),
      g = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
        (hfin s t A hA) 1}).topologicalClosure = ⊤ := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  have helem : ∀ u ∈ ℱ.elementarySets, μ u ≠ ∞ := by
    intro u hu
    rcases (ℱ.mem_elementarySets_iff.mp hu) with ⟨A, _, rfl⟩ | ⟨s, t, A, hA, rfl⟩
    · exact (ℱ.measure_singleton_bot_prod_eq_zero μ hzero A).trans_ne
        ENNReal.zero_ne_top
    · exact hfin s t A hA
  apply top_unique
  rw [← ℱ.topologicalClosure_span_indicatorConstLp_elementarySets_eq_top μ helem]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro g ⟨u, hu, rfl⟩
  rcases (ℱ.mem_elementarySets_iff.mp hu) with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · have hz : indicatorConstLp (μ := μ) 2
        (measurableSet_predictable_singleton_bot_prod hA)
        (helem _ (ℱ.singleton_bot_prod_mem_elementarySets hA)) (1 : ℝ) = 0 := by
      apply norm_eq_zero.mp
      simp [norm_indicatorConstLp, ℱ.measure_singleton_bot_prod_eq_zero μ hzero A,
        measureReal_def]
    rw [hz]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨s, t, A, hA, rfl⟩

end MeasureTheory.Filtration
