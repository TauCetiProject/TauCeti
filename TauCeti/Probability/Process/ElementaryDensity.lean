/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Measure
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
  obtain ⟨v, hv, hcover⟩ := ℱ.isCountablySpanning_elementarySets
  exact TauCeti.ae_eq_zero_of_setIntegral_eq_zero_of_isPiSystem
    ℱ.predictable_eq_generateFrom_elementarySets ℱ.isPiSystem_elementarySets
    v hv hcover (fun n ↦ hf _ (hv n)) helem

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

namespace ContinuousLinearMap

variable {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] {m : MeasurableSpace Ω}
    {ℱ : Filtration ι m} [(atTop : Filter ι).IsCountablyGenerated]
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [T2Space E]

/-- Continuous linear maps on predictable L² agree if they agree on rectangle indicators,
provided the measure is finite on rectangles and has no mass at the initial time. -/
theorem ext_indicatorConstLp_Ioc_prod
    (μ : @Measure (ι × Ω) ℱ.predictable)
    (hfin : ∀ ⦃s t : ι⦄, s < t → ∀ ⦃A : Set Ω⦄, MeasurableSet[ℱ s] A →
      μ (Ioc s t ×ˢ A) ≠ ∞)
    (hzero : μ ({⊥} ×ˢ (univ : Set Ω)) = 0)
    {J K : Lp ℝ 2 μ →L[ℝ] E}
    (h : ∀ ⦃s t : ι⦄ (hst : s < t) ⦃A : Set Ω⦄ (hA : MeasurableSet[ℱ s] A),
      J (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA) (hfin hst hA) 1) =
      K (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA) (hfin hst hA) 1)) :
    J = K := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  have hfin' : ∀ s t A, MeasurableSet[ℱ s] A → μ (Ioc s t ×ˢ A) ≠ ∞ := by
    intro s t A hA
    by_cases hst : s < t
    · exact hfin hst hA
    · simp [Ioc_eq_empty hst]
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (ℱ.topologicalClosure_span_indicatorConstLp_Ioc_prod_eq_top μ hfin' hzero))
  rintro f ⟨s, t, A, hA, rfl⟩
  by_cases hst : s < t
  · exact h hst hA
  · simp [Ioc_eq_empty hst]

/-- For a finite predictable measure with no initial mass or mass after `T`, continuous
linear maps agree if they agree on nonempty rectangle indicators ending at or before `T`. -/
theorem ext_indicatorConstLp_Ioc_prod_of_measure_Ioi_prod_eq_zero
    (μ : @Measure (ι × Ω) ℱ.predictable) [IsFiniteMeasure μ] (T : ι)
    (hzero : μ ({⊥} ×ˢ (univ : Set Ω)) = 0)
    (horizon : μ (Ioi T ×ˢ (univ : Set Ω)) = 0)
    {J K : Lp ℝ 2 μ →L[ℝ] E}
    (h : ∀ ⦃s t : ι⦄, s < t → t ≤ T → ∀ ⦃A : Set Ω⦄ (hA : MeasurableSet[ℱ s] A),
      J (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1) =
      K (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1)) :
    J = K := by
  apply ext_indicatorConstLp_Ioc_prod μ (fun _ _ _ _ _ ↦ measure_ne_top _ _) hzero
  intro s t _ A hA
  have hb : ∀ᵐ p ∂μ, p.1 ≤ T := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp horizon] with p hp
    simpa only [mem_prod, mem_Ioi, mem_univ, and_true, not_lt] using hp
  have heq : indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
      (measure_ne_top μ _) (1 : ℝ) =
      indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s (min t T) hA)
        (measure_ne_top _ _) 1 := by
    apply (indicatorConstLp_inj _ _ _ _ one_ne_zero).mpr
    filter_upwards [hb] with p hp
    simp only [mem_prod, mem_Ioc, le_min_iff, hp, and_true]
  rw [heq]
  by_cases hst : s < min t T
  · exact h hst (min_le_right _ _) hA
  · have hempty : Ioc s (min t T) ×ˢ A = ∅ := by
      simp [Ioc_eq_empty hst]
    simp [hempty]

/-- On finite-horizon predictable L², it suffices to compare continuous linear maps on
nonempty rectangle indicators whose right endpoints lie within the horizon. -/
theorem ext_indicatorConstLp_Ioc_prod_predictableMeasure
    {ℱ : Filtration ℝ≥0 m} {P : Measure Ω} [IsFiniteMeasure P] (T : ℝ≥0)
    {J K : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ] E}
    (h : ∀ ⦃s t : ℝ≥0⦄, s < t → t ≤ T → ∀ ⦃A : Set Ω⦄ (hA : MeasurableSet[ℱ s] A),
      J (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1) =
      K (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1)) :
    J = K := by
  apply ext_indicatorConstLp_Ioc_prod_of_measure_Ioi_prod_eq_zero
    (ℱ.predictableMeasure P T) T
    (ℱ.predictableMeasure_singleton_zero_prod P T MeasurableSet.univ) _ h
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hb := ae_restrict_mem (μ := ℱ.predictableMeasure P T)
    (measurableSet_predictable_Ioc_prod 0 T (𝓕 := ℱ) MeasurableSet.univ)
  rw [ℱ.predictableMeasure_restrict, min_self] at hb
  filter_upwards [hb] with p hp
  exact fun hmem ↦ (not_lt_of_ge hp.1.2) hmem.1

end ContinuousLinearMap
