/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Predictable
public import TauCeti.MeasureTheory.Integral.PiSystem

/-!
# Density of elementary predictable integrands

Initial slices and bounded predictable rectangles generate the predictable sigma-algebra
for a linearly ordered time index with a bottom element and a countable cofinal sequence.
Their indicators have dense real linear span in L² of any finite predictable measure.
If the initial slice is null, bounded rectangles alone suffice. Thus finite sums of bounded
predictable step processes suffice for completion of an elementary stochastic integral.
For nonnegative real time, the measure can be finite-horizon Brownian expected energy
(`dt ⊗ P` restricted to `[0,T] × Ω`) or a finite Doléans measure; no Brownian law or
usual-filtration assumptions are needed.

The proof also gives an integral testing criterion: an integrable predictable function with
zero integral on all elementary sets is zero almost everywhere.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2, elementary predictable processes and completion.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

variable {ι Ω : Type*} [LinearOrder ι] [OrderBot ι] {m : MeasurableSpace Ω}
    (ℱ : Filtration ι m)

/-- Elementary predictable sets are initial slices `{⊥} ×ˢ A` with `A ∈ ℱ ⊥`, and
bounded rectangles `Ioc s t ×ˢ A` with `A ∈ ℱ s`. If `t ≤ s`, the rectangle is empty. -/
def elementarySets : Set (Set (ι × Ω)) :=
  {u | ∃ A, MeasurableSet[ℱ ⊥] A ∧ u = {⊥} ×ˢ A} ∪
    {u | ∃ s t A, MeasurableSet[ℱ s] A ∧ u = Ioc s t ×ˢ A}

/-- Membership in the elementary predictable rectangles, including the initial slice. -/
@[simp]
theorem mem_elementarySets_iff {u : Set (ι × Ω)} :
    u ∈ ℱ.elementarySets ↔
      (∃ A, MeasurableSet[ℱ ⊥] A ∧ u = {⊥} ×ˢ A) ∨
        ∃ s t A, MeasurableSet[ℱ s] A ∧ u = Ioc s t ×ˢ A := Iff.rfl

/-- Every elementary set is predictable. -/
theorem measurableSet_predictable_of_mem_elementarySets {u : Set (ι × Ω)}
    (hu : u ∈ ℱ.elementarySets) : MeasurableSet[ℱ.predictable] u := by
  rcases hu with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · exact measurableSet_predictable_singleton_bot_prod hA
  · exact measurableSet_predictable_Ioc_prod s t hA

/-- Elementary predictable sets form a pi-system. -/
theorem isPiSystem_elementarySets : IsPiSystem ℱ.elementarySets := by
  rintro u (⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩)
    v (⟨B, hB, rfl⟩ | ⟨s', t', B, hB, rfl⟩) hne
  · exact Or.inl ⟨A ∩ B, hA.inter hB, by
      ext p
      simp only [mem_inter_iff, mem_prod, mem_singleton_iff]
      tauto⟩
  · obtain ⟨p, hpA, hpB⟩ := hne
    have hp0 : p.1 = ⊥ := hpA.1
    have hlt := hpB.1.1
    simp [hp0] at hlt
  · obtain ⟨p, hpA, hpB⟩ := hne
    have hp0 : p.1 = ⊥ := hpB.1
    have hlt := hpA.1.1
    simp [hp0] at hlt
  · refine Or.inr ⟨max s s', min t t', A ∩ B,
      (ℱ.mono (le_max_left _ _) _ hA).inter (ℱ.mono (le_max_right _ _) _ hB), ?_⟩
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Ioc, max_lt_iff, le_min_iff]
    tauto

omit [OrderBot ι] in
private theorem iUnion_Ioc_prod_eq_Ioi_prod {u : ℕ → ι}
    (hu : Tendsto u atTop atTop) (s : ι) (A : Set Ω) :
    (⋃ n, Ioc s (u n) ×ˢ A) = Ioi s ×ˢ A := by
  rw [← iUnion_prod_const, iUnion_Ioc_eq_Ioi_self_iff.mpr
    (fun x _ => (hu.eventually (eventually_ge_atTop x)).exists)]

variable [(atTop : Filter ι).IsCountablyGenerated]

/-- A countable subfamily of the elementary predictable sets covers the whole space. -/
theorem isCountablySpanning_elementarySets : IsCountablySpanning ℱ.elementarySets := by
  obtain ⟨u, _, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  let v : ℕ → Set (ι × Ω)
    | 0 => {⊥} ×ˢ univ
    | n + 1 => Ioc ⊥ (u n) ×ˢ univ
  refine ⟨v, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact Or.inl ⟨univ, MeasurableSet.univ, rfl⟩
    | succ n => exact Or.inr ⟨⊥, u n, univ, MeasurableSet.univ, rfl⟩
  · rw [← union_iUnion_nat_succ]
    change ({⊥} ×ˢ univ) ∪ (⋃ n, Ioc ⊥ (u n) ×ˢ univ) = univ
    rw [iUnion_Ioc_prod_eq_Ioi_prod hu]
    ext p
    simp only [mem_union, mem_prod, mem_singleton_iff, mem_univ, and_true,
      mem_Ioi, bot_lt_iff_ne_bot, iff_true]
    exact Classical.em _

/-- Bounded elementary rectangles and the initial slices generate the predictable sigma-algebra. -/
theorem predictable_eq_generateFrom_elementarySets :
    ℱ.predictable = MeasurableSpace.generateFrom ℱ.elementarySets := by
  obtain ⟨u, _, hu⟩ := exists_seq_monotone_tendsto_atTop_atTop ι
  apply le_antisymm
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨A, hA, rfl⟩)
    · intro s A hA
      rw [← iUnion_Ioc_prod_eq_Ioi_prod hu s A]
      exact MeasurableSet.iUnion fun n =>
        MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨s, u n, A, hA, rfl⟩)
  · exact MeasurableSpace.generateFrom_le fun _ hu =>
      ℱ.measurableSet_predictable_of_mem_elementarySets hu

/-- Testing integrals against all elementary predictable sets, including initial slices,
determines an integrable function. -/
theorem ae_eq_zero_of_setIntegral_elementarySets_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : @Measure (ι × Ω) ℱ.predictable) {f : ι × Ω → E}
    (hf : Integrable[ℱ.predictable] f μ)
    (helem : ∀ u ∈ ℱ.elementarySets, ∫ p in u, f p ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  exact TauCeti.ae_eq_zero_of_setIntegral_eq_zero_of_isPiSystem
    ℱ.predictable_eq_generateFrom_elementarySets ℱ.isPiSystem_elementarySets
    ℱ.isCountablySpanning_elementarySets hf helem

/-- Testing integrals against bounded predictable rectangles determines an integrable function,
provided the initial slice has zero measure. -/
theorem ae_eq_zero_of_setIntegral_Ioc_prod_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : @Measure (ι × Ω) ℱ.predictable) {f : ι × Ω → E}
    (hf : Integrable[ℱ.predictable] f μ)
    (hzero : μ ({⊥} ×ˢ (univ : Set Ω)) = 0)
    (hrect : ∀ s t A, MeasurableSet[ℱ s] A → ∫ p in Ioc s t ×ˢ A, f p ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  apply ℱ.ae_eq_zero_of_setIntegral_elementarySets_eq_zero μ hf
  rintro _ (⟨A, _, rfl⟩ | ⟨s, t, A, hA, rfl⟩)
  · exact setIntegral_measure_zero _
      (measure_mono_null (prod_mono_right (subset_univ A)) hzero)
  · exact hrect s t A hA

/-- Indicators of elementary predictable sets have dense real linear span in L² of any
finite predictable measure, whether or not its initial slice is null. -/
theorem topologicalClosure_span_indicatorConstLp_elementarySets_eq_top
    (μ : @Measure (ι × Ω) ℱ.predictable) [@IsFiniteMeasure _ ℱ.predictable μ] :
    letI : MeasurableSpace (ι × Ω) := ℱ.predictable
    (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ (u : Set (ι × Ω)) (hu : u ∈ ℱ.elementarySets),
      g = indicatorConstLp 2 (ℱ.measurableSet_predictable_of_mem_elementarySets hu)
        (measure_ne_top μ _) 1}).topologicalClosure = ⊤ := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  exact TauCeti.topologicalClosure_span_indicatorConstLp_eq_top_of_isPiSystem
    ℱ.predictable_eq_generateFrom_elementarySets ℱ.isPiSystem_elementarySets
    ℱ.isCountablySpanning_elementarySets

/-- Indicators of bounded predictable rectangles have dense real linear span in L² of any
finite predictable measure with no mass at the initial time. -/
theorem topologicalClosure_span_indicatorConstLp_Ioc_prod_eq_top
    (μ : @Measure (ι × Ω) ℱ.predictable) [@IsFiniteMeasure _ ℱ.predictable μ]
    (hzero : μ ({⊥} ×ˢ (univ : Set Ω)) = 0) :
    letI : MeasurableSpace (ι × Ω) := ℱ.predictable
    (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ (s t : ι) (A : Set Ω)
      (hA : MeasurableSet[ℱ s] A),
      g = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
        (measure_ne_top μ _) 1}).topologicalClosure = ⊤ := by
  let : MeasurableSpace (ι × Ω) := ℱ.predictable
  apply top_unique
  rw [← ℱ.topologicalClosure_span_indicatorConstLp_elementarySets_eq_top μ]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro g ⟨u, (⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩), rfl⟩
  · have hz : indicatorConstLp (μ := μ) 2
        (measurableSet_predictable_singleton_bot_prod hA) (measure_ne_top μ _) (1 : ℝ) = 0 := by
      apply norm_eq_zero.mp
      simp [norm_indicatorConstLp, measure_mono_null (prod_mono_right (subset_univ A)) hzero,
        measureReal_def]
    rw [hz]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span ⟨s, t, A, hA, rfl⟩

end MeasureTheory.Filtration
