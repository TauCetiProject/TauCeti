/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import TauCeti.MeasureTheory.Integral.PiSystem

/-!
# Density of elementary predictable integrands

For any finite measure on the predictable sigma-algebra in nonnegative real time which gives
zero mass to time zero, indicators of bounded rectangles `(s,t] × A`, with `A ∈ ℱ s`, have
dense real linear span in L². Thus finite sums of bounded predictable step processes suffice
for completion of an elementary stochastic integral. The measure can be Brownian expected
energy or a finite Doléans measure; no Brownian law or usual-filtration assumptions are needed.

The proof also gives an integral testing criterion: an integrable predictable function with
zero integral on all these rectangles is zero almost everywhere.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  §3.2, elementary predictable processes and completion.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

variable {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 m)

/-- The initial slices and bounded left-predictable rectangles. -/
def elementarySets : Set (Set (ℝ≥0 × Ω)) :=
  {u | ∃ A, MeasurableSet[ℱ 0] A ∧ u = {0} ×ˢ A} ∪
    {u | ∃ s t A, MeasurableSet[ℱ s] A ∧ u = Ioc s t ×ˢ A}

/-- Membership in the elementary predictable rectangles, including the initial slice. -/
@[simp]
theorem mem_elementarySets_iff {u : Set (ℝ≥0 × Ω)} :
    u ∈ ℱ.elementarySets ↔
      (∃ A, MeasurableSet[ℱ 0] A ∧ u = {0} ×ˢ A) ∨
        ∃ s t A, MeasurableSet[ℱ s] A ∧ u = Ioc s t ×ˢ A := Iff.rfl

/-- Every elementary set is predictable. -/
theorem measurableSet_of_mem_elementarySets {u : Set (ℝ≥0 × Ω)}
    (hu : u ∈ ℱ.elementarySets) : MeasurableSet[ℱ.predictable] u := by
  rcases hu with ⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩
  · exact measurableSet_predictable_singleton_bot_prod hA
  · exact measurableSet_predictable_Ioc_prod s t hA

/-- Elementary predictable sets form a pi-system. -/
theorem isPiSystem_elementarySets : IsPiSystem ℱ.elementarySets := by
  rintro u (⟨A, hA, rfl⟩ | ⟨s, t, A, hA, rfl⟩)
    v (⟨B, hB, rfl⟩ | ⟨s', t', B, hB, rfl⟩) hne
  · exact Or.inl ⟨A ∩ B, hA.inter hB, by ext p; simp; tauto⟩
  · obtain ⟨p, hpA, hpB⟩ := hne
    have hp0 : p.1 = 0 := hpA.1
    have hlt := hpB.1.1
    simp [hp0] at hlt
  · obtain ⟨p, hpA, hpB⟩ := hne
    have hp0 : p.1 = 0 := hpB.1
    have hlt := hpA.1.1
    simp [hp0] at hlt
  · refine Or.inr ⟨max s s', min t t', A ∩ B,
      (ℱ.mono (le_max_left _ _) _ hA).inter (ℱ.mono (le_max_right _ _) _ hB), ?_⟩
    ext p
    simp only [mem_inter_iff, mem_prod, mem_Ioc, max_lt_iff, le_min_iff]
    tauto

/-- Bounded elementary rectangles and the initial slices generate the predictable sigma-algebra. -/
theorem predictable_eq_generateFrom_elementarySets :
    ℱ.predictable = MeasurableSpace.generateFrom ℱ.elementarySets := by
  apply le_antisymm
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨A, hA, rfl⟩)
    · intro s A hA
      have he : Ioi s ×ˢ A = ⋃ n : ℕ, Ioc s (n : ℝ≥0) ×ˢ A := by
        rw [← iUnion_prod_const,
          iUnion_Ioc_eq_Ioi_self_iff.mpr (fun x _ => exists_nat_ge x)]
      rw [he]
      exact MeasurableSet.iUnion fun n =>
        MeasurableSpace.measurableSet_generateFrom (Or.inr ⟨s, n, A, hA, rfl⟩)
  · exact MeasurableSpace.generateFrom_le fun _ hu => ℱ.measurableSet_of_mem_elementarySets hu

/-- Testing integrals against bounded predictable rectangles determines an integrable function,
provided the initial slice has zero measure. -/
theorem ae_eq_zero_of_setIntegral_Ioc_prod_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable) {f : ℝ≥0 × Ω → E}
    (hf : Integrable[ℱ.predictable] f μ)
    (hzero : μ ({0} ×ˢ (univ : Set Ω)) = 0)
    (hrect : ∀ s t A, MeasurableSet[ℱ s] A → ∫ p in Ioc s t ×ˢ A, f p ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  have hinit (A : Set Ω) : ∫ p in {0} ×ˢ A, f p ∂μ = 0 := by
    exact setIntegral_measure_zero _ (measure_mono_null (prod_mono_right (subset_univ A)) hzero)
  have htail (s : ℝ≥0) (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
      ∫ p in Ioi s ×ˢ A, f p ∂μ = 0 := by
    have he : (⋃ n : ℕ, Ioc s (n : ℝ≥0) ×ˢ A) = Ioi s ×ˢ A := by
      rw [← iUnion_prod_const,
        iUnion_Ioc_eq_Ioi_self_iff.mpr (fun x _ => exists_nat_ge x)]
    have ht := tendsto_setIntegral_of_monotone
      (fun n : ℕ => measurableSet_predictable_Ioc_prod s n hA)
      (fun i j hij => prod_mono (Ioc_subset_Ioc_right (by exact_mod_cast hij)) le_rfl)
      hf.integrableOn
    rw [he] at ht
    have hz : Tendsto (fun n : ℕ => ∫ p in Ioc s n ×ˢ A, f p ∂μ) atTop (𝓝 0) := by
      simpa only [hrect s _ A hA] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 0))
    exact tendsto_nhds_unique ht hz
  have huniv : ∫ p, f p ∂μ = 0 := by
    have he : ({(0 : ℝ≥0)} ×ˢ (univ : Set Ω)) ∪ (Ioi 0 ×ˢ univ) = univ := by
      ext p
      simp only [mem_union, mem_prod, mem_singleton_iff, mem_univ, and_true, mem_Ioi,
        iff_true]
      have hp : 0 ≤ p.1 := bot_le
      rcases eq_or_lt_of_le hp with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    have hd : Disjoint ({(0 : ℝ≥0)} ×ˢ (univ : Set Ω)) (Ioi 0 ×ˢ univ) := by
      rw [Set.disjoint_left]
      rintro p ⟨hp, _⟩ ⟨hp', _⟩
      exact (lt_irrefl 0) ((mem_singleton_iff.mp hp) ▸ hp')
    have hi := setIntegral_union (μ := μ) (f := f) hd
      (measurableSet_predictable_Ioi_prod (𝓕 := ℱ) (i := (0 : ℝ≥0)) MeasurableSet.univ)
      hf.integrableOn hf.integrableOn
    rw [he, setIntegral_univ, hinit, htail 0 univ MeasurableSet.univ, add_zero] at hi
    exact hi
  apply hf.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro u hu _
  apply TauCeti.setIntegral_eq_zero_of_isPiSystem le_rfl
    ℱ.predictable_eq_generateFrom_elementarySets ℱ.isPiSystem_elementarySets hf huniv ?_ u hu
  rintro _ (⟨A, _, rfl⟩ | ⟨s, t, A, hA, rfl⟩)
  · exact hinit A
  · exact hrect s t A hA

/-- Indicators of bounded predictable rectangles have dense real linear span in L² of any
finite predictable measure with no mass at time zero. -/
theorem topologicalClosure_span_indicatorConstLp_Ioc_prod
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable) [@IsFiniteMeasure _ ℱ.predictable μ]
    (hzero : μ ({0} ×ˢ (univ : Set Ω)) = 0) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    (Submodule.span ℝ {g : Lp ℝ 2 μ | ∃ (s t : ℝ≥0) (A : Set Ω)
      (hA : MeasurableSet[ℱ s] A),
      g = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
        (measure_ne_top μ _) 1}).topologicalClosure = ⊤ := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  rw [← Submodule.orthogonal_eq_bot_iff, Submodule.orthogonal_closure]
  apply bot_unique
  intro f hf
  apply Lp.ext
  have hfi : Integrable f μ := by
    simpa only [integrableOn_univ] using
      integrableOn_Lp_of_measure_ne_top f (by norm_num) (measure_ne_top μ univ)
  refine (ℱ.ae_eq_zero_of_setIntegral_Ioc_prod_eq_zero μ hfi hzero ?_).trans
    (Lp.coeFn_zero ℝ 2 μ).symm
  intro s t A hA
  rw [← L2.inner_indicatorConstLp_one (measurableSet_predictable_Ioc_prod s t hA)
    (measure_ne_top μ _) f]
  exact (Submodule.mem_orthogonal _ f).mp hf _
    (Submodule.subset_span ⟨s, t, A, hA, rfl⟩)

end MeasureTheory.Filtration
