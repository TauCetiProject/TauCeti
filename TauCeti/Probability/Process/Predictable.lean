/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Topology.Order.Cadlag
public import TauCeti.Order.Interval.Set.Prod
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Elementary predictable sets and predictability of adapted processes

Initial slices and bounded predictable rectangles form a pi-system generating the predictable
sigma-algebra when the time index has a bottom element and a countable cofinal sequence.

Left-continuous adapted processes in nonnegative real time are strongly predictable. The proof uses
left endpoint step approximations on countable regular partitions, including the initial value
on the predictable time-zero slice. Continuous paths give a corollary. This supplies predictability
of continuous asset processes and hence of Borel functions of time and those assets.

An adapted process with almost-surely left-continuous paths has a predictable indistinguishable
version, even when the filtration is neither complete nor right-continuous. This does not assert
literal predictability of the original process or everywhere left continuity of the selected
version.

The time projection is measurable for the predictable sigma-algebra, so deterministic Borel
time dependence can be combined with predictable processes. A predictably measurable function
remains strongly predictable when extended by zero outside a measurable set of times.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991,
  Chapter 1, for predictable versions of adapted continuous processes.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal Topology

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

/-- An initial slice measurable at the bottom time is elementary predictable. -/
theorem singleton_bot_prod_mem_elementarySets {A : Set Ω}
    (hA : MeasurableSet[ℱ ⊥] A) : {⊥} ×ˢ A ∈ ℱ.elementarySets :=
  (mem_elementarySets_iff ℱ).mpr (Or.inl ⟨A, hA, rfl⟩)

/-- A bounded rectangle with its spatial set measurable at the left endpoint is
elementary predictable. -/
theorem Ioc_prod_mem_elementarySets (s t : ι) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) : Ioc s t ×ˢ A ∈ ℱ.elementarySets :=
  (mem_elementarySets_iff ℱ).mpr (Or.inr ⟨s, t, A, hA, rfl⟩)

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

/-- If a predictable measure has a null initial slice, every subset slice is null. -/
theorem measure_singleton_bot_prod_eq_zero
    (μ : @Measure (ι × Ω) ℱ.predictable)
    (hzero : μ ({⊥} ×ˢ (univ : Set Ω)) = 0) (A : Set Ω) :
    μ ({⊥} ×ˢ A) = 0 :=
  measure_mono_null (prod_mono_right (subset_univ A)) hzero

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
    | zero => exact ℱ.singleton_bot_prod_mem_elementarySets MeasurableSet.univ
    | succ n => exact ℱ.Ioc_prod_mem_elementarySets ⊥ (u n) MeasurableSet.univ
  · rw [← union_iUnion_nat_succ]
    simp only [v]
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
      exact MeasurableSpace.measurableSet_generateFrom (ℱ.singleton_bot_prod_mem_elementarySets hA)
    · intro s A hA
      rw [← iUnion_Ioc_prod_eq_Ioi_prod hu s A]
      exact MeasurableSet.iUnion fun n =>
        MeasurableSpace.measurableSet_generateFrom (ℱ.Ioc_prod_mem_elementarySets s (u n) hA)
  · exact MeasurableSpace.generateFrom_le fun _ hu =>
      ℱ.measurableSet_predictable_of_mem_elementarySets hu

end MeasureTheory.Filtration

-- Unlike floor sampling on half-open intervals, this samples strictly before every positive
-- time, including partition nodes. The cells are therefore predictable rectangles `(s, t]`.
private noncomputable def leftSample (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  ((⌈t * (n + 1)⌉₊ - 1 : ℕ) : ℝ≥0) / (n + 1)

private lemma leftSample_eq_natCast_div (n : ℕ) (t : ℝ≥0) :
    leftSample n t = ((⌈t * (n + 1)⌉₊ - 1 : ℕ) : ℝ≥0) / (n + 1) := rfl

private lemma leftSample_mem (n : ℕ) {t : ℝ≥0} (ht : 0 < t) :
    t ∈ Ioc (leftSample n t) (leftSample n t + 1 / (n + 1)) := by
  have hn : (0 : ℝ≥0) < n + 1 := by positivity
  have hc : 1 ≤ ⌈t * (n + 1)⌉₊ := Nat.one_le_ceil_iff.mpr (mul_pos ht hn)
  have hh := (Nat.ceil_eq_iff (by omega : ⌈t * (n + 1)⌉₊ ≠ 0)).mp rfl
  constructor
  · exact (div_lt_iff₀ hn).mpr hh.1
  · rw [leftSample, ← add_div, le_div_iff₀ hn]
    have he : ((⌈t * (n + 1)⌉₊ - 1 : ℕ) : ℝ≥0) + 1 = ⌈t * (n + 1)⌉₊ := by
      exact_mod_cast Nat.sub_add_cancel hc
    rw [he]
    exact hh.2

private lemma leftSample_zero (n : ℕ) : leftSample n 0 = 0 := by simp [leftSample]

private lemma leftSample_le (n : ℕ) (t : ℝ≥0) : leftSample n t ≤ t := by
  by_cases ht : t = 0
  · simp [ht, leftSample_zero]
  · exact (leftSample_mem n (pos_iff_ne_zero.mpr ht)).1.le

private lemma leftSample_eq (n k : ℕ) {t : ℝ≥0}
    (ht : t ∈ Ioc ((k : ℝ≥0) / (n + 1)) ((k + 1 : ℕ) / (n + 1))) :
    leftSample n t = k / (n + 1) := by
  have hn : (0 : ℝ≥0) < n + 1 := by positivity
  have hc : ⌈t * (n + 1)⌉₊ = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr
    simpa using And.intro ((div_lt_iff₀ hn).mp ht.1) ((le_div_iff₀ hn).mp ht.2)
  simp [leftSample, hc]

private lemma tendsto_leftSample (t : ℝ≥0) : Tendsto (fun n => leftSample n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlo : Tendsto (fun n : ℕ => (t : ℝ) - 1 / (n + 1)) atTop (𝓝 (t : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
  · intro n
    by_cases ht : t = 0
    · simp only [ht, leftSample_zero, NNReal.coe_zero, zero_sub, neg_nonpos]
      positivity
    · have h := (leftSample_mem n (pos_iff_ne_zero.mpr ht)).2
      exact sub_le_iff_le_add.mpr (by exact_mod_cast h)
  · intro n
    exact_mod_cast leftSample_le n t

variable {Ω E : Type*} {m : MeasurableSpace Ω} [TopologicalSpace E]
  [PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E]

private lemma measurable_leftSample {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E}
    (hu : StronglyAdapted ℱ u) (n : ℕ) :
    Measurable[ℱ.predictable] (fun p : ℝ≥0 × Ω => u (leftSample n p.1) p.2) := by
  intro A hA
  have he : (fun p : ℝ≥0 × Ω => u (leftSample n p.1) p.2) ⁻¹' A =
      ({0} ×ˢ (u 0 ⁻¹' A)) ∪ ⋃ k : ℕ,
        Ioc ((k : ℝ≥0) / (n + 1)) ((k + 1 : ℕ) / (n + 1)) ×ˢ
          (u (k / (n + 1)) ⁻¹' A) := by
    ext p
    simp only [mem_preimage, mem_union, mem_prod, mem_singleton_iff, mem_iUnion]
    constructor
    · intro hp
      by_cases ht : p.1 = 0
      · exact Or.inl ⟨ht, by simpa [ht, leftSample_zero] using hp⟩
      · refine Or.inr ⟨⌈p.1 * (n + 1)⌉₊ - 1, ?_, ?_⟩
        · have h := leftSample_mem n (pos_iff_ne_zero.mpr ht)
          convert h using 1
          simp only [leftSample_eq_natCast_div, Nat.cast_add, Nat.cast_one, add_div, one_div]
        · simpa only [leftSample_eq_natCast_div] using hp
    · rintro (⟨ht, hp⟩ | ⟨k, ht, hp⟩)
      · simpa [ht, leftSample_zero] using hp
      · simpa only [leftSample_eq n k ht] using hp
  rw [he]
  exact (measurableSet_predictable_singleton_bot_prod ((hu 0).measurable hA)).union
    (.iUnion fun k => measurableSet_predictable_Ioc_prod _ _ ((hu _).measurable hA))

private lemma stronglyMeasurable_leftSample {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E}
    (hu : StronglyAdapted ℱ u) (n : ℕ) :
    StronglyMeasurable[ℱ.predictable] (fun p : ℝ≥0 × Ω => u (leftSample n p.1) p.2) := by
  have hs : IsSeparable (⋃ k : ℕ, Set.range (u (k / (n + 1)))) :=
    .iUnion fun k => (hu (k / (n + 1))).isSeparable_range
  refine stronglyMeasurable_iff_measurable_separable.mpr ⟨measurable_leftSample hu n, hs.mono ?_⟩
  rintro _ ⟨p, rfl⟩
  refine Set.mem_iUnion.mpr ⟨⌈p.1 * (n + 1)⌉₊ - 1, ?_⟩
  dsimp only
  rw [leftSample_eq_natCast_div]
  exact Set.mem_range_self p.2

omit [MeasurableSpace E] [BorelSpace E] in
/-- An adapted process with left-continuous sample paths is predictable. -/
theorem MeasureTheory.StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
    {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E} (hu : StronglyAdapted ℱ u)
    (hc : ∀ ω, IsLeftContinuous (fun s => u s ω)) :
    IsStronglyPredictable ℱ u := by
  borelize E
  apply stronglyMeasurable_of_tendsto atTop (stronglyMeasurable_leftSample hu)
  apply tendsto_pi_nhds.mpr
  intro p
  apply (continuousWithinAt_Iio_iff_Iic.mp (hc p.2 p.1)).tendsto.comp
  refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_leftSample p.1, .of_forall fun n => ?_⟩
  exact leftSample_le n p.1

omit [MeasurableSpace E] [BorelSpace E] in
/-- An adapted process with continuous sample paths is predictable. -/
theorem MeasureTheory.StronglyAdapted.isStronglyPredictable_of_continuous
    {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E} (hu : StronglyAdapted ℱ u)
    (hc : ∀ ω, Continuous (fun t => u t ω)) : IsStronglyPredictable ℱ u :=
  hu.isStronglyPredictable_of_isLeftContinuous fun ω => (hc ω).isLeftContinuous

omit [MeasurableSpace E] [BorelSpace E] in
/-- An adapted process with almost-surely left-continuous paths has a predictable
indistinguishable version on the same raw filtration. No completeness or right continuity of
the filtration is required. The selected version need not be left-continuous on exceptional
paths. -/
theorem MeasureTheory.StronglyAdapted.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
    [Nonempty E] [IsCompletelyMetrizableSpace E]
    {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E} {P : Measure Ω}
    (hu : StronglyAdapted ℱ u) (hc : ∀ᵐ ω ∂P, IsLeftContinuous (fun t => u t ω)) :
    ∃ v : ℝ≥0 → Ω → E, IsStronglyPredictable ℱ v ∧ v ≡ᵐ[P] u := by
  borelize E
  let v t ω := limUnder atTop (fun n => u (leftSample n t) ω)
  refine ⟨v, ?_, ?_⟩
  · let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    exact StronglyMeasurable.limUnder (stronglyMeasurable_leftSample hu)
  · filter_upwards [hc] with ω hω
    intro t
    exact ((continuousWithinAt_Iio_iff_Iic.mp (hω t)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨tendsto_leftSample t, .of_forall fun n => leftSample_le n t⟩)).limUnder_eq

/-- Calendar time is measurable for the predictable sigma-algebra. -/
theorem MeasureTheory.Filtration.measurable_fst_predictable {ι Ω : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    (ℱ : Filtration ι m) : Measurable[ℱ.predictable] (Prod.fst : ι × Ω → ι) := by
  apply measurable_of_Ioi
  intro t
  simpa only [Set.prod_univ] using
    measurableSet_predictable_Ioi_prod (𝓕 := ℱ) (i := t) MeasurableSet.univ

/-- A predictably measurable function, extended by zero outside a measurable set of times,
defines a strongly predictable process. In particular, the time predicate can impose a
deterministic maturity cutoff without any continuity assumption at maturity. -/
theorem Measurable.isStronglyPredictable_ite_zero {ι Ω E : Type*}
    {m : MeasurableSpace Ω} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι]
    [OrderTopology ι] [SecondCountableTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    [TopologicalSpace E] [PseudoMetrizableSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [Zero E]
    {ℱ : Filtration ι m} {f : ι × Ω → E} (hf : Measurable[ℱ.predictable] f)
    {P : ι → Prop} [DecidablePred P] (hP : MeasurableSet {t | P t}) :
    IsStronglyPredictable ℱ (fun t ω => if P t then f (t, ω) else 0) :=
  (hf.ite (hP.preimage ℱ.measurable_fst_predictable) measurable_const).stronglyMeasurable
