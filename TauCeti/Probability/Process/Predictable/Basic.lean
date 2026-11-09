/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Predictable
public import Mathlib.Topology.Order.Cadlag
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Predictability of left-continuous adapted processes

Left-continuous adapted processes in nonnegative real time are strongly predictable. The proof uses
left endpoint step approximations on countable regular partitions, including the initial value
on the predictable time-zero slice. Continuous paths give a corollary. This supplies predictability
of continuous asset processes and hence of Borel functions of time and those assets.

The time projection is measurable for the predictable sigma-algebra, so deterministic Borel
time dependence can be combined with predictable processes. A predictably measurable function
remains strongly predictable when extended by zero outside a measurable set of times.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal Topology

section Arithmetic

variable {ι Ω E : Type*} {m : MeasurableSpace Ω} [Preorder ι] [OrderBot ι]
  [TopologicalSpace E] {ℱ : Filtration ι m} {H K : ι → Ω → E}

/-- The sum of two strongly predictable processes is strongly predictable. -/
theorem MeasureTheory.IsStronglyPredictable.add [Add E] [ContinuousAdd E]
    (hH : IsStronglyPredictable ℱ H) (hK : IsStronglyPredictable ℱ K) :
    IsStronglyPredictable ℱ (fun t ω ↦ H t ω + K t ω) := by
  -- Uncurrying respects pointwise addition; predictability is strong measurability.
  unfold IsStronglyPredictable at *
  exact hH.add hK

/-- Multiplication by a constant preserves strong predictability. -/
theorem MeasureTheory.IsStronglyPredictable.const_mul [Mul E] [ContinuousMul E]
    (h : IsStronglyPredictable ℱ H) (c : E) :
    IsStronglyPredictable ℱ (fun t ω ↦ c * H t ω) := by
  -- Uncurrying respects pointwise multiplication; predictability is strong measurability.
  unfold IsStronglyPredictable at *
  exact h.const_mul c

end Arithmetic

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

omit [MeasurableSpace E] [BorelSpace E] in
/-- An adapted process with left-continuous sample paths is predictable. -/
theorem MeasureTheory.StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
    {ℱ : Filtration ℝ≥0 m} {u : ℝ≥0 → Ω → E} (hu : StronglyAdapted ℱ u)
    (hc : ∀ ω, IsLeftContinuous (fun s => u s ω)) :
    IsStronglyPredictable ℱ u := by
  borelize E
  have hm (n : ℕ) : StronglyMeasurable[ℱ.predictable]
      (fun p : ℝ≥0 × Ω => u (leftSample n p.1) p.2) := by
    have hs : IsSeparable (⋃ k : ℕ, Set.range (u (k / (n + 1)))) :=
      .iUnion fun k => (hu (k / (n + 1))).isSeparable_range
    refine stronglyMeasurable_iff_measurable_separable.mpr ⟨measurable_leftSample hu n, hs.mono ?_⟩
    rintro _ ⟨p, rfl⟩
    refine Set.mem_iUnion.mpr ⟨⌈p.1 * (n + 1)⌉₊ - 1, ?_⟩
    dsimp only
    rw [leftSample_eq_natCast_div]
    exact Set.mem_range_self p.2
  apply stronglyMeasurable_of_tendsto atTop hm
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

/-- Calendar time is measurable for the predictable sigma-algebra. -/
theorem MeasureTheory.Filtration.measurable_fst_predictable {ι Ω : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [MeasurableSpace ι] [BorelSpace ι]
    (ℱ : Filtration ι m) : Measurable[ℱ.predictable] (Prod.fst : ι × Ω → ι) := by
  apply measurable_of_Ioi
  intro t
  simpa only [Set.prod_univ] using
    measurableSet_predictable_Ioi_prod (𝓕 := ℱ) (i := t) MeasurableSet.univ

/-- The predictable sigma-algebra is contained in the ambient time-product sigma-algebra.
This inclusion allows time-product measures to be trimmed to predictable sets. -/
theorem MeasureTheory.Filtration.predictable_le_prod {ι Ω : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [MeasurableSpace ι]
    [OpensMeasurableSpace ι] [OrderClosedTopology ι] (ℱ : Filtration ι m) :
    ℱ.predictable ≤ (inferInstance : MeasurableSpace ι).prod m := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton _).prod (ℱ.le _ _ hA)
  · intro i A hA
    exact measurableSet_Ioi.prod (ℱ.le _ _ hA)

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
