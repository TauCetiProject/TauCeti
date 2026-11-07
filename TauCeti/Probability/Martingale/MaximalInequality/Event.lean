/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.MaximalInequality.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IsLUB

/-!
# Event-refined maximal inequalities

For a nonnegative submartingale, Doob's maximal inequality retains the crossing event in the
terminal expectation. This refinement, unlike the weak bound by the whole terminal expectation,
can be integrated over the threshold to obtain strong maximal estimates for stochastic-integral
approximation.

We prove the refinement on countable sets of times and, for almost surely right-continuous
paths, at all times up to a fixed terminal time. No usual-filtration assumption is needed.
Uncountable crossing events are interpreted using outer measure and restricted integrals;
right continuity identifies them almost everywhere with countable measurable crossing events.
The finite-set input is `Submartingale.mul_measure_exists_mem_le_le_setIntegral`, which uses
Mathlib's `maximal_ineq` without dropping its terminal event indicator.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 1.3.8.
-/

public section
noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ} [IsFiniteMeasure μ]

/-- **Event-refined Doob inequality on a countable set.** Sampling need not include the
terminal time; the expectation is restricted to exactly the sampled crossing event. -/
theorem mul_measure_exists_mem_le_le_setIntegral_of_countable
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) (ε : ℝ≥0)
    {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T) :
    ε * μ {ω | ∃ t ∈ S, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ S, (ε : ℝ) ≤ f t ω}, f T ω ∂μ) := by
  classical
  have := hS.to_subtype
  let A : Finset S → Set Ω := fun F ↦ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}
  have hdir : Directed (· ⊆ ·) A := fun F G ↦ ⟨F ∪ G,
    fun _ ⟨t, ht, h⟩ ↦ ⟨t, Finset.mem_union_left _ ht, h⟩,
    fun _ ⟨t, ht, h⟩ ↦ ⟨t, Finset.mem_union_right _ ht, h⟩⟩
  have hUnion : (⋃ F, A F) = {ω | ∃ t ∈ S, (ε : ℝ) ≤ f t ω} := by
    ext ω
    constructor
    · intro h
      obtain ⟨F, t, ht, h⟩ := mem_iUnion.1 h
      exact ⟨t, t.2, h⟩
    · rintro ⟨t, ht, h⟩
      exact mem_iUnion.2 ⟨{⟨t, ht⟩}, ⟨t, ht⟩, Finset.mem_singleton_self _, h⟩
  rw [← hUnion, hdir.measure_iUnion, ENNReal.mul_iSup]
  apply iSup_le
  intro F
  have hbound := hf.mul_measure_exists_mem_le_le_setIntegral hnonneg ε
    (F := F.map (Function.Embedding.subtype _)) (T := T) (by
      intro t ht
      obtain ⟨⟨t, htS⟩, _, rfl⟩ := Finset.mem_map.1 ht
      exact hST t htS)
  have hset : {ω | ∃ t ∈ F.map (Function.Embedding.subtype _), (ε : ℝ) ≤ f t ω} = A F := by
    ext ω
    simp [A]
  rw [hset] at hbound
  refine hbound.trans (ENNReal.ofReal_le_ofReal (setIntegral_mono_set
    (hf.integrable T).integrableOn (Eventually.of_forall (fun _ ↦ hnonneg T _)) ?_))
  exact Eventually.of_forall (subset_iUnion A F)

/-- The event-refined Doob inequality also holds for strict crossings on a countable set. -/
theorem mul_measure_exists_mem_lt_le_setIntegral_of_countable
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) (ε : ℝ≥0)
    {S : Set ι} (hS : S.Countable) {T : ι} (hST : ∀ t ∈ S, t ≤ T) :
    ε * μ {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ S, (ε : ℝ) < f t ω}, f T ω ∂μ) := by
  obtain ⟨δ, hδanti, hδlt, hδlim⟩ := exists_seq_strictAnti_tendsto ε
  let A : ℕ → Set Ω := fun n ↦ {ω | ∃ t ∈ S, (δ n : ℝ) ≤ f t ω}
  have hmono : Monotone A := by
    intro i j hij ω ⟨t, ht, h⟩
    refine ⟨t, ht, le_trans ?_ h⟩
    exact_mod_cast hδanti.antitone hij
  have hsub (n : ℕ) : A n ⊆ {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} := by
    rintro ω ⟨t, ht, h⟩
    have hn : (ε : ℝ) < δ n := hδlt n
    exact ⟨t, ht, hn.trans_le h⟩
  have hUnion : (⋃ n, A n) = {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} := by
    apply Subset.antisymm (iUnion_subset hsub)
    rintro ω ⟨t, ht, h⟩
    obtain ⟨n, hn⟩ := ((NNReal.tendsto_coe.2 hδlim).eventually (Iio_mem_nhds h)).exists
    exact mem_iUnion.2 ⟨n, t, ht, hn.le⟩
  rw [← hUnion, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun n ↦ ?_
  calc ε * μ (A n) ≤ δ n * μ (A n) := by gcongr; exact (hδlt n).le
    _ ≤ ENNReal.ofReal (∫ ω in A n, f T ω ∂μ) :=
      hf.mul_measure_exists_mem_le_le_setIntegral_of_countable hnonneg (δ n) hS hST
    _ ≤ _ := ENNReal.ofReal_le_ofReal (setIntegral_mono_set
      (hf.integrable T).integrableOn (Eventually.of_forall (fun _ ↦ hnonneg T _))
      (Eventually.of_forall (by rw [hUnion]; exact hsub n)))

/-- **Event-refined Doob inequality in continuous time.** Almost surely right-continuous paths
allow all times before the terminal time, retaining the same strict crossing event in the
terminal expectation. The measure need not be complete and the filtration need not be usual. -/
theorem mul_measure_exists_le_lt_le_setIntegral
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    [TopologicalSpace.SeparableSpace ι]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (ε : ℝ≥0) :
    ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ≤ T, (ε : ℝ) < f t ω}, f T ω ∂μ) := by
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt (α := ℝ) T
  have heq : {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} =ᵐ[μ]
      {ω | ∃ t ∈ S, (ε : ℝ) < f t ω} := by
    filter_upwards [hcont] with ω hω
    exact propext ⟨fun ⟨t, ht, h⟩ ↦ by
      obtain ⟨s, hs, hεs⟩ := hS hω ht h
      exact ⟨s, hs, hεs⟩,
      fun ⟨t, ht, h⟩ ↦ ⟨t, hST ht, h⟩⟩
  rw [measure_congr heq, setIntegral_congr_set heq]
  exact hf.mul_measure_exists_mem_lt_le_setIntegral_of_countable hnonneg ε hSc
    (fun _ ht ↦ hST ht)

/-- **Closed-level event-refined Doob inequality.** The running supremum is taken in `ℝ≥0∞`,
so no pathwise boundedness assumption or convention for an unattained real supremum is needed.
The terminal expectation retains exactly the event that this supremum is at least `ε`. -/
theorem mul_measure_le_iSup_le_setIntegral
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]
    [TopologicalSpace.SeparableSpace ι]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t)
    (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ≥0∞) ≤ ⨆ t ≤ T, ENNReal.ofReal (f t ω)},
        f T ω ∂μ) := by
  by_cases hε : ε = 0
  · simp [hε]
  obtain ⟨δ, hδmono, hδmem, hδlim⟩ := exists_seq_strictMono_tendsto' (pos_iff_ne_zero.2 hε)
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal (f t ω)
  let A : ℕ → Set Ω := fun n ↦ {ω | (δ n : ℝ≥0∞) < Y ω}
  have hY : AEMeasurable Y μ := aemeasurable_iSup_le_ofReal
    (fun t ↦ ((hf.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl).aemeasurable) hcont
  have hA (n : ℕ) : NullMeasurableSet (A n) μ := nullMeasurableSet_lt aemeasurable_const hY
  have hanti : Antitone A := by
    intro i j hij ω h
    have hij' : (δ i : ℝ≥0∞) ≤ δ j := by exact_mod_cast hδmono.monotone hij
    exact hij'.trans_lt h
  have hδlim' : Tendsto (fun n ↦ (δ n : ℝ≥0∞)) atTop (𝓝 (ε : ℝ≥0∞)) :=
    ENNReal.continuous_coe.tendsto ε |>.comp hδlim
  have hInter : (⋂ n, A n) = {ω | (ε : ℝ≥0∞) ≤ Y ω} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq, A]
    exact ⟨fun h ↦ le_of_tendsto' hδlim' (fun n ↦ (h n).le),
      fun h n ↦ lt_of_lt_of_le (by exact_mod_cast (hδmem n).2) h⟩
  -- Decreasing crossing events converge in measure and under the terminal expectation.
  have hmeasure := tendsto_measure_iInter_atTop hA hanti ⟨0, measure_ne_top _ _⟩
  have hint := tendsto_integral_of_dominated_convergence (fun ω ↦ ‖f T ω‖)
    (fun n ↦ (hf.integrable T).aestronglyMeasurable.indicator₀ (hA n)) (hf.integrable T).norm
    (fun n ↦ Eventually.of_forall (fun ω ↦ norm_indicator_le_norm_self (f T) ω))
    (Eventually.of_forall (fun ω ↦ (hanti.tendsto_indicator _ _ _).trans (pure_le_nhds _)))
  simp_rw [integral_indicator₀ (hA _)] at hint
  rw [integral_indicator₀ (NullMeasurableSet.iInter hA)] at hint
  have hbound (n : ℕ) : δ n * μ (A n) ≤ ENNReal.ofReal (∫ ω in A n, f T ω ∂μ) := by
    have hset : A n = {ω | ∃ t ≤ T, (δ n : ℝ) < f t ω} := by
      ext ω
      simp [A, Y, lt_iSup_iff, ENNReal.coe_lt_ofReal]
    rw [hset]
    exact hf.mul_measure_exists_le_lt_le_setIntegral hnonneg hcont (δ n)
  have h := le_of_tendsto_of_tendsto'
    (ENNReal.Tendsto.mul hδlim' (Or.inr (measure_ne_top _ _)) hmeasure
      (Or.inr ENNReal.coe_ne_top)) (ENNReal.tendsto_ofReal hint) hbound
  simpa only [hInter] using h

end MeasureTheory.Submartingale
