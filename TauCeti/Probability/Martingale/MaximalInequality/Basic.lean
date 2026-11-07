/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Analysis.SpecificLimits.Basic
public import TauCeti.Topology.Algebra.InfiniteSum.ENNReal
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RightContinuous

/-!
# Doob's maximal inequality over finite and countable sets and in continuous time

Mathlib's `MeasureTheory.maximal_ineq` is Doob's maximal inequality for a nonnegative submartingale
indexed by `ℕ`. This file transfers it to a general linearly ordered time set. For a nonnegative
submartingale `f`, a time `T` and `ε : ℝ≥0`:

* over any finite or countable set `F` of times `≤ T`,
  `ε P(∃ t ∈ F, ε ≤ f_t) ≤ E[f_T 1_{∃ t ∈ F, ε ≤ f_t}] ≤ E[f_T]`;
* if every path is right-continuous before `T` (almost surely), and the time set is densely ordered
  and separable (for instance `ℝ≥0`), `ε P(∃ t ≤ T, ε < f_t) ≤ E[f_T]`.

The event `{∃ t ≤ T, ε < f_t}` need not be measurable; `P` is applied to it as an outer measure.
Under the same right-continuity hypothesis the running maximum `sup_{t ≤ T} f_t` is almost
everywhere measurable (`MeasureTheory.aemeasurable_iSup_le_ofReal`).

A weak-type bound of this kind controls the running maximum in every `Lᵖ` with `p < 1`. The file
records the case `p = 1 / 2`, `E[sup_{t ≤ T} √f_t] ≤ P(Ω) + 4 E[f_T]`. Applied to `f = g²`, it
bounds the expected running maximum of a nonnegative process `g` whose square is a submartingale;
this is how the running maximum of an exponential martingale is shown to be integrable.

## Main declarations

* `MeasureTheory.Submartingale.mul_measure_exists_mem_le_le_setIntegral`: the finite-set
  inequality retaining the crossing event in the terminal expectation.
* `MeasureTheory.Submartingale.mul_measure_exists_mem_le_le`: the maximal inequality over a finite
  set of times.
* `MeasureTheory.Submartingale.mul_measure_exists_mem_le_le_setIntegral_of_countable`: the
  event-refined inequality over a countable set of times.
* `MeasureTheory.Submartingale.mul_measure_exists_le_lt_le_setIntegral`: the event-refined
  inequality over all times `t ≤ T`, for right-continuous paths.
* `MeasureTheory.Submartingale.mul_measure_exists_le_lt_le`: the maximal inequality over all times
  `t ≤ T`, for right-continuous paths.
* `MeasureTheory.Submartingale.lintegral_iSup_sqrt_le`: the bound on `E[sup_{t ≤ T} √f_t]`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991,
  Theorem 1.3.8.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, Springer, 1999,
  Theorem II.1.7.
-/

public section

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace MeasureTheory.Submartingale

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [LinearOrder ι]
  {ℱ : Filtration ι m0} {f : ι → Ω → ℝ}

/-- **Event-refined Doob inequality on a finite set.** The terminal expectation is restricted
to the same crossing event, even when the terminal time does not belong to the sampled set. -/
theorem mul_measure_exists_mem_le_le_setIntegral [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) (ε : ℝ≥0) {F : Finset ι} {T : ι}
    (hF : ∀ t ∈ F, t ≤ T) :
    ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤
      ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, f T ω ∂μ) := by
  classical
  obtain hEmpty | hne := F.eq_empty_or_nonempty
  · simp [hEmpty]
  -- Sample exactly F, not F ∪ {T}: adding T would enlarge the event on the right.
  set n := F.card - 1
  have hcard : F.card = n + 1 := (Nat.sub_add_cancel hne.card_pos).symm
  let e := F.orderEmbOfFin hcard
  let τ : ℕ → ι := fun j ↦ e ⟨min j n, by omega⟩
  have hτ : Monotone τ := fun i j hij ↦ e.monotone (Fin.mk_le_mk.2 (min_le_min_right _ hij))
  have hmem (j : ℕ) : τ j ∈ F := F.orderEmbOfFin_mem hcard _
  have hτn : τ n = F.max' hne := by
    simpa [τ, e] using Finset.orderEmbOfFin_last hcard (Nat.succ_pos n)
  let 𝒢 : Filtration ℕ m0 := ⟨fun j ↦ ℱ (τ j), fun _ _ hij ↦ ℱ.mono (hτ hij), fun _ ↦ ℱ.le _⟩
  have hg : Submartingale (fun j ↦ f (τ j)) 𝒢 μ :=
    ⟨fun j ↦ hf.stronglyAdapted (τ j), fun _ _ hij ↦ hf.ae_le_condExp (hτ hij),
      fun j ↦ hf.integrable (τ j)⟩
  have hset : {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} = {ω | (ε : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k ↦ f (τ k) ω} := by
    ext ω
    simp only [mem_ofPred_eq, Finset.le_sup'_iff]
    constructor
    · rintro ⟨t, ht, hεt⟩
      obtain ⟨i, rfl⟩ : t ∈ range e := by
        rw [Finset.range_orderEmbOfFin]
        exact ht
      exact ⟨i, Finset.mem_range.2 i.2, by simpa [τ, min_eq_left (by omega : (i : ℕ) ≤ n)]⟩
    · rintro ⟨j, hj, hεj⟩
      exact ⟨τ j, hmem j, hεj⟩
  have hmeas : MeasurableSet[ℱ (τ n)] {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} := by
    simp only [← exists_prop, ofPred_exists]
    apply F.measurableSet_biUnion
    intro t ht
    exact measurableSet_le measurable_const
      (((hf.stronglyAdapted t).mono (ℱ.mono (by rw [hτn]; exact F.le_max' t ht))).measurable)
  calc ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}
      ≤ ENNReal.ofReal (∫ ω in {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω}, f (τ n) ω ∂μ) := by
        rw [hset]
        exact maximal_ineq hg (fun _ ↦ hnonneg _) n
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hf.setIntegral_le (hF _ (hmem n)) hmeas)

/-- **Doob's maximal inequality over a finite set of times.** For a nonnegative submartingale `f`
and a finite set `F` of times `≤ T`, `ε P(∃ t ∈ F, ε ≤ f_t) ≤ E[f_T]`. -/
theorem mul_measure_exists_mem_le_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hnonneg : 0 ≤ f) (ε : ℝ≥0) {F : Finset ι} {T : ι} (hF : ∀ t ∈ F, t ≤ T) :
    ε * μ {ω | ∃ t ∈ F, (ε : ℝ) ≤ f t ω} ≤ ENNReal.ofReal (∫ ω, f T ω ∂μ) :=
  (hf.mul_measure_exists_mem_le_le_setIntegral hnonneg ε hF).trans
    (ENNReal.ofReal_le_ofReal
      (setIntegral_le_integral (hf.integrable T) (Eventually.of_forall (hnonneg T))))

/-- **Event-refined Doob inequality on a countable set.** Sampling need not include the
terminal time; the expectation is restricted to exactly the sampled crossing event. -/
theorem mul_measure_exists_mem_le_le_setIntegral_of_countable [IsFiniteMeasure μ]
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
theorem mul_measure_exists_mem_lt_le_setIntegral_of_countable [IsFiniteMeasure μ]
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

section ContinuousTime

variable [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι]

/-- **Event-refined Doob inequality in continuous time.** Almost surely right-continuous paths
allow all times before the terminal time, retaining the same strict crossing event in the
terminal expectation. The measure need not be complete and the filtration need not be usual. -/
theorem mul_measure_exists_le_lt_le_setIntegral
    [TopologicalSpace.SeparableSpace ι] [IsFiniteMeasure μ]
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

/-- **Doob's maximal inequality in continuous time.** Let `f` be a nonnegative submartingale
indexed by a densely ordered separable time set, such as `ℝ≥0`, whose paths are almost surely
right-continuous at every time before `T`. Then `ε P(∃ t ≤ T, ε < f_t) ≤ E[f_T]`. -/
theorem mul_measure_exists_le_lt_le [TopologicalSpace.SeparableSpace ι] [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) (ε : ℝ≥0) :
    ε * μ {ω | ∃ t ≤ T, (ε : ℝ) < f t ω} ≤ ENNReal.ofReal (∫ ω, f T ω ∂μ) :=
  (hf.mul_measure_exists_le_lt_le_setIntegral hnonneg hcont ε).trans
    (ENNReal.ofReal_le_ofReal
      (setIntegral_le_integral (hf.integrable T) (Eventually.of_forall (hnonneg T))))

/-- **The running maximum of the square root of a submartingale is integrable.** For a
nonnegative submartingale `f` whose paths are almost surely right-continuous before `T`,
`E[sup_{t ≤ T} √f_t] ≤ P(Ω) + 4 E[f_T]`. The integrand is almost everywhere measurable by
`MeasureTheory.aemeasurable_iSup_le_ofReal`. -/
theorem lintegral_iSup_sqrt_le [TopologicalSpace.SeparableSpace ι] [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hnonneg : 0 ≤ f) {T : ι}
    (hcont : ∀ᵐ ω ∂μ, ∀ t < T, ContinuousWithinAt (fun u ↦ f u ω) (Ioi t) t) :
    ∫⁻ ω, ⨆ t ≤ T, ENNReal.ofReal √(f t ω) ∂μ ≤
      μ univ + 4 * ENNReal.ofReal (∫ ω, f T ω ∂μ) := by
  set Y : Ω → ℝ≥0∞ := fun ω ↦ ⨆ t ≤ T, ENNReal.ofReal √(f t ω)
  set E := ENNReal.ofReal (∫ ω, f T ω ∂μ)
  -- The level sets `{2^k < Y} = {∃ t ≤ T, 4^k < f_t}` have measure at most `E / 4^k`.
  have hlevel : ∀ k : ℕ, (2 : ℝ≥0∞) ^ (k + 1) * μ {ω | 2 ^ k < Y ω} ≤ 2 * 2⁻¹ ^ k * E := by
    intro k
    -- `2^k = √(4^k)`, read in `ℝ≥0∞`.
    have hsqrt : (2 : ℝ≥0∞) ^ k = ENNReal.ofReal √((4 ^ k : ℝ≥0) : ℝ) := by
      have : √((4 ^ k : ℝ≥0) : ℝ) = 2 ^ k := by
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity), ← mul_pow]
        norm_num
      rw [this, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
    have hset : {ω | 2 ^ k < Y ω} = {ω | ∃ t ≤ T, ((4 ^ k : ℝ≥0) : ℝ) < f t ω} := by
      ext ω
      simp only [Y, mem_ofPred_eq, lt_iSup_iff, exists_prop, hsqrt,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _),
        Real.sqrt_lt_sqrt_iff (NNReal.coe_nonneg _)]
    have hmax := hf.mul_measure_exists_le_lt_le hnonneg hcont (4 ^ k)
    rw [← hset] at hmax
    -- `2^(k+1) = 2 · 2⁻ᵏ · 4^k`, since `2⁻ᵏ · 2ᵏ = 1` and `4^k = 2^k · 2^k`.
    have hinv : (2 : ℝ≥0∞)⁻¹ ^ k * 2 ^ k = 1 := by
      rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    have h4 : ((4 ^ k : ℝ≥0) : ℝ≥0∞) = 2 ^ k * 2 ^ k := by
      push_cast
      rw [← mul_pow]
      norm_num
    have hpow : (2 : ℝ≥0∞) ^ (k + 1) = 2 * 2⁻¹ ^ k * ((4 ^ k : ℝ≥0) : ℝ≥0∞) :=
      calc (2 : ℝ≥0∞) ^ (k + 1) = 2 * (2⁻¹ ^ k * 2 ^ k) * 2 ^ k := by rw [hinv]; ring
        _ = 2 * 2⁻¹ ^ k * ((4 ^ k : ℝ≥0) : ℝ≥0∞) := by rw [h4]; ring
    rw [hpow, mul_assoc]
    gcongr
  -- Replace the level sets by measurable supersets of the same measure.
  set B : ℕ → Set Ω := fun k ↦ toMeasurable μ {ω | 2 ^ k < Y ω}
  calc ∫⁻ ω, Y ω ∂μ
      ≤ ∫⁻ ω, 1 + ∑' k : ℕ, (B k).indicator (fun _ ↦ (2 : ℝ≥0∞) ^ (k + 1)) ω ∂μ := by
        refine lintegral_mono fun ω ↦ (ENNReal.le_one_add_tsum_pow_indicator (Y ω)).trans ?_
        gcongr with k
        split_ifs with h
        · rw [indicator_of_mem (subset_toMeasurable μ _ h)]
        · exact bot_le
    _ = μ univ + ∑' k : ℕ, 2 ^ (k + 1) * μ {ω | 2 ^ k < Y ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
          lintegral_tsum fun k ↦ (measurable_const.indicator
            (measurableSet_toMeasurable _ _)).aemeasurable]
        simp_rw [lintegral_indicator_const (measurableSet_toMeasurable _ _),
          measure_toMeasurable]
    _ ≤ μ univ + ∑' k : ℕ, 2 * 2⁻¹ ^ k * E := add_le_add le_rfl (tsum_le_tsum hlevel)
    _ = μ univ + 4 * E := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
          ENNReal.one_sub_inv_two, inv_inv]
        norm_num

end ContinuousTime

end MeasureTheory.Submartingale
