/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.TightNormed
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Measure.Portmanteau

/-!
# Boundedness in probability and stochastic order algebra

A sequence of functions `X : ℕ → Ω → E` taking values in a seminormed group `E` is **bounded in
probability** (written `Xₙ = O_P(1)`) under a measure `μ` if for every `ε > 0` there is a threshold
`C > 0` such that `μ.real {ω | C < ‖X n ω‖} ≤ ε` eventually as `n → ∞`. Because `μ.real` uses the
outer measure, no measurability assumption on `X n` is required in the definition or in the basic
algebraic closure properties.

## Main definitions

* `TauCeti.IsBoundedInProbability` — stochastic boundedness `O_P(1)` for a sequence `ℕ → Ω → E`.

## Main statements

* `TauCeti.isBoundedInProbability_iff` — definitional unfolding of `IsBoundedInProbability`.
* `TauCeti.IsBoundedInProbability.mono_norm_ae`, `TauCeti.IsBoundedInProbability.add`,
  `TauCeti.IsBoundedInProbability.sub`, `TauCeti.IsBoundedInProbability.const_smul`,
  `TauCeti.IsBoundedInProbability.smul` — closure of
  `O_P(1)` under norm domination, linear combinations, and scalar actions.
* `TauCeti.isBoundedInProbability_of_tendstoInMeasure_const`,
  `TauCeti.isBoundedInProbability_of_tendstoInMeasure`,
  `TauCeti.isBoundedInProbability_of_tendstoInDistribution` — sequences converging in measure or in
  distribution are bounded in probability.
* `TauCeti.isBoundedInProbability_iff_isTightMeasureSet_range` — in a proper normed group with its
  Borel σ-algebra, boundedness in probability is equivalent to tightness of the sequence of laws
  `fun n ↦ μ.map (X n)`.
* `TauCeti.tendstoInMeasure_smul_zero_of_isBoundedInProbability`,
  `TauCeti.tendstoInMeasure_smul_zero_of_tendstoInMeasure_zero` — the stochastic order algebra
  identities `O_P(1) • o_P(1) = o_P(1)` and `o_P(1) • O_P(1) = o_P(1)`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §2.1–2.2,
  pp. 8–13.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace TauCeti

section Basic

variable {Ω E F : Type*} [MeasurableSpace Ω] [SeminormedAddGroup E]

/-- A sequence `X : ℕ → Ω → E` is **bounded in probability** (`Xₙ = O_P(1)`) under `μ` if for every
`ε > 0` there is `C > 0` such that `μ.real {ω | C < ‖X n ω‖} ≤ ε` eventually as `n → ∞`. The sets
are measured by the outer measure, so no measurability of `X n` is required. -/
def IsBoundedInProbability (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  ∀ ε > 0, ∃ C > 0, ∀ᶠ n in atTop, μ.real {ω | C < ‖X n ω‖} ≤ ε

/-- Characterization of `IsBoundedInProbability`. -/
theorem isBoundedInProbability_iff {μ : Measure Ω} {X : ℕ → Ω → E} :
    IsBoundedInProbability μ X ↔
      ∀ ε > 0, ∃ C > 0, ∀ᶠ n in atTop, μ.real {ω | C < ‖X n ω‖} ≤ ε :=
  Iff.rfl

/-- A deterministic constant sequence is bounded in probability for any measure. -/
theorem isBoundedInProbability_const (μ : Measure Ω) (c : E) :
    IsBoundedInProbability μ (fun _ _ ↦ c) := by
  intro ε hε
  refine ⟨‖c‖ + 1, by positivity, Eventually.of_forall fun _ ↦ ?_⟩
  have hempty : {_ω : Ω | ‖c‖ + 1 < ‖c‖} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun _ h ↦ by linarith [Set.mem_ofPred_eq.mp h]
  rw [hempty, measureReal_empty]
  exact hε.le

/-- Negation preserves boundedness in probability for any measure. -/
theorem IsBoundedInProbability.neg {μ : Measure Ω} {X : ℕ → Ω → E}
    (hX : IsBoundedInProbability μ X) : IsBoundedInProbability μ (fun n ω ↦ -X n ω) := by
  intro ε hε
  simpa only [norm_neg] using hX ε hε

/-- A sequence whose norm is eventually almost everywhere dominated by a sequence bounded in
probability is itself bounded in probability, under a finite measure. -/
theorem IsBoundedInProbability.mono_norm_ae [SeminormedAddGroup F] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → E} {Y : ℕ → Ω → F}
    (hX : IsBoundedInProbability μ X) (hle : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, ‖Y n ω‖ ≤ ‖X n ω‖) :
    IsBoundedInProbability μ Y := by
  intro ε hε
  obtain ⟨C, hC, hX_ev⟩ := hX ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hX_ev, hle] with n hn hle_n
  have hsub : {ω | C < ‖Y n ω‖} ≤ᵐ[μ] {ω | C < ‖X n ω‖} := by
    filter_upwards [hle_n] with ω hω hY
    exact lt_of_lt_of_le hY hω
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans hn

/-- Helper for two-argument closure of `IsBoundedInProbability` via a positive output threshold
function whose tail event lies in the union of the two input tail events. -/
private theorem isBoundedInProbability_of_union
    {E₁ E₂ E₃ : Type*} [SeminormedAddGroup E₁] [SeminormedAddGroup E₂] [SeminormedAddGroup E₃]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → E₁} {Y : ℕ → Ω → E₂} {Z : ℕ → Ω → E₃}
    (hX : IsBoundedInProbability μ X) (hY : IsBoundedInProbability μ Y)
    (C : ℝ → ℝ → ℝ) (hC_pos : ∀ {c₁ c₂}, 0 < c₁ → 0 < c₂ → 0 < C c₁ c₂)
    (hbound : ∀ {c₁ c₂}, 0 < c₁ → 0 < c₂ → ∀ n ω,
      ‖X n ω‖ ≤ c₁ → ‖Y n ω‖ ≤ c₂ → ‖Z n ω‖ ≤ C c₁ c₂) :
    IsBoundedInProbability μ Z := by
  intro ε hε
  obtain ⟨c₁, hc₁, hX_ev⟩ := hX (ε / 2) (half_pos hε)
  obtain ⟨c₂, hc₂, hY_ev⟩ := hY (ε / 2) (half_pos hε)
  refine ⟨C c₁ c₂, hC_pos hc₁ hc₂, ?_⟩
  filter_upwards [hX_ev, hY_ev] with n hn₁ hn₂
  have hsub : {ω | C c₁ c₂ < ‖Z n ω‖} ⊆ {ω | c₁ < ‖X n ω‖} ∪ {ω | c₂ < ‖Y n ω‖} := by
    intro ω hω
    by_contra hmem
    rw [Set.mem_union, not_or] at hmem
    exact not_le_of_gt (Set.mem_ofPred_eq.mp hω)
      (hbound hc₁ hc₂ n ω (not_lt.1 hmem.1) (not_lt.1 hmem.2))
  calc μ.real {ω | C c₁ c₂ < ‖Z n ω‖}
      ≤ μ.real ({ω | c₁ < ‖X n ω‖} ∪ {ω | c₂ < ‖Y n ω‖}) := measureReal_mono hsub
    _ ≤ μ.real {ω | c₁ < ‖X n ω‖} + μ.real {ω | c₂ < ‖Y n ω‖} := measureReal_union_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hn₁ hn₂
    _ = ε := add_halves ε

/-- The sum of two sequences bounded in probability is bounded in probability, under a finite
measure. -/
theorem IsBoundedInProbability.add {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : ℕ → Ω → E}
    (hX : IsBoundedInProbability μ X) (hY : IsBoundedInProbability μ Y) :
    IsBoundedInProbability μ (fun n ω ↦ X n ω + Y n ω) :=
  isBoundedInProbability_of_union hX hY (· + ·) (fun hc₁ hc₂ ↦ by positivity)
    fun _ _ _ _ h1 h2 ↦ (norm_add_le _ _).trans (add_le_add h1 h2)

/-- The difference of two sequences bounded in probability is bounded in probability, under a
finite measure. -/
theorem IsBoundedInProbability.sub {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : ℕ → Ω → E}
    (hX : IsBoundedInProbability μ X) (hY : IsBoundedInProbability μ Y) :
    IsBoundedInProbability μ (fun n ω ↦ X n ω - Y n ω) := by
  simpa only [sub_eq_add_neg] using hX.add hY.neg

/-- Scaling a sequence bounded in probability by a sequence bounded in probability yields a sequence
bounded in probability, under a finite measure. -/
theorem IsBoundedInProbability.smul {𝕜 : Type*} [SeminormedAddGroup 𝕜]
    [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] {μ : Measure Ω} [IsFiniteMeasure μ]
    {U : ℕ → Ω → 𝕜} {V : ℕ → Ω → E}
    (hU : IsBoundedInProbability μ U) (hV : IsBoundedInProbability μ V) :
    IsBoundedInProbability μ (fun n ω ↦ U n ω • V n ω) :=
  isBoundedInProbability_of_union hU hV (· * ·) (fun hc₁ hc₂ ↦ by positivity)
    fun hc₁ _ _ _ h1 h2 ↦ (norm_smul_le _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) hc₁.le)

/-- Scaling a sequence bounded in probability by a fixed constant preserves boundedness in
probability, under a finite measure. -/
theorem IsBoundedInProbability.const_smul {𝕜 : Type*} [SeminormedAddGroup 𝕜]
    [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → E} (hX : IsBoundedInProbability μ X) (c : 𝕜) :
    IsBoundedInProbability μ (fun n ω ↦ c • X n ω) :=
  (isBoundedInProbability_const μ c).smul hX

/-- A single function whose norm is almost-everywhere measurable defines a constant sequence that
is bounded in probability under any finite measure. The measurability hypothesis on `‖Z ·‖` is
needed because continuity from above fails for outer measure on arbitrary non-measurable sets. -/
theorem isBoundedInProbability_of_aemeasurable_norm {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → E} (hZ : AEMeasurable (fun ω ↦ ‖Z ω‖) μ) :
    IsBoundedInProbability μ (fun _ ↦ Z) := by
  have hlim := MeasureTheory.tendsto_measure_dist_ge_atTop hZ.aestronglyMeasurable 0
  intro ε hε
  obtain ⟨r, hr, hr1⟩ :=
    ((hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).and (eventually_ge_atTop 1)).exists
  refine ⟨r, by linarith, Eventually.of_forall fun _ ↦ ?_⟩
  have hsub : {ω | r < ‖Z ω‖} ⊆ {ω | r ≤ dist ‖Z ω‖ 0} := fun ω hω ↦ by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), Set.mem_ofPred_eq] using
      le_of_lt (Set.mem_ofPred_eq.mp hω)
  have hle : μ {ω | r < ‖Z ω‖} ≤ ENNReal.ofReal ε := (measure_mono hsub).trans hr.le
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hle

/-- A sequence converging in measure to a constant is bounded in probability, for any measure and
with no measurability assumptions. -/
theorem isBoundedInProbability_of_tendstoInMeasure_const {μ : Measure Ω} {X : ℕ → Ω → E} {c : E}
    (h : TendstoInMeasure μ X atTop (fun _ ↦ c)) : IsBoundedInProbability μ X := by
  intro ε hε
  refine ⟨‖c‖ + 1, by positivity, ?_⟩
  have h1 := (tendstoInMeasure_iff_dist.1 h 1 one_pos).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  filter_upwards [h1] with n hn
  have hsub : {ω | ‖c‖ + 1 < ‖X n ω‖} ⊆ {ω | 1 ≤ dist (X n ω) c} := by
    intro ω hω
    have htri : ‖X n ω‖ ≤ dist (X n ω) c + ‖c‖ := by
      simpa only [dist_zero_right] using dist_triangle (X n ω) c 0
    exact Set.mem_ofPred_eq.mpr (by linarith [Set.mem_ofPred_eq.mp hω])
  have hle : μ {ω | ‖c‖ + 1 < ‖X n ω‖} ≤ ENNReal.ofReal ε := (measure_mono hsub).trans hn.le
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hle

/-- A sequence converging in measure to a limit whose norm is almost-everywhere measurable is
bounded in probability, under a finite measure. -/
theorem isBoundedInProbability_of_tendstoInMeasure {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → E} {Z : Ω → E} (h : TendstoInMeasure μ X atTop Z)
    (hZ : AEMeasurable (fun ω ↦ ‖Z ω‖) μ) : IsBoundedInProbability μ X := by
  have hsub : TendstoInMeasure μ (fun n ω ↦ -(Z ω) + X n ω) atTop (fun _ ↦ 0) := by
    rw [tendstoInMeasure_iff_dist] at h ⊢
    simpa only [dist_zero_right, ← dist_eq_norm_neg_add'] using h
  have hbd := (isBoundedInProbability_of_aemeasurable_norm hZ).add
    (isBoundedInProbability_of_tendstoInMeasure_const hsub)
  simpa only [add_neg_cancel_left] using hbd

/-- A sequence converging in distribution in any seminormed group with opens-measurable structure
is bounded in probability. Neither properness nor second countability is required. -/
theorem isBoundedInProbability_of_tendstoInDistribution {Ω' : Type*} [MeasurableSpace Ω']
    [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {X : ℕ → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ μ) μ') :
    IsBoundedInProbability μ X := by
  intro ε hε
  obtain ⟨R, hR⟩ := ProbabilityMeasure.exists_measure_nndist_ge_le_of_tendsto h.tendsto (0 : E)
    (ENNReal.ofReal_pos.2 hε)
  refine ⟨(R : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [hR] with n hn
  have hopen : MeasurableSet {y : E | (R : ℝ) + 1 < ‖y‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hsub : {y : E | (R : ℝ) + 1 < ‖y‖} ⊆ {y : E | R ≤ nndist (0 : E) y} := by
    intro y hy
    have hnorm : (R : ℝ) ≤ (nndist (0 : E) y : ℝ) := by
      rw [coe_nndist, dist_zero_left]
      linarith [Set.mem_ofPred_eq.mp hy]
    exact_mod_cast hnorm
  have hle : μ {ω | (R : ℝ) + 1 < ‖X n ω‖} ≤ ENNReal.ofReal ε := by
    calc μ {ω | (R : ℝ) + 1 < ‖X n ω‖}
        = (μ.map (X n)) {y : E | (R : ℝ) + 1 < ‖y‖} :=
            (Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hopen).symm
      _ ≤ (μ.map (X n)) {y : E | R ≤ nndist (0 : E) y} := measure_mono hsub
      _ ≤ ENNReal.ofReal ε := hn
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hle

end Basic

section Tightness

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E]

/-- If the laws of a sequence of almost-everywhere measurable maps form a tight set of measures in
a normed group with opens-measurable structure, then the sequence is bounded in probability. -/
theorem isBoundedInProbability_of_isTightMeasureSet_range [OpensMeasurableSpace E]
    {μ : Measure Ω} {X : ℕ → Ω → E} (hX : ∀ n, AEMeasurable (X n) μ)
    (htight : IsTightMeasureSet (Set.range fun n ↦ μ.map (X n))) :
    IsBoundedInProbability μ X := by
  intro ε hε
  have hlim := tendsto_measure_norm_gt_of_isTightMeasureSet htight
  obtain ⟨r, hr⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists_forall_of_atTop
  refine ⟨max r 1, by positivity, Eventually.of_forall fun n ↦ ?_⟩
  have hopen : MeasurableSet {x : E | max r 1 < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hle : μ {ω | max r 1 < ‖X n ω‖} ≤ ENNReal.ofReal ε := by
    calc μ {ω | max r 1 < ‖X n ω‖}
        = (μ.map (X n)) {x : E | max r 1 < ‖x‖} :=
            (Measure.map_apply_of_aemeasurable (hX n) hopen).symm
      _ ≤ ⨆ ν ∈ Set.range (fun k ↦ μ.map (X k)), ν {x : E | max r 1 < ‖x‖} :=
            le_biSup (fun ν : Measure E ↦ ν {x : E | max r 1 < ‖x‖}) ⟨n, rfl⟩
      _ ≤ ENNReal.ofReal ε := (hr (max r 1) (le_max_left r 1)).le
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hle

/-- In a proper normed group with its Borel σ-algebra, the laws of a bounded-in-probability
sequence of almost-everywhere measurable maps under a finite measure form a tight set. -/
theorem isTightMeasureSet_range_of_isBoundedInProbability [ProperSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → E} (hX : ∀ n, AEMeasurable (X n) μ)
    (hbd : IsBoundedInProbability μ X) :
    IsTightMeasureSet (Set.range fun n ↦ μ.map (X n)) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt ?_
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  rcases eq_top_or_lt_top ε with rfl | hε_top
  · exact ⟨0, fun _ _ ↦ le_top⟩
  have hε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top.ne
  obtain ⟨C, _, hC⟩ := hbd ε.toReal hε_pos
  refine ⟨C, fun r hr ↦ limsup_le_of_le (by isBoundedDefault) ?_⟩
  filter_upwards [hC] with n hn
  have hopen : MeasurableSet {x : E | r < ‖x‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  calc (μ.map (X n)) {x : E | r < ‖x‖}
      = μ {ω | r < ‖X n ω‖} := Measure.map_apply_of_aemeasurable (hX n) hopen
    _ ≤ μ {ω | C < ‖X n ω‖} := measure_mono fun ω (hω : r < ‖X n ω‖) ↦ hr.trans_lt hω
    _ = ENNReal.ofReal (μ.real {ω | C < ‖X n ω‖}) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hn
    _ = ε := ENNReal.ofReal_toReal hε_top.ne

/-- In a proper normed group with its Borel σ-algebra, a sequence of almost-everywhere measurable
maps under a finite measure is bounded in probability if and only if its sequence of laws is
tight. -/
theorem isBoundedInProbability_iff_isTightMeasureSet_range [ProperSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → E} (hX : ∀ n, AEMeasurable (X n) μ) :
    IsBoundedInProbability μ X ↔ IsTightMeasureSet (Set.range fun n ↦ μ.map (X n)) :=
  ⟨isTightMeasureSet_range_of_isBoundedInProbability hX,
    isBoundedInProbability_of_isTightMeasureSet_range hX⟩

end Tightness

section StochasticOrder

variable {Ω 𝕜 E : Type*} [MeasurableSpace Ω]

private theorem tendstoInMeasure_zero_of_norm_le_mul
    {E₁ E₂ E₃ : Type*} [SeminormedAddGroup E₁] [SeminormedAddGroup E₂]
    [SeminormedAddGroup E₃] {μ : Measure Ω} [IsFiniteMeasure μ]
    {U : ℕ → Ω → E₁} {V : ℕ → Ω → E₂} {W : ℕ → Ω → E₃}
    (hU : IsBoundedInProbability μ U) (hV : TendstoInMeasure μ V atTop (fun _ ↦ 0))
    (hle : ∀ n ω, ‖W n ω‖ ≤ ‖U n ω‖ * ‖V n ω‖) :
    TendstoInMeasure μ W atTop (fun _ ↦ 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hV ⊢
  simp_rw [dist_zero_right] at hV ⊢
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨C, hC, hU_ev⟩ := hU (δ / 2) (half_pos hδ)
  have hV_ev := Metric.tendsto_nhds.1 (hV (ε / C) (by positivity)) (δ / 2) (half_pos hδ)
  filter_upwards [hU_ev, hV_ev] with n hnU hnV
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at hnV ⊢
  have hsub : {ω | ε ≤ ‖W n ω‖} ⊆ {ω | C < ‖U n ω‖} ∪ {ω | ε / C ≤ ‖V n ω‖} := by
    intro ω hω
    by_contra hmem
    rw [Set.mem_union, not_or] at hmem
    have h1 : ‖U n ω‖ ≤ C := not_lt.1 hmem.1
    have h2 : ‖V n ω‖ < ε / C := not_le.1 hmem.2
    have hmul : ‖W n ω‖ < ε := by
      calc ‖W n ω‖
          ≤ ‖U n ω‖ * ‖V n ω‖ := hle n ω
        _ ≤ C * ‖V n ω‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < C * (ε / C) := mul_lt_mul_of_pos_left h2 hC
        _ = ε := mul_div_cancel₀ ε hC.ne'
    linarith [Set.mem_ofPred_eq.mp hω]
  calc μ.real {ω | ε ≤ ‖W n ω‖}
      ≤ μ.real ({ω | C < ‖U n ω‖} ∪ {ω | ε / C ≤ ‖V n ω‖}) := measureReal_mono hsub
    _ ≤ μ.real {ω | C < ‖U n ω‖} + μ.real {ω | ε / C ≤ ‖V n ω‖} := measureReal_union_le _ _
    _ < δ / 2 + δ / 2 := add_lt_add_of_le_of_lt hnU hnV
    _ = δ := add_halves δ

/-- **Stochastic order algebra `O_P(1) • o_P(1) = o_P(1)`.** Scaling a sequence tending to `0` in
measure by a sequence bounded in probability yields a sequence tending to `0` in measure, under
any finite measure. -/
theorem tendstoInMeasure_smul_zero_of_isBoundedInProbability
    [SeminormedAddGroup 𝕜] [SeminormedAddGroup E] [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {U : ℕ → Ω → 𝕜} {V : ℕ → Ω → E}
    (hU : IsBoundedInProbability μ U) (hV : TendstoInMeasure μ V atTop (fun _ ↦ 0)) :
    TendstoInMeasure μ (fun n ω ↦ U n ω • V n ω) atTop (fun _ ↦ 0) :=
  tendstoInMeasure_zero_of_norm_le_mul hU hV fun n ω ↦ norm_smul_le (U n ω) (V n ω)

/-- **Stochastic order algebra `o_P(1) • O_P(1) = o_P(1)`.** Scaling a sequence bounded in
probability by a scalar sequence tending to `0` in measure yields a sequence tending to `0` in
measure, under any finite measure. -/
theorem tendstoInMeasure_smul_zero_of_tendstoInMeasure_zero
    [SeminormedAddGroup 𝕜] [SeminormedAddGroup E] [SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {U : ℕ → Ω → 𝕜} {V : ℕ → Ω → E}
    (hU : TendstoInMeasure μ U atTop (fun _ ↦ 0)) (hV : IsBoundedInProbability μ V) :
    TendstoInMeasure μ (fun n ω ↦ U n ω • V n ω) atTop (fun _ ↦ 0) :=
  tendstoInMeasure_zero_of_norm_le_mul hV hU fun n ω ↦
    (norm_smul_le (U n ω) (V n ω)).trans_eq (mul_comm _ _)

end StochasticOrder

end TauCeti
