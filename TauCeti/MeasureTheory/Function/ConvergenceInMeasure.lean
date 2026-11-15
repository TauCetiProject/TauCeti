/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.Moments.Chebyshev

/-! # Convergence in measure from moment and high-probability bounds

A standard way to consume concentration inequalities: if for each index `i` the
deviation `edist (f i x) (g x)` exceeds some deterministic `rate i` only on a
set of small measure, and `rate` tends to `0`, then `f` tends to `g` in
measure.  This is how "with high probability, the error is at most `rate i`"
statements are converted into `MeasureTheory.TendstoInMeasure`.

No measurability is required of the exceptional sets, since the squeeze only
uses monotonicity of the (outer) measure; the index runs along an arbitrary
filter, matching the generality of `MeasureTheory.TendstoInMeasure`.

Convergence in mean square also implies convergence in measure, with integrability of the
squared deviations required only eventually along the filter.

## Main results

* `MeasureTheory.TendstoInMeasure.add`, `MeasureTheory.TendstoInMeasure.const_smul`,
  `MeasureTheory.AEStronglyMeasurable.tendstoInMeasure_smul`: algebraic operations preserving
  convergence in measure.
* `MeasureTheory.tendstoInMeasure_of_tendsto_integral_norm_sq`: convergence in mean square
  implies convergence in measure for any measure and filter.
* `TauCeti.tendsto_measure_ge_zero_const_mul`, `TauCeti.tendsto_measure_ge_zero_mul_of_ae_lt_top`,
  and `TauCeti.tendsto_measure_ge_zero_of_ae_le`: positive tail-measure convergence to zero under
  constant scaling, finite-measure almost-everywhere finite random weights, and eventual
  almost-everywhere bounds `E ≤ E₁ + E₂` (including threshold `∞`).
* `TauCeti.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm`: `L²(μ.prod ν)` convergence to
  zero forces the `ν`-tail measure of the `μ`-slice lower square integrals to tend to zero.
* `TauCeti.tendstoInMeasure_of_tendsto_measure_rate_lt_edist`: the `edist`
  form, for an `ℝ≥0∞`-valued rate and a target with an extended distance.
* `TauCeti.tendstoInMeasure_of_tendsto_measure_rate_lt_dist`: the `dist`
  form, for a real-valued rate and a pseudometric target.
* `TauCeti.tendstoInMeasure_of_tendsto_measure_dist_le_rate`: the
  high-probability phrasing for a probability measure, with hypothesis
  `μ {x | dist (f i x) (g x) ≤ rate i} → 1`; here null-measurability of the
  good events (eventually along the filter) is genuinely needed, since an outer
  measure can assign full measure to both a set and its complement.

## Source

Adapted from the Davis--Kahan/DKPS formalization,
`ForMathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` at `fc38eb4`,
by Claude Fable 5 (Kitware, Inc., Apache-2.0).
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α ι E : Type*} {m : MeasurableSpace α} {μ : Measure α} {l : Filter ι}

/--
If `f i` is within `rate i` of `g` outside a set whose measure tends to `0`,
and `rate` tends to `0`, then `f` tends to `g` in measure.

This is the form in which concentration inequalities ("with high probability,
`edist (f i x) (g x) ≤ rate i`") are consumed.  No measurability of the
exceptional sets is needed: the proof only uses monotonicity of the measure.
-/
theorem tendstoInMeasure_of_tendsto_measure_rate_lt_edist [EDist E]
    {f : ι → α → E} {g : α → E} {rate : ι → ℝ≥0∞} (hrate : Tendsto rate l (𝓝 0))
    (h : Tendsto (fun i => μ {x | rate i < edist (f i x) (g x)}) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun i => zero_le) ?_
  filter_upwards [hrate.eventually_lt_const hε] with i hi
  exact measure_mono fun x hx => hi.trans_le hx

/--
If a real-valued rate tends to zero and the measure of the events
`{x | rate i < dist (f i x) (g x)}` tends to zero, then `f` converges to `g`
in measure. The rate may be negative, and no measurability assumption on the
exceptional sets is required.
-/
theorem tendstoInMeasure_of_tendsto_measure_rate_lt_dist [PseudoMetricSpace E]
    {f : ι → α → E} {g : α → E} {rate : ι → ℝ} (hrate : Tendsto rate l (𝓝 0))
    (h : Tendsto (fun i => μ {x | rate i < dist (f i x) (g x)}) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun i => zero_le) ?_
  filter_upwards [hrate.eventually_lt_const hε] with i hi
  exact measure_mono fun x hx => hi.trans_le hx

/--
**High-probability phrasing.** If, for a probability measure, the events
"`f i` is within `rate i` of `g`" have probability tending to `1` and `rate`
tends to `0`, then `f` tends to `g` in measure.

Unlike `tendstoInMeasure_of_tendsto_measure_rate_lt_dist`, null-measurability
of the good events cannot be dropped here (it is required only eventually along
`l`): an outer measure can assign measure `1` to both a set and its complement,
so `μ s → 1` alone says nothing about `μ sᶜ`.
-/
theorem tendstoInMeasure_of_tendsto_measure_dist_le_rate [PseudoMetricSpace E]
    [IsProbabilityMeasure μ] {f : ι → α → E} {g : α → E} {rate : ι → ℝ}
    (hrate : Tendsto rate l (𝓝 0))
    (hmeas : ∀ᶠ i in l, NullMeasurableSet {x | dist (f i x) (g x) ≤ rate i} μ)
    (hprob : Tendsto (fun i => μ {x | dist (f i x) (g x) ≤ rate i}) l (𝓝 1)) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_of_tendsto_measure_rate_lt_dist hrate ?_
  have h := ENNReal.Tendsto.sub tendsto_const_nhds hprob (Or.inl ENNReal.one_ne_top)
  rw [tsub_self] at h
  refine h.congr' ?_
  filter_upwards [hmeas] with i hi
  rw [← prob_compl_eq_one_sub₀ hi, Set.compl_ofPred]
  simp_rw [not_le]

/-- Scaling an `ℝ≥0∞`-valued family by a finite constant `c ≠ ∞` preserves convergence of all
positive tail measures to zero (including at threshold `∞`). -/
theorem tendsto_measure_ge_zero_const_mul {E : ι → α → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E i x}) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ μ {x | ε ≤ c * E i x}) l (𝓝 0) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp only [zero_mul, not_le_of_gt hε, Set.ofPred_false, measure_empty]
    exact tendsto_const_nhds
  rcases eq_or_ne ε ∞ with rfl | _
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h 1 one_pos)
      (fun _ ↦ zero_le) fun i ↦ measure_mono fun x hx ↦ ?_
    by_contra hnot
    rw [Set.mem_ofPred_eq, not_le] at hnot
    exact (ENNReal.mul_lt_top hc.lt_top (hnot.trans ENNReal.one_lt_top)).not_ge hx
  · have hdiv : 0 < ε / c := ENNReal.div_pos hε.ne' hc
    refine (h (ε / c) hdiv).congr' (.of_forall fun i ↦ ?_)
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, ENNReal.div_le_iff_le_mul (.inl hc0) (.inl hc), mul_comm]

/-- On a finite measure space, multiplying an `ℝ≥0∞`-valued family by a fixed `μ`-almost everywhere
measurable and `μ`-almost everywhere finite weight preserves convergence of all positive tail
measures to zero (including at threshold `∞`). -/
theorem tendsto_measure_ge_zero_mul_of_ae_lt_top [IsFiniteMeasure μ]
    {E : ι → α → ℝ≥0∞} {c : α → ℝ≥0∞} (hc : AEMeasurable c μ) (hfin : ∀ᵐ x ∂μ, c x < ∞)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E i x}) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ μ {x | ε ≤ c x * E i x}) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  let A (M : ℕ) : Set α := {x | (M : ℝ≥0∞) ≤ c x}
  have hA_meas (M : ℕ) : NullMeasurableSet (A M) μ := hc.nullMeasurable measurableSet_Ici
  have hA_anti : Antitone A :=
    fun _ _ hMN _ (hx : (_ : ℝ≥0∞) ≤ _) ↦ (Nat.cast_le.2 hMN).trans hx
  have hA_inter : μ (⋂ M, A M) = 0 := by
    refine measure_mono_null (fun x hx ↦ ?_) (ae_iff.1 hfin)
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, not_lt, top_le_iff] at hx ⊢
    by_contra hne
    obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hne
    exact hM.not_ge (hx M)
  have hA_lim : Tendsto (μ ∘ A) atTop (𝓝 0) :=
    hA_inter ▸ tendsto_measure_iInter_atTop hA_meas hA_anti ⟨0, measure_ne_top μ _⟩
  have hhalf : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨M, hM⟩ := (hA_lim.eventually (eventually_le_nhds hhalf)).exists
  have hEM := (tendsto_measure_ge_zero_const_mul (ENNReal.natCast_ne_top M) h hε).eventually
    (eventually_le_nhds hhalf)
  filter_upwards [hEM] with i hi
  have hsub : {x | ε ≤ c x * E i x} ⊆ A M ∪ {x | ε ≤ (M : ℝ≥0∞) * E i x} := fun x hx ↦ by
    by_cases hxM : x ∈ A M
    · exact Or.inl hxM
    · refine Or.inr (show ε ≤ (M : ℝ≥0∞) * E i x from hx.trans ?_)
      gcongr
      exact le_of_not_ge hxM
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans
    ((add_le_add hM hi).trans_eq (ENNReal.add_halves δ))

/-- If `E` is eventually bounded `μ`-almost everywhere by `E₁ + E₂`, and all positive tail measures
of `E₁` and `E₂` tend to zero along `l`, then all positive tail measures of `E` tend to zero along
`l` (including at threshold `∞`). -/
theorem tendsto_measure_ge_zero_of_ae_le {E E₁ E₂ : ι → α → ℝ≥0∞}
    (h₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E₁ i x}) l (𝓝 0))
    (h₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E₂ i x}) l (𝓝 0))
    (hle : ∀ᶠ i in l, ∀ᵐ x ∂μ, E i x ≤ E₁ i x + E₂ i x)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ μ {x | ε ≤ E i x}) l (𝓝 0) := by
  rcases eq_or_ne ε ∞ with rfl | _
  · have hsum : Tendsto (fun i ↦ μ {x | 1 ≤ E₁ i x} + μ {x | 1 ≤ E₂ i x}) l (𝓝 0) := by
      simpa using (h₁ 1 one_pos).add (h₂ 1 one_pos)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ ↦ zero_le) (hle.mono fun i hi ↦ ?_)
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hi] with x hx htop
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    have hlt : E i x < ∞ := hx.trans_lt (ENNReal.add_lt_top.2
      ⟨hnot.1.trans ENNReal.one_lt_top, hnot.2.trans ENNReal.one_lt_top⟩)
    exact hlt.not_ge htop
  · have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    have hsum : Tendsto (fun i ↦
        μ {x | ε / 2 ≤ E₁ i x} + μ {x | ε / 2 ≤ E₂ i x}) l (𝓝 0) := by
      simpa using (h₁ _ hhalf).add (h₂ _ hhalf)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ ↦ zero_le) (hle.mono fun i hi ↦ ?_)
    refine (measure_mono_ae ?_).trans (measure_union_le _ _)
    filter_upwards [hi] with x hx hge
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    have hlt : E₁ i x + E₂ i x < ε :=
      (ENNReal.add_lt_add hnot.1 hnot.2).trans_eq (ENNReal.add_halves ε)
    exact (hx.trans_lt hlt).not_ge hge

/-- If `eLpNorm (f i) 2 (μ.prod ν)` tends to zero along `l` for `SFinite` measures `μ` and `ν`,
then the `ν`-measure of the slices where `∫⁻ x, ‖f i (x, y)‖ₑ ^ 2 ∂μ` exceeds any positive
threshold `ε` (including `∞`) tends to zero along `l`. No explicit measurability hypothesis on `f`
is needed, since `eLpNorm (f i) 2 (μ.prod ν) < ∞` eventually forces `AEStronglyMeasurable`. -/
theorem tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
    {β ε' : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite μ] [SFinite ν]
    [TopologicalSpace ε'] [ContinuousENorm ε'] {f : ι → α × β → ε'}
    (hlim : Tendsto (fun i ↦ eLpNorm (f i) 2 (μ.prod ν)) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ ν {y | ε ≤ ∫⁻ x, ‖f i (x, y)‖ₑ ^ 2 ∂μ}) l (𝓝 0) := by
  have hev : ∀ᶠ i in l, AEStronglyMeasurable (f i) (μ.prod ν) := by
    filter_upwards [hlim.eventually (eventually_lt_nhds ENNReal.zero_lt_top)] with i hi
    by_contra hnot
    exact hi.ne (eLpNorm_of_not_aestronglyMeasurable hnot)
  have hsq : Tendsto (fun i ↦ eLpNorm (f i) 2 (μ.prod ν) ^ 2) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.pow (n := 2) hlim
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
      (Eventually.of_forall fun _ ↦ zero_le) (hev.mono fun i hsm ↦ ?_)
    have hm : AEMeasurable (fun p ↦ ‖f i p‖ₑ ^ 2) (μ.prod ν) := hsm.eNorm.pow_const 2
    have hsub : {y | ∞ ≤ ∫⁻ x, ‖f i (x, y)‖ₑ ^ 2 ∂μ} ⊆
        {y | 1 ≤ ∫⁻ x, ‖f i (x, y)‖ₑ ^ 2 ∂μ} :=
      fun _ hy ↦ (le_top : (1 : ℝ≥0∞) ≤ ∞).trans hy
    refine (measure_mono hsub).trans ?_
    refine (MeasureTheory.meas_ge_le_lintegral_div hm.lintegral_prod_left'
      one_ne_zero ENNReal.one_ne_top).trans_eq ?_
    rw [div_one, ← lintegral_prod_symm _ hm,
      TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow (by norm_num : 2 ≠ 0) hsm]
    rfl
  · have hdiv : Tendsto (fun i ↦ eLpNorm (f i) 2 (μ.prod ν) ^ 2 / ε) l (𝓝 0) := by
      simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hsq (.inr hε.ne')
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdiv
      (Eventually.of_forall fun _ ↦ zero_le) (hev.mono fun i hsm ↦ ?_)
    have hm : AEMeasurable (fun p ↦ ‖f i p‖ₑ ^ 2) (μ.prod ν) := hsm.eNorm.pow_const 2
    refine (MeasureTheory.meas_ge_le_lintegral_div hm.lintegral_prod_left'
      hε.ne' hεtop).trans_eq ?_
    rw [← lintegral_prod_symm _ hm,
      TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow (by norm_num : 2 ≠ 0) hsm]
    rfl

end TauCeti

namespace MeasureTheory

open Filter ENNReal Topology

/-- Pointwise sums of functions converging in measure converge in measure to the sum of the
limits, for any measure and filter and without measurability hypotheses. -/
theorem TendstoInMeasure.add {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [SeminormedAddCommGroup E] {l : Filter ι} {f₁ f₂ : ι → Ω → E} {g₁ g₂ : Ω → E}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i ω ↦ f₁ i ω + f₂ i ω) l (fun ω ↦ g₁ ω + g₂ ω) := by
  refine tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsum : Tendsto (fun i ↦ μ {ω | ε / 2 ≤ ‖f₁ i ω - g₁ ω‖} +
      μ {ω | ε / 2 ≤ ‖f₂ i ω - g₂ ω‖}) l (𝓝 0) := by
    simpa using ((tendstoInMeasure_iff_norm.1 h₁) _ hhalf).add
      ((tendstoInMeasure_iff_norm.1 h₂) _ hhalf)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun i ↦ ?_
  refine (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
  by_contra hnot
  push Not at hnot
  have htri : ‖f₁ i ω + f₂ i ω - (g₁ ω + g₂ ω)‖ ≤ ‖f₁ i ω - g₁ ω‖ + ‖f₂ i ω - g₂ ω‖ := by
    simpa only [add_sub_add_comm] using norm_add_le (f₁ i ω - g₁ ω) (f₂ i ω - g₂ ω)
  linarith

/-- Pointwise scalar multiplication by a constant preserves convergence in measure whenever
`(c • ·)` is uniformly continuous, for any measure and filter and without measurability
hypotheses. -/
theorem TendstoInMeasure.const_smul {Ω M E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [PseudoEMetricSpace E] [SMul M E] [UniformContinuousConstSMul M E]
    {l : Filter ι} {f : ι → Ω → E} {g : Ω → E}
    (h : TendstoInMeasure μ f l g) (c : M) :
    TendstoInMeasure μ (fun i ω ↦ c • f i ω) l (fun ω ↦ c • g ω) := by
  intro ε hε
  obtain ⟨δ, hδ, huc⟩ := EMetric.uniformContinuous_iff.1
    (uniformContinuous_const_smul c : UniformContinuous fun x : E ↦ c • x) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ ↦ zero_le) fun i ↦ measure_mono fun ω hω ↦ ?_
  by_contra hlt
  exact (huc (not_le.1 hlt)).not_ge hω

/-- Pointwise negation preserves convergence in measure, for any measure and filter and without
measurability hypotheses. -/
theorem TendstoInMeasure.neg {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [SeminormedAddCommGroup E] {l : Filter ι} {f : ι → Ω → E} {g : Ω → E}
    (h : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i ω ↦ -f i ω) l (fun ω ↦ -g ω) := by
  simpa only [neg_one_smul] using h.const_smul (-1 : ℤ)

/-- Pointwise subtraction preserves convergence in measure, for any measure and filter and without
measurability hypotheses. -/
theorem TendstoInMeasure.sub {Ω E ι : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [SeminormedAddCommGroup E] {l : Filter ι} {f₁ f₂ : ι → Ω → E} {g₁ g₂ : Ω → E}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i ω ↦ f₁ i ω - f₂ i ω) l (fun ω ↦ g₁ ω - g₂ ω) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- On a finite measure space, pointwise scalar multiplication by an almost-everywhere strongly
measurable scalar function preserves convergence in measure along any filter. -/
theorem AEStronglyMeasurable.tendstoInMeasure_smul {Ω 𝕜 E ι : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] [SeminormedAddCommGroup 𝕜] [SeminormedAddCommGroup E]
    [DistribSMul 𝕜 E] [IsBoundedSMul 𝕜 E] {l : Filter ι} {c : Ω → 𝕜}
    (hc : AEStronglyMeasurable c μ) {f : ι → Ω → E} {g : Ω → E}
    (h : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i ω ↦ c ω • f i ω) l (fun ω ↦ c ω • g ω) := by
  refine tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_
  have hE (δ : ℝ≥0∞) (hδ : 0 < δ) :
      Tendsto (fun i ↦ μ {ω | δ ≤ ‖f i ω - g ω‖ₑ}) l (𝓝 0) := by
    rcases eq_or_ne δ ∞ with rfl | hδtop
    · simp only [not_le_of_gt eNorm_lt_top, Set.ofPred_false, measure_empty]
      exact tendsto_const_nhds
    · refine ((tendstoInMeasure_iff_norm.1 h) δ.toReal (ENNReal.toReal_pos hδ.ne' hδtop)).congr'
        (.of_forall fun i ↦ ?_)
      congr 1
      ext ω
      simp only [Set.mem_ofPred_eq, ← ofReal_norm, ENNReal.le_ofReal_iff_toReal_le hδtop
        (norm_nonneg _)]
  have hmul := TauCeti.tendsto_measure_ge_zero_mul_of_ae_lt_top hc.eNorm
    (.of_forall fun _ ↦ eNorm_lt_top) hE (ENNReal.ofReal_pos.2 hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul
    (fun _ ↦ zero_le) fun i ↦ measure_mono fun ω hω ↦ ?_
  rw [Set.mem_ofPred_eq] at hω ⊢
  have hbound : ‖c ω • f i ω - c ω • g ω‖ ≤ ‖c ω‖ * ‖f i ω - g ω‖ := by
    simpa only [smul_sub] using norm_smul_le (c ω) (f i ω - g ω)
  have he : ENNReal.ofReal ε ≤ ENNReal.ofReal (‖c ω‖ * ‖f i ω - g ω‖) :=
    ENNReal.ofReal_le_ofReal (hω.trans hbound)
  rwa [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm] at he

/-- Convergence in mean square implies convergence in measure, for any measure and filter.
Integrability of the squared deviations is needed only eventually. -/
theorem tendstoInMeasure_of_tendsto_integral_norm_sq {Ω E ι : Type*}
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [SeminormedAddCommGroup E]
    {l : Filter ι} {f : ι → Ω → E} {g : Ω → E}
    (hint : ∀ᶠ k in l, Integrable (fun ω ↦ ‖f k ω - g ω‖ ^ 2) μ)
    (hlim : Tendsto (fun k ↦ ∫ ω, ‖f k ω - g ω‖ ^ 2 ∂μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_
  have hbound := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hlim.div_const (ε ^ 2))
  simp only [zero_div, ENNReal.ofReal_zero, Function.comp_def] at hbound
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hint] with k hk
  exact TauCeti.meas_ge_le_integral_norm_sq_div_sq hk hε

end MeasureTheory
