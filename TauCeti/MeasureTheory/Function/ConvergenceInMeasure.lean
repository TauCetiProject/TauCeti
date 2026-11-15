/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
squared deviations required only eventually along the filter. In the other direction,
Chebyshev-type bounds with an auxiliary truncation level give measures tending to zero, and real
functions tending to zero in measure have upper tails of measure tending to zero.

## Main results

* `MeasureTheory.tendstoInMeasure_of_tendsto_integral_norm_sq`: convergence in mean square
  implies convergence in measure for any measure and filter.
* `TauCeti.tendstoInMeasure_of_tendsto_measure_rate_lt_edist`: the `edist`
  form, for an `ℝ≥0∞`-valued rate and a target with an extended distance.
* `TauCeti.tendstoInMeasure_of_tendsto_measure_rate_lt_dist`: the `dist`
  form, for a real-valued rate and a pseudometric target.
* `TauCeti.tendstoInMeasure_of_tendsto_measure_dist_le_rate`: the
  high-probability phrasing for a probability measure, with hypothesis
  `μ {x | dist (f i x) (g x) ≤ rate i} → 1`; here null-measurability of the
  good events (eventually along the filter) is genuinely needed, since an outer
  measure can assign full measure to both a set and its complement.
* `TauCeti.tendsto_measure_of_le_ofReal_div_sq_add`: a measure bounded by `δ / ε²` plus a
  term tending to zero for every `δ > 0` tends to zero.
* `TauCeti.tendsto_measure_lt_of_tendstoInMeasure`: real functions tending to zero in measure
  have upper tails of measure tending to zero.

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

/-- If, for every `δ > 0`, the measure of `A k` is at most `δ / ε²` plus a term `B δ k` tending to
zero along `l`, then the measure of `A k` tends to zero. This is how Chebyshev-type estimates
with an auxiliary truncation level `δ` are turned into convergence in probability. -/
theorem tendsto_measure_of_le_ofReal_div_sq_add {A : ι → Set α} {B : ℝ → ι → ℝ≥0∞} {ε : ℝ}
    (htail : ∀ δ > 0, Tendsto (B δ) l (𝓝 0))
    (hbound : ∀ δ > 0, ∀ k, μ (A k) ≤ ENNReal.ofReal (δ / ε ^ 2) + B δ k) :
    Tendsto (fun k ↦ μ (A k)) l (𝓝 0) := by
  -- For `ε = 0` the bound is `B 1 k` itself.
  by_cases hε : ε = 0
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (htail 1 one_pos)
      (fun _ ↦ zero_le) fun k ↦ ?_
    simpa [hε] using hbound 1 one_pos k
  refine ENNReal.tendsto_nhds_zero.2 fun c hc ↦ ?_
  by_cases hctop : c = ∞
  · simp [hctop]
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc.ne' hctop
  let δ := c.toReal * ε ^ 2 / 2
  have hδ : 0 < δ := by positivity
  have hhalf : 0 < ENNReal.ofReal (c.toReal / 2) := by positivity
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (htail δ hδ) _ hhalf] with k hk
  have hquot : δ / ε ^ 2 = c.toReal / 2 := by
    dsimp [δ]
    field_simp
  calc
    μ (A k) ≤ ENNReal.ofReal (δ / ε ^ 2) + B δ k := hbound δ hδ k
    _ ≤ ENNReal.ofReal (c.toReal / 2) + ENNReal.ofReal (c.toReal / 2) := by
      rw [hquot]
      exact add_le_add le_rfl hk
    _ = c := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
        ENNReal.ofReal_toReal hctop]

/-- If real functions `f i` tend to zero in measure, then for every `δ > 0` the measure of the
upper tail `{x | δ < f i x}` tends to zero. -/
theorem tendsto_measure_lt_of_tendstoInMeasure {f : ι → α → ℝ}
    (hf : TendstoInMeasure μ f l fun _ ↦ 0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun i ↦ μ {x | δ < f i x}) l (𝓝 0) := by
  have htail := (tendstoInMeasure_iff_norm.1 hf) δ hδ
  simp only [sub_zero, Real.norm_eq_abs] at htail
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ ↦ zero_le) fun i ↦ measure_mono fun x hx ↦ by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact hx.le.trans (le_abs_self _)

end TauCeti

namespace MeasureTheory

open Filter Topology

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
