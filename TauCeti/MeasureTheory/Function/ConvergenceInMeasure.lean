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
squared deviations required only eventually along the filter.

## Main results

* `UniformContinuous.comp_tendstoInMeasure`: composition with a uniformly continuous map preserves
  convergence in measure.
* `MeasureTheory.TendstoInMeasure.prodMk`, `add`, `neg`, `sub`, `const_smul`: algebraic closure of
  convergence in measure on uniform additive groups and actions, with no measurability or
  finite-measure assumptions.
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

## Source

Adapted from the Davis--Kahan/DKPS formalization,
`ForMathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` at `fc38eb4`,
by Claude Fable 5 (Kitware, Inc., Apache-2.0).
-/

public section

/-- Composition on the left with a uniformly continuous map preserves convergence in measure, for
any measure and filter and with no measurability assumptions. -/
theorem UniformContinuous.comp_tendstoInMeasure {α ι E F : Type*} {mα : MeasurableSpace α}
    {μ : MeasureTheory.Measure α} [PseudoEMetricSpace E] [PseudoEMetricSpace F] {l : Filter ι}
    {T : E → F} {f : ι → α → E} {g : α → E} (hT : UniformContinuous T)
    (hf : MeasureTheory.TendstoInMeasure μ f l g) :
    MeasureTheory.TendstoInMeasure μ (fun i x ↦ T (f i x)) l (fun x ↦ T (g x)) := by
  intro ε hε
  obtain ⟨δ, hδ, hTδ⟩ := EMetric.uniformContinuous_iff.1 hT ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf δ hδ)
    (fun _ ↦ zero_le) fun i ↦ MeasureTheory.measure_mono fun x hx ↦ ?_
  by_contra hlt
  exact hx.not_gt (hTδ (not_le.mp hlt))

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

end TauCeti

namespace MeasureTheory

open Filter Topology
open scoped ENNReal

/-- A constant family of functions converges in measure to itself along any filter. -/
theorem tendstoInMeasure_const {α ι E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoEMetricSpace E] {l : Filter ι} {g : α → E} :
    TendstoInMeasure μ (fun _ : ι ↦ g) l g := by
  intro ε hε
  simpa [hε.not_ge] using (tendsto_const_nhds (x := (0 : ℝ≥0∞)) (f := l))

namespace TendstoInMeasure

variable {α ι E F 𝕜 : Type*} {mα : MeasurableSpace α} {μ : Measure α} {l : Filter ι}

/-- Pointwise pairing preserves convergence in measure, with no measurability or finite-measure
assumptions. -/
theorem prodMk [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : ι → α → E} {g : α → E}
    {f' : ι → α → F} {g' : α → F} (hf : TendstoInMeasure μ f l g)
    (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (fun i x ↦ (f i x, f' i x)) l (fun x ↦ (g x, g' x)) := by
  intro ε hε
  have h0 : Tendsto (fun i ↦ μ {x | ε ≤ edist (f i x) (g x)} +
      μ {x | ε ≤ edist (f' i x) (g' x)}) l (𝓝 0) := by
    simpa using (hf ε hε).add (hf' ε hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun _ ↦ zero_le) fun i ↦ ?_
  refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
  simpa only [Set.mem_union, Set.mem_ofPred_eq, Prod.edist_eq, le_max_iff] using hx

/-- Pointwise addition on a uniform additive group preserves convergence in measure. -/
protected theorem add [PseudoEMetricSpace E] [AddGroup E] [IsUniformAddGroup E]
    {f f' : ι → α → E} {g g' : α → E} (hf : TendstoInMeasure μ f l g)
    (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (f + f') l (g + g') :=
  uniformContinuous_add.comp_tendstoInMeasure (hf.prodMk hf')

/-- Pointwise negation on a uniform additive group preserves convergence in measure. -/
protected theorem neg [PseudoEMetricSpace E] [AddGroup E] [IsUniformAddGroup E]
    {f : ι → α → E} {g : α → E} (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (-f) l (-g) :=
  uniformContinuous_neg.comp_tendstoInMeasure hf

/-- Pointwise subtraction on a uniform additive group preserves convergence in measure. -/
protected theorem sub [PseudoEMetricSpace E] [AddGroup E] [IsUniformAddGroup E]
    {f f' : ι → α → E} {g g' : α → E} (hf : TendstoInMeasure μ f l g)
    (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (f - f') l (g - g') :=
  uniformContinuous_sub.comp_tendstoInMeasure (hf.prodMk hf')

/-- Pointwise scalar multiplication by a constant preserves convergence in measure. -/
protected theorem const_smul [PseudoEMetricSpace E] [SMul 𝕜 E] [UniformContinuousConstSMul 𝕜 E]
    {f : ι → α → E} {g : α → E} (hf : TendstoInMeasure μ f l g) (c : 𝕜) :
    TendstoInMeasure μ (c • f) l (c • g) :=
  (uniformContinuous_const_smul c).comp_tendstoInMeasure hf

end TendstoInMeasure

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
