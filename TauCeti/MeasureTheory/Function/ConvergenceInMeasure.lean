/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.Moments.Chebyshev

/-! # Convergence in measure from moment bounds, high-probability rates, and uniform operations

A standard way to consume concentration inequalities: if for each index `i` the
deviation `edist (f i x) (g x)` exceeds some deterministic `rate i` only on a
set of small measure, and `rate` tends to `0`, then `f` tends to `g` in
measure.  This is how "with high probability, the error is at most `rate i`"
statements are converted into `MeasureTheory.TendstoInMeasure`.

No measurability is required of the exceptional sets, since the squeeze only
uses monotonicity of the (outer) measure; the index runs along an arbitrary
filter, matching the generality of `MeasureTheory.TendstoInMeasure`.

Convergence in mean square also implies convergence in measure, with integrability of the
squared deviations required only eventually along the filter. Finally, `TendstoInMeasure` is
preserved under post-composition with uniformly continuous maps, product pairing, uniform group
operations, and uniformly continuous scalar multiplication without finiteness or measurability
hypotheses.

## Main results

* `UniformContinuous.comp_tendstoInMeasure`: post-composing with a uniformly continuous map
  preserves convergence in measure.
* `MeasureTheory.TendstoInMeasure.prodMk`: pairing two families that converge in measure yields
  convergence in measure in the product space.
* `MeasureTheory.TendstoInMeasure.mul`, `MeasureTheory.TendstoInMeasure.add`: convergence in
  measure is closed under multiplication and addition in a uniform group.
* `MeasureTheory.TendstoInMeasure.const_smul`, `MeasureTheory.TendstoInMeasure.const_mul`:
  convergence in measure is closed under uniformly continuous constant scalar and left
  multiplication.
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

The rate-based concentration lemmas are adapted from the Davis--Kahan/DKPS formalization,
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

end TauCeti

/-- Post-composing with a uniformly continuous map preserves convergence in measure, with no
finiteness assumption on the measure and no measurability assumption on the functions. -/
theorem UniformContinuous.comp_tendstoInMeasure {Ω E F ι : Type*}
    {_ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {l : Filter ι} {f : ι → Ω → E} {g : Ω → E} {ψ : E → F}
    (hψ : UniformContinuous ψ) (hf : MeasureTheory.TendstoInMeasure μ f l g) :
    MeasureTheory.TendstoInMeasure μ (fun k ω ↦ ψ (f k ω)) l (fun ω ↦ ψ (g ω)) := by
  intro ε hε
  obtain ⟨δ, hδ, hosc⟩ := EMetric.uniformContinuous_iff.1 hψ ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf δ hδ)
    (fun _ ↦ zero_le) fun k ↦ MeasureTheory.measure_mono fun ω hω ↦ ?_
  by_contra hlt
  exact (hosc (not_le.1 hlt)).not_ge hω

namespace MeasureTheory

open Filter Topology

/-- Pairing two families that converge in measure gives convergence in measure in the product
space. -/
theorem TendstoInMeasure.prodMk {Ω E F ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {l : Filter ι}
    {f₁ : ι → Ω → E} {f₂ : ι → Ω → F} {g₁ : Ω → E} {g₂ : Ω → F}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun k ω ↦ (f₁ k ω, f₂ k ω)) l (fun ω ↦ (g₁ ω, g₂ ω)) := by
  intro ε hε
  have h0 : Tendsto
      (fun k ↦ μ {ω | ε ≤ edist (f₁ k ω) (g₁ ω)} + μ {ω | ε ≤ edist (f₂ k ω) (g₂ ω)})
      l (𝓝 0) := by
    simpa only [add_zero] using (h₁ ε hε).add (h₂ ε hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
    (fun _ ↦ zero_le) fun k ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  simpa only [Set.mem_union, Set.mem_ofPred_eq, Prod.edist_eq, le_max_iff] using hω

/-- Pointwise multiplication of two families converging in measure in a uniform group converges in
measure to the pointwise product of their limits. -/
@[to_additive
  /-- Pointwise addition of two families converging in measure in an additive uniform group
  converges in measure to the pointwise sum of their limits. -/]
theorem TendstoInMeasure.mul {Ω E ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [PseudoEMetricSpace E] [Group E] [IsUniformGroup E] {l : Filter ι}
    {f₁ f₂ : ι → Ω → E} {g₁ g₂ : Ω → E}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun k ω ↦ f₁ k ω * f₂ k ω) l (fun ω ↦ g₁ ω * g₂ ω) :=
  uniformContinuous_mul.comp_tendstoInMeasure (h₁.prodMk h₂)

/-- Uniformly continuous constant scalar multiplication preserves convergence in measure. -/
@[to_additive
  /-- Uniformly continuous constant vector addition preserves convergence in measure. -/]
theorem TendstoInMeasure.const_smul {Ω M E ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [PseudoEMetricSpace E] [SMul M E] [UniformContinuousConstSMul M E] {l : Filter ι}
    {f : ι → Ω → E} {g : Ω → E} (hf : TendstoInMeasure μ f l g) (c : M) :
    TendstoInMeasure μ (fun k ω ↦ c • f k ω) l (fun ω ↦ c • g ω) :=
  (uniformContinuous_const_smul c).comp_tendstoInMeasure hf

/-- Left multiplication by a constant preserves convergence in measure whenever left multiplication
is uniformly continuous via `UniformContinuousConstSMul R R`. -/
theorem TendstoInMeasure.const_mul {Ω R ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [Mul R] [PseudoEMetricSpace R] [UniformContinuousConstSMul R R] {l : Filter ι}
    {f : ι → Ω → R} {g : Ω → R} (hf : TendstoInMeasure μ f l g) (c : R) :
    TendstoInMeasure μ (fun k ω ↦ c * f k ω) l (fun ω ↦ c * g ω) :=
  hf.const_smul c

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
