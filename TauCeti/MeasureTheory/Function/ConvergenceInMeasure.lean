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

* `MeasureTheory.tendstoInMeasure_of_tendsto_integral_norm_sq`: convergence in mean square
  implies convergence in measure for any measure and filter.
* `MeasureTheory.TendstoInMeasure.add`, `MeasureTheory.TendstoInMeasure.neg`,
  `MeasureTheory.TendstoInMeasure.sub`, `MeasureTheory.TendstoInMeasure.const_smul`: algebraic
  closure of convergence in measure.
* `MeasureTheory.ae_eq_of_tendstoInMeasure_sub_zero`: two families converging in measure whose
  difference tends to `0` in measure have a.e.-equal limits.
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

/-- Pointwise addition preserves convergence in measure. -/
theorem TendstoInMeasure.add {α ι E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [SeminormedAddCommGroup E] {l : Filter ι} {f f' : ι → α → E} {g g' : α → E}
    (hf : TendstoInMeasure μ f l g) (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (fun i x ↦ f i x + f' i x) l (fun x ↦ g x + g' x) := by
  rw [tendstoInMeasure_iff_norm] at hf hf' ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (hf (ε / 2) (half_pos hε)).add (hf' (ε / 2) (half_pos hε)))
    (fun _ ↦ zero_le) fun i ↦ (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
  by_contra hnot
  obtain ⟨h1, h2⟩ := not_or.mp hnot
  simp only [Set.mem_ofPred_eq, not_le] at h1 h2
  have htri : ‖(f i x + f' i x) - (g x + g' x)‖ ≤ ‖f i x - g x‖ + ‖f' i x - g' x‖ := by
    simpa only [add_sub_add_comm] using norm_add_le (f i x - g x) (f' i x - g' x)
  exact (lt_of_le_of_lt htri (by linarith)).not_ge hx

/-- Pointwise negation preserves convergence in measure. -/
theorem TendstoInMeasure.neg {α ι E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [SeminormedAddCommGroup E] {l : Filter ι} {f : ι → α → E} {g : α → E}
    (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i x ↦ -f i x) l (fun x ↦ -g x) := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro ε hε
  simpa only [neg_sub_neg, norm_sub_rev] using hf ε hε

/-- Pointwise subtraction preserves convergence in measure. -/
theorem TendstoInMeasure.sub {α ι E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [SeminormedAddCommGroup E] {l : Filter ι} {f f' : ι → α → E} {g g' : α → E}
    (hf : TendstoInMeasure μ f l g) (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (fun i x ↦ f i x - f' i x) l (fun x ↦ g x - g' x) := by
  simpa only [sub_eq_add_neg] using hf.add hf'.neg

/-- Scaling by a constant preserves convergence in measure. -/
theorem TendstoInMeasure.const_smul {α ι 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α}
    [SeminormedAddGroup 𝕜] [SeminormedAddGroup E] [DistribSMul 𝕜 E] [IsBoundedSMul 𝕜 E]
    {l : Filter ι} {f : ι → α → E} {g : α → E} (hf : TendstoInMeasure μ f l g) (c : 𝕜) :
    TendstoInMeasure μ (fun i x ↦ c • f i x) l (fun x ↦ c • g x) := by
  simp_rw [tendstoInMeasure_iff_dist, SeminormedAddGroup.dist_eq] at hf ⊢
  intro ε hε
  by_cases hc : ‖c‖ = 0
  · have hempty (i : ι) : {x | ε ≤ ‖-(c • f i x) + c • g x‖} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      calc ‖-(c • f i x) + c • g x‖ = ‖c • (-f i x + g x)‖ := by rw [smul_add, smul_neg]
        _ ≤ ‖c‖ * ‖-f i x + g x‖ := norm_smul_le _ _
        _ = 0 := by rw [hc, zero_mul]
        _ < ε := hε
    exact tendsto_const_nhds.congr fun i ↦ by rw [hempty, measure_empty]
  · have hcpos : 0 < ‖c‖ := lt_of_le_of_ne (norm_nonneg c) (Ne.symm hc)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hf (ε / ‖c‖) (div_pos hε hcpos)) (fun _ ↦ zero_le) fun i ↦ measure_mono fun x hx ↦ ?_
    rw [Set.mem_ofPred_eq, div_le_iff₀' hcpos]
    exact hx.trans (by rw [← smul_neg, ← smul_add]; exact norm_smul_le _ _)

/-- If two families converge in measure along a countably generated nontrivial filter and their
difference converges to `0` in measure, then their limits agree almost everywhere. -/
theorem ae_eq_of_tendstoInMeasure_sub_zero {α ι E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {l : Filter ι} [NeBot l] [IsCountablyGenerated l]
    {f f' : ι → α → E} {g g' : α → E} (hf : TendstoInMeasure μ f l g)
    (hf' : TendstoInMeasure μ f' l g')
    (hsub : TendstoInMeasure μ (fun i x ↦ f i x - f' i x) l (fun _ ↦ 0)) :
    g =ᵐ[μ] g' :=
  (tendstoInMeasure_ae_unique (hf.sub hf') hsub).mono fun _ h ↦ sub_eq_zero.mp h

end MeasureTheory
