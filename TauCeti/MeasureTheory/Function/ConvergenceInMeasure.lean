/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.Moments.Chebyshev

/-! # Convergence in measure: bounds and continuous transformations

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

Pairing preserves convergence in measure along arbitrary filters and for arbitrary measures.
On finite measure spaces, continuous transformations preserve convergence along arbitrary
filters whenever the transformed functions are eventually almost everywhere strongly
measurable.

## Main results

* `MeasureTheory.tendstoInMeasure_of_tendsto_integral_norm_sq`: convergence in mean square
  implies convergence in measure for any measure and filter.
* `Topology.IsInducing.tendsto_measure_notMem_nhds_iff`: convergence in measure to a constant
  can be checked on a family of metric-valued tests inducing the topology, even when the
  measure spaces vary with the index.
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
* `MeasureTheory.TendstoInMeasure.prodMk`: convergence in measure of paired functions,
  for arbitrary measures and filters, without measurability assumptions.
* `MeasureTheory.TendstoInMeasure.continuous_comp`: continuous unary transformations on
  finite measure spaces along arbitrary filters.
* `MeasureTheory.TendstoInMeasure.continuous_comp₂`: the corresponding binary transformation
  theorem, obtained by pairing and unary composition.

## Source

The high-probability rate lemmas are adapted from the Davis--Kahan/DKPS formalization,
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

namespace MeasureTheory.TendstoInMeasure

open Filter
open scoped Topology ENNReal

/-- Pairing functions preserves convergence in measure, without measurability or finiteness
assumptions on the measure, and along an arbitrary filter. -/
theorem prodMk {α ι E₁ E₂ : Type*} [MeasurableSpace α] {μ : Measure α}
    [PseudoEMetricSpace E₁] [PseudoEMetricSpace E₂] {l : Filter ι}
    {f₁ : ι → α → E₁} {f₂ : ι → α → E₂} {g₁ : α → E₁} {g₂ : α → E₂}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i x ↦ (f₁ i x, f₂ i x)) l (fun x ↦ (g₁ x, g₂ x)) := by
  intro ε hε
  have hsum := (h₁ ε hε).add (h₂ ε hε)
  rw [zero_add] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun i ↦ ?_
  simpa only [Prod.edist_eq, le_max_iff, Set.ofPred_or] using
    measure_union_le {x | ε ≤ edist (f₁ i x) (g₁ x)} {x | ε ≤ edist (f₂ i x) (g₂ x)}

/-- A continuous transformation preserves convergence in measure on a finite measure space
along an arbitrary filter, provided the transformed functions are eventually almost everywhere
strongly measurable. The transformation need not be uniformly continuous or bounded. -/
theorem continuous_comp {α ι E₁ E₂ : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [PseudoEMetricSpace E₁] [PseudoEMetricSpace E₂]
    {l : Filter ι} {f : ι → α → E₁} {g : α → E₁}
    (h : TendstoInMeasure μ f l g) {φ : E₁ → E₂} (hφ : Continuous φ)
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (fun x ↦ φ (f i x)) μ) :
    TendstoInMeasure μ (fun i x ↦ φ (f i x)) l (fun x ↦ φ (g x)) := by
  classical
  rw [tendstoInMeasure_iff_tendsto_toNNReal]
  intro ε hε
  by_contra hbad
  obtain ⟨s, hs, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hbad
  obtain ⟨δ, hδ, hsub⟩ := NNReal.nhds_zero_basis.mem_iff.1 hs
  let r : ℕ → ℝ≥0∞ := fun n ↦ (2⁻¹ : ℝ≥0∞) ^ n
  have hr : Tendsto r atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hselect (n : ℕ) : ∃ i, AEStronglyMeasurable (fun x ↦ φ (f i x)) μ ∧
      μ {x | r n ≤ edist (f i x) (g x)} ≤ r n ∧
      δ ≤ (μ {x | ε ≤ edist (φ (f i x)) (φ (g x))}).toNNReal := by
    have hrpos : 0 < r n := ENNReal.pow_pos (by norm_num) _
    have hevent := (h (r n) hrpos).eventually (gt_mem_nhds hrpos)
    obtain ⟨i, hi, hfi, hri⟩ := (hfreq.and_eventually (hf.and hevent)).exists
    exact ⟨i, hfi, hri.le, Set.notMem_Iio.1 (Set.notMem_subset hsub hi)⟩
  choose ns hmeas hbound hbadbound using hselect
  have hseq : TendstoInMeasure μ (fun n ↦ f (ns n)) atTop g := by
    apply TauCeti.tendstoInMeasure_of_tendsto_measure_rate_lt_edist hr
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr (fun _ ↦ zero_le)
    intro n
    exact (measure_mono (s := {x | r n < edist (f (ns n) x) (g x)})
      (fun x hx ↦ show r n ≤ edist (f (ns n) x) (g x) from le_of_lt hx)).trans (hbound n)
  obtain ⟨ks, _, hlim⟩ := hseq.exists_seq_tendsto_ae
  have hcomp := tendstoInMeasure_of_tendsto_ae (fun n ↦ hmeas (ks n))
    (hlim.mono fun x hx ↦ (hφ.tendsto (g x)).comp hx)
  have hzero := tendstoInMeasure_iff_tendsto_toNNReal.mp hcomp ε hε
  exact (not_lt_of_ge (ge_of_tendsto' hzero (fun n ↦ hbadbound (ks n)))) hδ

/-- A continuous binary transformation preserves convergence in measure on a finite measure
space along an arbitrary filter, provided the transformed functions are eventually
almost everywhere strongly measurable. -/
theorem continuous_comp₂ {α ι E₁ E₂ E₃ : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [PseudoEMetricSpace E₁] [PseudoEMetricSpace E₂]
    [PseudoEMetricSpace E₃] {l : Filter ι}
    {f₁ : ι → α → E₁} {f₂ : ι → α → E₂} {g₁ : α → E₁} {g₂ : α → E₂}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂)
    {φ : E₁ → E₂ → E₃} (hφ : Continuous (Function.uncurry φ))
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (fun x ↦ φ (f₁ i x) (f₂ i x)) μ) :
    TendstoInMeasure μ (fun i x ↦ φ (f₁ i x) (f₂ i x)) l
      (fun x ↦ φ (g₁ x) (g₂ x)) :=
  (h₁.prodMk h₂).continuous_comp hφ hf

end MeasureTheory.TendstoInMeasure

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

namespace Topology.IsInducing

open Filter MeasureTheory Set
open scoped Topology

/-- For a family of tests inducing the topology, convergence in measure to a constant is
equivalent to convergence of each test. The sample spaces and measures may vary, and the
filter is arbitrary. No measurability is needed because the statement uses outer measures. -/
theorem tendsto_measure_notMem_nhds_iff {X J E ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace E] {T : X → J → E} (hT : IsInducing T)
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (P : (i : ι) → Measure (Ω i))
    (Y : (i : ι) → Ω i → X) (l : Filter ι) (x : X) :
    (∀ U ∈ 𝓝 x, Tendsto (fun i ↦ P i {ω | Y i ω ∉ U}) l (𝓝 0)) ↔
      ∀ j ε, 0 < ε →
        Tendsto (fun i ↦ P i {ω | ε ≤ dist (T (Y i ω) j) (T x j)}) l (𝓝 0) := by
  classical
  constructor
  · intro h j ε hε
    have hU : {y | dist (T y j) (T x j) < ε} ∈ 𝓝 x :=
      ((continuous_apply j).comp hT.continuous).continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hε)
    simpa only [mem_ofPred_eq, not_lt] using h _ hU
  · intro h U hU
    rw [hT.nhds_eq_comap] at hU
    obtain ⟨V, hV, hVU⟩ := mem_comap.1 hU
    rw [nhds_pi, Filter.mem_pi'] at hV
    obtain ⟨s, W, hW, hWV⟩ := hV
    choose δ hδ hδW using fun j ↦ Metric.mem_nhds_iff.1 (hW j)
    have hlim : Tendsto
        (fun i ↦ ∑ j ∈ s, P i {ω | δ j ≤ dist (T (Y i ω) j) (T x j)}) l (𝓝 0) := by
      simpa using tendsto_finsetSum s (fun j _ ↦ h j (δ j) (hδ j))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ zero_le) fun i ↦ ?_
    refine (measure_mono ?_).trans (measure_biUnion_finset_le s _)
    intro ω hω
    simp only [mem_iUnion, mem_ofPred_eq]
    by_contra! hgood
    apply hω
    apply hVU
    apply hWV
    intro j hj
    exact hδW j (hgood j hj)

end Topology.IsInducing
