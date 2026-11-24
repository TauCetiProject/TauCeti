/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.MeasureTheory.OuterMeasure.AE
import TauCeti.Probability.Moments.Chebyshev

/-! # Convergence in measure: bounds, continuous transformations, and algebraic operations

A standard way to consume concentration inequalities: if for each index `i` the
deviation `edist (f i x) (g x)` exceeds some deterministic `rate i` only on a
set of small measure, and `rate` tends to `0`, then `f` tends to `g` in
measure.  This is how "with high probability, the error is at most `rate i`"
statements are converted into `MeasureTheory.TendstoInMeasure`.

No measurability is required of the exceptional sets, since the squeeze only
uses monotonicity of the (outer) measure; the index runs along an arbitrary
filter, matching the generality of `MeasureTheory.TendstoInMeasure`.

Convergence in mean absolute norm implies vanishing tail measures even when the measure spaces
vary with the index. Convergence in mean square implies convergence in measure, with
integrability of the squared deviations required only eventually along the filter. Chebyshev-type
bounds with an auxiliary truncation level give measures tending to zero. Real functions tending to
zero in measure have upper tails of measure tending to zero.

This file also develops continuous and algebraic stability of `MeasureTheory.TendstoInMeasure`:
* Pairing (`TendstoInMeasure.prodMk`), uniformly continuous unary and binary maps
  (`TendstoInMeasure.uniformContinuous_comp`, `TendstoInMeasure.uniformContinuous₂_comp`), and
  uniform-group and constant-scalar operations (`add`, `neg`, `sub`, `const_smul`) preserve
  convergence in measure along arbitrary filters on arbitrary measure spaces without measurability
  hypotheses.
* On finite measure spaces, continuous unary and binary transformations preserve convergence along
  arbitrary filters whenever the transformed functions are eventually almost everywhere strongly
  measurable (`TendstoInMeasure.continuous_comp`, `TendstoInMeasure.continuous_comp₂`).
* On finite measure spaces, almost-everywhere strongly measurable functions are tight in distance
  (`MeasureTheory.tendsto_measure_dist_ge_atTop`), so bounded scalar multiplication
  (`TendstoInMeasure.smul`, `Filter.Tendsto.smul_tendstoInMeasure`) and bounded multiplication
  (`TendstoInMeasure.mul`) preserve convergence in measure along an arbitrary filter when the
  limits are almost-everywhere strongly measurable (without measurability assumptions on the
  approximating families).

## Main results

* `MeasureTheory.tendstoInMeasure_of_tendsto_integral_norm_sq`: convergence in mean square
  implies convergence in measure for any measure and filter.
* `MeasureTheory.exists_subseq_ae_tendsto_of_tendsto_integral_norm_sub_sq`: a sequence converging
  in mean square has an almost everywhere convergent subsequence.
* `MeasureTheory.ae_le_of_tendsto_integral_norm_sub_sq`: almost everywhere bounds
  `φ x (f n x) ≤ c n`, for continuous `φ x`, pass to the limit in mean square.
* `MeasureTheory.tendsto_measure_of_subset_biUnion_finset`: an event covered by finitely many
  events of vanishing measure has vanishing measure, along any filter and on varying spaces.
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
* `MeasureTheory.TendstoInMeasure.continuousAt_const_comp`: local continuous mapping at a constant
  limit, without finiteness or measurability assumptions.
* `MeasureTheory.TendstoInMeasure.uniformContinuous_comp` and
  `MeasureTheory.TendstoInMeasure.uniformContinuous₂_comp`: post-composition with uniformly
  continuous unary and binary maps on arbitrary measure spaces.
* `MeasureTheory.TendstoInMeasure.add`, `neg`, `sub`, `const_smul`: uniform-group
  and constant scalar operations on arbitrary measure spaces.
* `MeasureTheory.TendstoInMeasure.of_edist_le_on`,
  `MeasureTheory.TendstoInMeasure.zero_of_norm_le_on`, and
  `MeasureTheory.TendstoInMeasure.zero_of_norm_le_on_prob`: domination on events whose complements
  have vanishing measure.
* `MeasureTheory.tendsto_measure_compl_zero_of_tendsto_one`: eventually null-measurable events
  whose probabilities tend to `1` have complements of measure tending to `0`.
* `MeasureTheory.tendstoInMeasure_iff_measureReal_lt_dist`: strict-distance characterization
  for finite measures.
* `MeasureTheory.tendsto_measure_dist_ge_atTop`: distance tightness of almost-everywhere strongly
  measurable functions on finite measure spaces.
* `MeasureTheory.TendstoInMeasure.smul`, `Filter.Tendsto.smul_tendstoInMeasure`, and
  `MeasureTheory.TendstoInMeasure.mul`: joint bounded scalar multiplication and multiplication on
  finite measure spaces.

## Source

The high-probability rate lemmas in `namespace TauCeti` are adapted from the Davis--Kahan/DKPS
formalization, `ForMathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` at `fc38eb4`,
by Claude Fable 5 (Kitware, Inc., Apache-2.0).
-/

public section

namespace MeasureTheory

open Filter
open scoped ENNReal Topology

/-- For eventually null-measurable events of probability tending to `1`, the complements have
measure tending to `0`. -/
theorem tendsto_measure_compl_zero_of_tendsto_one {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {l : Filter ι} {A : ι → Set α}
    (hmeas : ∀ᶠ i in l, NullMeasurableSet (A i) μ)
    (hA : Tendsto (fun i ↦ μ (A i)) l (𝓝 1)) :
    Tendsto (fun i ↦ μ (A i)ᶜ) l (𝓝 0) := by
  have h := ENNReal.Tendsto.sub tendsto_const_nhds hA (Or.inl ENNReal.one_ne_top)
  rw [tsub_self] at h
  refine h.congr' ?_
  filter_upwards [hmeas] with i hi
  exact (prob_compl_eq_one_sub₀ hi).symm

end MeasureTheory

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
  simpa only [Set.compl_ofPred, not_le] using tendsto_measure_compl_zero_of_tendsto_one hmeas hprob

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
    have hsubset : {x | r n < edist (f (ns n) x) (g x)} ⊆
        {x | r n ≤ edist (f (ns n) x) (g x)} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      exact le_of_lt hx
    exact (measure_mono hsubset).trans (hbound n)
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

/-- A map continuous at a constant `c` preserves convergence in measure to `c`, for any measure and
filter, with no measurability or finiteness assumptions. -/
theorem continuousAt_const_comp {α ι E₁ E₂ : Type*} [MeasurableSpace α] {μ : Measure α}
    [PseudoEMetricSpace E₁] [PseudoEMetricSpace E₂] {l : Filter ι} {f : ι → α → E₁} {c : E₁}
    (h : TendstoInMeasure μ f l (fun _ ↦ c)) {φ : E₁ → E₂} (hφ : ContinuousAt φ c) :
    TendstoInMeasure μ (fun i x ↦ φ (f i x)) l (fun _ ↦ φ c) := by
  intro ε hε
  obtain ⟨δ, hδ, hδ_le⟩ := EMetric.continuousAt_iff.1 hφ ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ ↦ zero_le) fun i ↦ measure_mono fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq] at hx ⊢
  by_contra! hlt
  exact not_le_of_gt (hδ_le hlt) hx

/-- If `edist (g i x) (g₀ x) ≤ edist (f i x) (f₀ x)` on events `A i` whose complements have
measure tending to `0`, and `f → f₀` in measure, then `g → g₀` in measure. -/
theorem of_edist_le_on {α ι E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [EDist E] [EDist F] {l : Filter ι} {f : ι → α → E} {f₀ : α → E}
    {g : ι → α → F} {g₀ : α → F} {A : ι → Set α}
    (hf : TendstoInMeasure μ f l f₀) (hA : Tendsto (fun i ↦ μ (A i)ᶜ) l (𝓝 0))
    (hle : ∀ᶠ i in l, ∀ x ∈ A i, edist (g i x) (g₀ x) ≤ edist (f i x) (f₀ x)) :
    TendstoInMeasure μ g l g₀ := by
  intro ε hε
  have hsum := (hf ε hε).add hA
  rw [zero_add] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hle] with i hi
  refine (measure_mono fun x hx ↦ ?_).trans
    (measure_union_le {x | ε ≤ edist (f i x) (f₀ x)} (A i)ᶜ)
  by_cases hxA : x ∈ A i
  · exact Or.inl ((Set.mem_ofPred_eq.mp hx).trans (hi x hxA))
  · exact Or.inr hxA

/-- If `‖g i x‖ ≤ ‖f i x‖` on events `A i` whose complements have measure tending to `0`, and
`f → 0` in measure, then `g → 0` in measure. -/
theorem zero_of_norm_le_on {α ι E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [SeminormedAddGroup E] [SeminormedAddGroup F] {l : Filter ι}
    {f : ι → α → E} {g : ι → α → F} {A : ι → Set α}
    (hf : TendstoInMeasure μ f l (fun _ ↦ 0)) (hA : Tendsto (fun i ↦ μ (A i)ᶜ) l (𝓝 0))
    (hle : ∀ᶠ i in l, ∀ x ∈ A i, ‖g i x‖ ≤ ‖f i x‖) :
    TendstoInMeasure μ g l (fun _ ↦ 0) := by
  refine hf.of_edist_le_on hA ?_
  filter_upwards [hle] with i hi x hx
  simpa only [edist_dist, dist_zero_right] using ENNReal.ofReal_le_ofReal (hi x hx)

/-- If `‖g i x‖ ≤ ‖f i x‖` on eventually null-measurable events `A i` of probability tending to `1`,
and `f → 0` in probability, then `g → 0` in probability. -/
theorem zero_of_norm_le_on_prob {α ι E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] [SeminormedAddGroup E] [SeminormedAddGroup F]
    {l : Filter ι} {f : ι → α → E} {g : ι → α → F} {A : ι → Set α}
    (hf : TendstoInMeasure μ f l (fun _ ↦ 0))
    (hmeas : ∀ᶠ i in l, NullMeasurableSet (A i) μ)
    (hA : Tendsto (fun i ↦ μ (A i)) l (𝓝 1))
    (hle : ∀ᶠ i in l, ∀ x ∈ A i, ‖g i x‖ ≤ ‖f i x‖) :
    TendstoInMeasure μ g l (fun _ ↦ 0) := by
  exact hf.zero_of_norm_le_on (tendsto_measure_compl_zero_of_tendsto_one hmeas hA) hle

end MeasureTheory.TendstoInMeasure

namespace MeasureTheory

open Filter Topology
open scoped ENNReal

/-- For a finite measure, convergence in measure is equivalent to `μ.real {ε < dist (f i) g} → 0`
for every `ε > 0`. -/
theorem tendstoInMeasure_iff_measureReal_lt_dist {α ι E : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [PseudoMetricSpace E] {l : Filter ι} {f : ι → α → E} {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε > 0, Tendsto (fun i ↦ μ.real {x | ε < dist (f i x) (g x)}) l (𝓝 0) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
      (fun _ ↦ measureReal_nonneg) fun i ↦
      measureReal_mono fun x (hx : ε < dist (f i x) (g x)) ↦ le_of_lt hx
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h (ε / 2) (half_pos hε))
      (fun _ ↦ measureReal_nonneg) fun i ↦
      measureReal_mono fun x (hx : ε ≤ dist (f i x) (g x)) ↦ (half_lt_self hε).trans_le hx

/-- Sectionwise convergence in measure almost everywhere implies convergence in measure on a
product of two finite measures if the distances to the limit are eventually jointly measurable. -/
theorem tendstoInMeasure_prod_of_ae_tendstoInMeasure
    {α β E ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [EDist E]
    {μ : Measure α} {ν : Measure β} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {l : Filter ι} [l.IsCountablyGenerated] {f : ι → α × β → E} {g : α × β → E}
    (hf : ∀ᶠ i in l, Measurable (fun p ↦ edist (f i p) (g p)))
    (h : ∀ᵐ x ∂μ, TendstoInMeasure ν (fun n y ↦ f n (x, y)) l (fun y ↦ g (x, y))) :
    TendstoInMeasure (μ.prod ν) f l g := by
  intro ε hε
  let s (n : ι) := {p | ε ≤ edist (f n p) (g p)}
  have hs : ∀ᶠ i in l, MeasurableSet (s i) :=
    hf.mono fun _ hi ↦ measurableSet_le measurable_const hi
  refine Tendsto.congr' (hs.mono fun _ hi ↦ (Measure.prod_apply hi).symm) ?_
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ ν (Prod.mk x ⁻¹' s n)) l (𝓝 0) :=
    h.mono fun x hx ↦ hx ε hε
  simpa only [lintegral_zero] using tendsto_lintegral_filter_of_dominated_convergence
    (fun _ ↦ ν Set.univ) (hs.mono fun _ hi ↦ measurable_measure_prodMk_left hi)
    (Eventually.of_forall fun _ ↦ ae_of_all _ fun _ ↦ measure_mono (Set.subset_univ _))
    (by rw [lintegral_const]; finiteness) hlim

/-- If the mean norms tend to zero, every positive norm tail has vanishing measure, even
on varying measure spaces. Integrability of the norms is only needed eventually. -/
theorem tendsto_measure_norm_ge_of_tendsto_integral_norm {ι E : Type*}
    [SeminormedAddCommGroup E]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] {μ : ∀ i, Measure (Ω i)}
    {l : Filter ι} {f : ∀ i, Ω i → E}
    (hint : ∀ᶠ i in l, Integrable (fun ω ↦ ‖f i ω‖) (μ i))
    (hlim : Tendsto (fun i ↦ ∫ ω, ‖f i ω‖ ∂μ i) l (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i ↦ μ i {ω | ε ≤ ‖f i ω‖}) l (𝓝 0) := by
  have hupper := ENNReal.tendsto_ofReal (hlim.div_const ε)
  simp only [zero_div, ENNReal.ofReal_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hint] with i hi
  have hMarkov := meas_ge_le_lintegral_div hi.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top
  rw [← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun ω ↦ norm_nonneg (f i ω)),
    ← ENNReal.ofReal_div_of_pos hε] at hMarkov
  simpa only [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] using hMarkov

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
  exact TauCeti.meas_ge_le_integral_sq_div_sq hk hε

/-- **Convergence in mean square gives an almost everywhere convergent subsequence.** If
`‖f n - g‖²` is eventually integrable and `∫ ‖f n - g‖² → 0`, then a subsequence of `f n`
converges to `g` almost everywhere. -/
theorem exists_subseq_ae_tendsto_of_tendsto_integral_norm_sub_sq {α E : Type*}
    [MeasurableSpace α] {μ : Measure α} [SeminormedAddCommGroup E] {f : ℕ → α → E} {g : α → E}
    (hint : ∀ᶠ n in atTop, Integrable (fun x ↦ ‖f n x - g x‖ ^ 2) μ)
    (h : Tendsto (fun n ↦ ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Tendsto (fun k ↦ f (ns k) x) atTop (𝓝 (g x)) :=
  (tendstoInMeasure_of_tendsto_integral_norm_sq hint h).exists_seq_tendsto_ae

/-- **Pointwise bounds pass to limits in mean square.** If `‖f n - g‖²` is eventually integrable
and `∫ ‖f n - g‖² → 0`, each `φ x` is continuous and `φ x (f n x) ≤ c n` almost everywhere with
`c n → M`, then `φ x (g x) ≤ M` almost everywhere. -/
theorem ae_le_of_tendsto_integral_norm_sub_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [SeminormedAddCommGroup E] {f : ℕ → α → E} {g : α → E} {φ : α → E → ℝ} {c : ℕ → ℝ} {M : ℝ}
    (hint : ∀ᶠ n in atTop, Integrable (fun x ↦ ‖f n x - g x‖ ^ 2) μ)
    (h : Tendsto (fun n ↦ ∫ x, ‖f n x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) (hφ : ∀ x, Continuous (φ x))
    (hc : Tendsto c atTop (𝓝 M)) (hle : ∀ n, ∀ᵐ x ∂μ, φ x (f n x) ≤ c n) :
    ∀ᵐ x ∂μ, φ x (g x) ≤ M := by
  obtain ⟨ns, hns, hlim⟩ := exists_subseq_ae_tendsto_of_tendsto_integral_norm_sub_sq hint h
  exact TauCeti.ae_le_of_tendsto_of_tendsto_of_frequently (F₂ := fun k _ ↦ c (ns k))
    (G₂ := fun _ ↦ M) (hlim.mono fun x hx ↦ ((hφ x).tendsto (g x)).comp hx)
    (Eventually.of_forall fun _ ↦ hc.comp hns.tendsto_atTop)
    (Eventually.of_forall fun k ↦ hle (ns k)).frequently

section Algebra

variable {α ι 𝕜 E E₁ E₂ F R : Type*} {m : MeasurableSpace α} {μ : Measure α} {l : Filter ι}

/-- A constant family of functions converges in measure to itself along any filter. -/
theorem tendstoInMeasure_const [PseudoEMetricSpace E] (g : α → E) :
    TendstoInMeasure μ (fun _ : ι ↦ g) l g := by
  intro ε hε
  simpa [edist_self, hε.ne'] using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))

/-- A deterministic family `c : ι → E` converging to `c₀` in `E` converges to the constant
function `fun _ ↦ c₀` in measure on any measure space. -/
theorem _root_.Filter.Tendsto.tendstoInMeasure_const [PseudoEMetricSpace E]
    {c : ι → E} {c₀ : E} (hc : Tendsto c l (𝓝 c₀)) :
    TendstoInMeasure μ (fun i _ ↦ c i) l (fun _ ↦ c₀) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_const_nhds
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [EMetric.tendsto_nhds.mp hc ε hε] with i hi
  simp [hi.not_ge]

/-- Post-composing with a uniformly continuous map preserves convergence in measure on any
measure space, without measurability hypotheses. -/
theorem TendstoInMeasure.uniformContinuous_comp [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {Φ : E → F} (hΦ : UniformContinuous Φ) {f : ι → α → E} {g : α → E}
    (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i x ↦ Φ (f i x)) l (fun x ↦ Φ (g x)) := by
  intro ε hε
  obtain ⟨δ, hδ, hΦδ⟩ := EMetric.uniformContinuous_iff.mp hΦ ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf δ hδ)
    (fun _ ↦ zero_le) fun i ↦ measure_mono fun x hx ↦ ?_
  rw [Set.mem_ofPred_eq] at hx ⊢
  by_contra! hlt
  exact hx.not_gt (hΦδ hlt)

/-- Combining two families that converge in measure via a uniformly continuous binary operation
preserves convergence in measure on any measure space, without measurability hypotheses. -/
theorem TendstoInMeasure.uniformContinuous₂_comp [PseudoEMetricSpace E₁] [PseudoEMetricSpace E₂]
    [PseudoEMetricSpace F] {Ψ : E₁ → E₂ → F} (hΨ : UniformContinuous₂ Ψ)
    {f₁ : ι → α → E₁} {g₁ : α → E₁} {f₂ : ι → α → E₂} {g₂ : α → E₂}
    (hf₁ : TendstoInMeasure μ f₁ l g₁) (hf₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i x ↦ Ψ (f₁ i x) (f₂ i x)) l (fun x ↦ Ψ (g₁ x) (g₂ x)) :=
  (hf₁.prodMk hf₂).uniformContinuous_comp hΨ

/-- Pointwise addition preserves convergence in measure in any uniform additive group and on
any measure space. -/
theorem TendstoInMeasure.add [AddGroup E] [PseudoEMetricSpace E] [IsUniformAddGroup E]
    {f₁ f₂ : ι → α → E} {g₁ g₂ : α → E}
    (hf₁ : TendstoInMeasure μ f₁ l g₁) (hf₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i x ↦ f₁ i x + f₂ i x) l (fun x ↦ g₁ x + g₂ x) :=
  hf₁.uniformContinuous₂_comp uniformContinuous_add hf₂

/-- Pointwise negation preserves convergence in measure in any uniform additive group and on
any measure space. -/
theorem TendstoInMeasure.neg [AddGroup E] [PseudoEMetricSpace E] [IsUniformAddGroup E]
    {f : ι → α → E} {g : α → E} (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i x ↦ -f i x) l (fun x ↦ -g x) :=
  hf.uniformContinuous_comp uniformContinuous_neg

/-- Pointwise subtraction preserves convergence in measure in any uniform additive group and on
any measure space. -/
theorem TendstoInMeasure.sub [AddGroup E] [PseudoEMetricSpace E] [IsUniformAddGroup E]
    {f₁ f₂ : ι → α → E} {g₁ g₂ : α → E}
    (hf₁ : TendstoInMeasure μ f₁ l g₁) (hf₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i x ↦ f₁ i x - f₂ i x) l (fun x ↦ g₁ x - g₂ x) :=
  hf₁.uniformContinuous₂_comp uniformContinuous_sub hf₂

/-- Pointwise multiplication by a fixed scalar preserves convergence in measure whenever
constant scalar multiplication is uniformly continuous, on any measure space. -/
theorem TendstoInMeasure.const_smul [SMul 𝕜 E] [PseudoEMetricSpace E]
    [UniformContinuousConstSMul 𝕜 E] {f : ι → α → E} {g : α → E}
    (hf : TendstoInMeasure μ f l g) (c : 𝕜) :
    TendstoInMeasure μ (fun i x ↦ c • f i x) l (fun x ↦ c • g x) :=
  hf.uniformContinuous_comp (uniformContinuous_const_smul c)

/-- On a finite measure space, the measure of `{x | r ≤ dist (g x) y₀}` tends to `0` as
`r → ∞` for every almost-everywhere strongly measurable function `g`. Both finiteness of `μ`
and measurability of `g` are essential. -/
theorem tendsto_measure_dist_ge_atTop [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {g : α → E} (hg : AEStronglyMeasurable g μ) (y₀ : E) :
    Tendsto (fun r : ℝ ↦ μ {x | r ≤ dist (g x) y₀}) atTop (𝓝 0) := by
  let g' : α → E := hg.mk g
  have hmeas : ∀ r : ℝ, MeasurableSet {x | r ≤ dist (g' x) y₀} := fun r ↦
    measurableSet_le measurable_const
      (hg.stronglyMeasurable_mk.dist stronglyMeasurable_const).measurable
  have hanti : Antitone (fun r : ℝ ↦ {x | r ≤ dist (g' x) y₀}) := fun r s hrs x hx ↦ by
    rw [Set.mem_ofPred_eq] at hx ⊢
    exact hrs.trans hx
  have hinter : (⋂ r : ℝ, {x | r ≤ dist (g' x) y₀}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    exact exists_gt (dist (g' x) y₀)
  have hlim := tendsto_measure_iInter_atTop (fun r ↦ (hmeas r).nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  rw [hinter, measure_empty] at hlim
  refine hlim.congr fun r ↦ measure_congr ?_
  filter_upwards [hg.ae_eq_mk] with x hx
  simp [g', hx]

/-- Deterministic four-tail deviation estimate for a binary map uniformly continuous on a ball:
outside the two cutoff tails for the limit pair `(g₁, g₂)` and the two proximity tails for
`(f₁, g₁)` and `(f₂, g₂)`, both pairs lie in `Metric.ball (y₁, y₂) (M + r)` at distance `< δ₀`,
so the output deviation is `< ε`. -/
private theorem measure_dist_ge_le_of_ball_bound [PseudoMetricSpace E₁] [PseudoMetricSpace E₂]
    [PseudoMetricSpace F] {Ψ : E₁ × E₂ → F} {y₁ : E₁} {y₂ : E₂} {M r ε δ₀ δ : ℝ}
    (hδ₀ : δ ≤ δ₀) (hδr : δ ≤ r)
    (huc : ∀ p ∈ Metric.ball (y₁, y₂) (M + r), ∀ q ∈ Metric.ball (y₁, y₂) (M + r),
      dist p q < δ₀ → dist (Ψ p) (Ψ q) < ε)
    (f₁ g₁ : α → E₁) (f₂ g₂ : α → E₂) :
    μ {x | ε ≤ dist (Ψ (f₁ x, f₂ x)) (Ψ (g₁ x, g₂ x))} ≤
      (μ {x | M ≤ dist (g₁ x) y₁} + μ {x | M ≤ dist (g₂ x) y₂}) +
        (μ {x | δ ≤ dist (f₁ x) (g₁ x)} + μ {x | δ ≤ dist (f₂ x) (g₂ x)}) := by
  have hsub : {x | ε ≤ dist (Ψ (f₁ x, f₂ x)) (Ψ (g₁ x, g₂ x))} ⊆
      ({x | M ≤ dist (g₁ x) y₁} ∪ {x | M ≤ dist (g₂ x) y₂}) ∪
      ({x | δ ≤ dist (f₁ x) (g₁ x)} ∪ {x | δ ≤ dist (f₂ x) (g₂ x)}) := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    rcases hnot with ⟨⟨hg₁, hg₂⟩, ⟨hf₁, hf₂⟩⟩
    have hr : 0 < r := (dist_nonneg.trans_lt hf₁).trans_le hδr
    have hp₁ : (f₁ x, f₂ x) ∈ Metric.ball (y₁, y₂) (M + r) := by
      simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨(dist_triangle (f₁ x) (g₁ x) y₁).trans_lt (by linarith),
        (dist_triangle (f₂ x) (g₂ x) y₂).trans_lt (by linarith)⟩
    have hp₀ : (g₁ x, g₂ x) ∈ Metric.ball (y₁, y₂) (M + r) := by
      simp only [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      exact ⟨by linarith, by linarith⟩
    have hp_dist : dist (f₁ x, f₂ x) (g₁ x, g₂ x) < δ₀ :=
      (max_lt hf₁ hf₂).trans_le hδ₀
    exact hx.not_gt (huc (f₁ x, f₂ x) hp₁ (g₁ x, g₂ x) hp₀ hp_dist)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) (measure_union_le _ _)))

/-- On a finite measure space, bounded scalar multiplication preserves convergence in measure
jointly in the scalar and vector families along any filter, provided both limit functions are
almost-everywhere strongly measurable. -/
theorem TendstoInMeasure.smul [Zero 𝕜] [Zero E] [PseudoMetricSpace 𝕜] [PseudoMetricSpace E]
    [SMul 𝕜 E] [IsBoundedSMul 𝕜 E] [IsFiniteMeasure μ]
    {c : ι → α → 𝕜} {c₀ : α → 𝕜} {f : ι → α → E} {g : α → E}
    (hc₀ : AEStronglyMeasurable c₀ μ) (hg : AEStronglyMeasurable g μ)
    (hc : TendstoInMeasure μ c l c₀) (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i x ↦ c i x • f i x) l (fun x ↦ c₀ x • g x) := by
  rw [tendstoInMeasure_iff_dist] at hc hf ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.div_pos hη.ne' ENNReal.ofNat_ne_top
  have hη4 : 0 < η / 2 / 2 := ENNReal.div_pos hη2.ne' ENNReal.ofNat_ne_top
  -- Use tightness of the limit functions to confine `(c₀, g)` to a bounded ball up to `η / 2`.
  obtain ⟨N₁, hN₁⟩ := ENNReal.tendsto_atTop_zero.mp
    (tendsto_measure_dist_ge_atTop hc₀ 0) (η / 2 / 2) hη4
  obtain ⟨N₂, hN₂⟩ := ENNReal.tendsto_atTop_zero.mp
    (tendsto_measure_dist_ge_atTop hg 0) (η / 2 / 2) hη4
  let M : ℝ := max N₁ N₂
  have hMc₀ : μ {x | M ≤ dist (c₀ x) 0} ≤ η / 2 / 2 := hN₁ M (le_max_left _ _)
  have hMg : μ {x | M ≤ dist (g x) 0} ≤ η / 2 / 2 := hN₂ M (le_max_right _ _)
  -- Bounded scalar multiplication is uniformly continuous on the enlarged ball of radius `M + 1`.
  obtain ⟨δ₀, hδ₀, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (Metric.isBounded_ball (x := (0 : 𝕜 × E)) (r := M + 1)).uniformContinuousOn_smul ε hε
  let δ : ℝ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  -- Apply the four-tail measure bound once `c i` and `f i` are within `δ` of their limits.
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp (hc δ hδ)) (η / 2 / 2) hη4,
    (ENNReal.tendsto_nhds_zero.mp (hf δ hδ)) (η / 2 / 2) hη4] with i hic hif
  calc μ {x | ε ≤ dist (c i x • f i x) (c₀ x • g x)}
      ≤ (μ {x | M ≤ dist (c₀ x) 0} + μ {x | M ≤ dist (g x) 0}) +
          (μ {x | δ ≤ dist (c i x) (c₀ x)} + μ {x | δ ≤ dist (f i x) (g x)}) :=
        measure_dist_ge_le_of_ball_bound (Ψ := fun p : 𝕜 × E ↦ p.1 • p.2)
          (min_le_left δ₀ 1) (min_le_right δ₀ 1) huc (c i) c₀ (f i) g
    _ ≤ (η / 2 / 2 + η / 2 / 2) + (η / 2 / 2 + η / 2 / 2) :=
        add_le_add (add_le_add hMc₀ hMg) (add_le_add hic hif)
    _ = η := by simp only [ENNReal.add_halves]

/-- On a finite measure space, multiplying by a deterministic scalar family `c i → c₀`
preserves convergence in measure when the limit function is almost-everywhere strongly
measurable. -/
theorem _root_.Filter.Tendsto.smul_tendstoInMeasure [Zero 𝕜] [Zero E] [PseudoMetricSpace 𝕜]
    [PseudoMetricSpace E] [SMul 𝕜 E] [IsBoundedSMul 𝕜 E] [IsFiniteMeasure μ]
    {c : ι → 𝕜} {c₀ : 𝕜} {f : ι → α → E} {g : α → E}
    (hc : Tendsto c l (𝓝 c₀)) (hg : AEStronglyMeasurable g μ)
    (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i x ↦ c i • f i x) l (fun x ↦ c₀ • g x) :=
  hc.tendstoInMeasure_const.smul aestronglyMeasurable_const hg hf

/-- On a finite measure space, bounded pointwise multiplication preserves convergence in measure
along any filter when both limit functions are almost-everywhere strongly measurable. -/
theorem TendstoInMeasure.mul [Zero R] [Mul R] [PseudoMetricSpace R] [IsBoundedSMul R R]
    [IsFiniteMeasure μ] {f₁ f₂ : ι → α → R} {g₁ g₂ : α → R}
    (hg₁ : AEStronglyMeasurable g₁ μ) (hg₂ : AEStronglyMeasurable g₂ μ)
    (hf₁ : TendstoInMeasure μ f₁ l g₁) (hf₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i x ↦ f₁ i x * f₂ i x) l (fun x ↦ g₁ x * g₂ x) :=
  hf₁.smul hg₁ hg₂ hf₂

end Algebra

/-- **A finite union bound along a filter.** If each of finitely many events `A j i` has measure
tending to zero along `l` and every `B i` is covered by them, then `P i (B i)` tends to zero. The
sample spaces and measures may vary with the index, and no measurability is needed because the
statement uses outer measures. -/
theorem tendsto_measure_of_subset_biUnion_finset {ι J : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] {P : (i : ι) → Measure (Ω i)} {l : Filter ι} (s : Finset J)
    {A : J → (i : ι) → Set (Ω i)} {B : (i : ι) → Set (Ω i)}
    (hA : ∀ j ∈ s, Tendsto (fun i ↦ P i (A j i)) l (𝓝 0)) (hB : ∀ i, B i ⊆ ⋃ j ∈ s, A j i) :
    Tendsto (fun i ↦ P i (B i)) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using tendsto_finsetSum s hA) (fun _ ↦ zero_le) fun i ↦ ?_
  exact (measure_mono (hB i)).trans (measure_biUnion_finset_le s _)

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
    refine tendsto_measure_of_subset_biUnion_finset s (fun j _ ↦ h j (δ j) (hδ j))
      fun i ω hω ↦ ?_
    simp only [mem_iUnion, mem_ofPred_eq]
    by_contra! hgood
    exact hω (hVU (hWV fun j hj ↦ hδW j (hgood j hj)))

end Topology.IsInducing
