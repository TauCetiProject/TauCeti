/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.Moments.Chebyshev

/-! # Convergence in measure: bounds, continuous transformations, and uniform operations

A standard way to consume concentration inequalities: if for each index `i` the
deviation `edist (f i x) (g x)` exceeds some deterministic `rate i` only on a
set of small measure, and `rate` tends to `0`, then `f` tends to `g` in
measure.  This is how "with high probability, the error is at most `rate i`"
statements are converted into `MeasureTheory.TendstoInMeasure`.

No measurability is required of the exceptional sets, since the squeeze only
uses monotonicity of the (outer) measure; the index runs along an arbitrary
filter, matching the generality of `MeasureTheory.TendstoInMeasure`.

Convergence in mean square also implies convergence in measure, with integrability of the
squared deviations required only eventually along the filter. Likewise, convergence in measure
can be localized off a family of exceptional sets whose measures have infimum zero, and any
convergent deterministic family converges in measure as constant functions, again without
measurability or finiteness hypotheses.

Pairing, post-composition with uniformly continuous maps, uniform group operations, and
uniformly continuous constant scalar multiplication preserve convergence in measure along
arbitrary filters and for arbitrary measures, without measurability assumptions. On finite
measure spaces, continuous transformations also preserve convergence along arbitrary filters
whenever the transformed functions are eventually almost everywhere strongly measurable.

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
* `TauCeti.tendstoInMeasure_of_iInf_measure_eq_zero`: localize convergence in measure off a family
  of exceptional sets whose infimum measure vanishes (`⨅ m, μ (F m) = 0`), without measurability
  or finiteness assumptions.
* `TauCeti.tendstoInMeasure_const`: a family constant along a filter converges in measure to its
  value, without finiteness or measurability assumptions.
* `Filter.Tendsto.tendstoInMeasure_const`: a convergent deterministic family converges in measure
  as constant functions, without finiteness or measurability assumptions.
* `UniformContinuous.comp_tendstoInMeasure`: post-composing with a uniformly continuous map
  preserves convergence in measure without finiteness or measurability assumptions.
* `MeasureTheory.TendstoInMeasure.prodMk`: convergence in measure of paired functions,
  for arbitrary measures and filters, without measurability assumptions.
* `MeasureTheory.TendstoInMeasure.mul`, `MeasureTheory.TendstoInMeasure.add`: convergence in
  measure is closed under multiplication and addition in a uniform group.
* `MeasureTheory.TendstoInMeasure.const_smul`, `MeasureTheory.TendstoInMeasure.const_add`,
  `MeasureTheory.TendstoInMeasure.const_mul`: convergence in measure is closed under uniformly
  continuous constant scalar multiplication, vector addition, and left multiplication.
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

/-- **Localization of convergence in measure.** If a family of exceptional sets `F m` satisfies
`⨅ m, μ (F m) = 0`, and for each `m` a localized family `f_loc m` converges in measure to `g_loc m`
along `l` while dominating `edist (f k x) (g x)` almost everywhere off `F m` eventually along `l`,
then `f` converges in measure to `g` along `l`. No measurability of `F m` or finiteness of `μ` is
needed. -/
theorem tendstoInMeasure_of_iInf_measure_eq_zero {E' : Type*} {κ : Sort*} [EDist E] [EDist E']
    {f : ι → α → E} {g : α → E} {F : κ → Set α}
    {f_loc : κ → ι → α → E'} {g_loc : κ → α → E'}
    (hF : ⨅ m, μ (F m) = 0)
    (hlim : ∀ m, TendstoInMeasure μ (f_loc m) l (g_loc m))
    (hle : ∀ m, ∀ᶠ k in l, ∀ᵐ x ∂μ, x ∉ F m →
      edist (f k x) (g x) ≤ edist (f_loc m k x) (g_loc m x)) :
    TendstoInMeasure μ f l g := by
  intro ε hε
  refine ENNReal.tendsto_nhds_zero.2 fun η hη ↦ ?_
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  obtain ⟨m, hm⟩ : ∃ m, μ (F m) < η / 2 := iInf_lt_iff.1 (hF.symm ▸ hη2)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (hlim m ε hε) (η / 2) hη2, hle m] with k hkm hlek
  have hsub :
      ({x | ε ≤ edist (f k x) (g x)} : Set α) ≤ᵐ[μ]
        ({x | ε ≤ edist (f_loc m k x) (g_loc m x)} ∪ F m : Set α) := by
    filter_upwards [hlek] with x hx hmem
    by_cases hxF : x ∈ F m
    · exact Or.inr hxF
    · exact Or.inl (hmem.trans (hx hxF))
  calc
    μ {x | ε ≤ edist (f k x) (g x)}
        ≤ μ ({x | ε ≤ edist (f_loc m k x) (g_loc m x)} ∪ F m) := measure_mono_ae hsub
    _ ≤ μ {x | ε ≤ edist (f_loc m k x) (g_loc m x)} + μ (F m) := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hkm hm.le
    _ = η := ENNReal.add_halves η

/-- A constant family along any filter converges in measure to its value, with no finiteness or
measurability assumptions. -/
theorem tendstoInMeasure_const [PseudoEMetricSpace E] (g : α → E) :
    TendstoInMeasure μ (fun _ ↦ g) l g := fun ε hε ↦ by
  simpa [edist_self, hε.not_ge] using tendsto_const_nhds

end TauCeti

/-- A convergent deterministic family converges in measure as constant functions, with no finiteness
assumption on the measure and no measurability assumption. -/
theorem Filter.Tendsto.tendstoInMeasure_const {α ι E : Type*} {_ : MeasurableSpace α}
    {μ : MeasureTheory.Measure α} [PseudoEMetricSpace E] {l : Filter ι} {c : ι → E} {b : E}
    (hc : Filter.Tendsto c l (nhds b)) :
    MeasureTheory.TendstoInMeasure μ (fun k _ ↦ c k) l (fun _ ↦ b) := by
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [EMetric.tendsto_nhds.1 hc ε hε] with k hk
  simp [hk.not_ge]

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

namespace MeasureTheory.TendstoInMeasure

open Filter
open scoped Topology ENNReal

/-- Pairing functions preserves convergence in measure, without measurability or finiteness
assumptions on the measure, and along an arbitrary filter. -/
theorem prodMk {α ι E₁ E₂ : Type*} {_ : MeasurableSpace α} {μ : Measure α}
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

/-- Pointwise multiplication of two families converging in measure in a uniform group converges in
measure to the pointwise product of their limits. -/
@[to_additive
  /-- Pointwise addition of two families converging in measure in an additive uniform group
  converges in measure to the pointwise sum of their limits. -/]
theorem mul {Ω E ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [PseudoEMetricSpace E] [Group E] [IsUniformGroup E] {l : Filter ι}
    {f₁ f₂ : ι → Ω → E} {g₁ g₂ : Ω → E}
    (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun k ω ↦ f₁ k ω * f₂ k ω) l (fun ω ↦ g₁ ω * g₂ ω) :=
  uniformContinuous_mul.comp_tendstoInMeasure (h₁.prodMk h₂)

/-- Uniformly continuous constant scalar multiplication preserves convergence in measure. -/
@[to_additive
  /-- Uniformly continuous constant vector addition preserves convergence in measure. -/]
theorem const_smul {Ω M E ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [PseudoEMetricSpace E] [SMul M E] [UniformContinuousConstSMul M E] {l : Filter ι}
    {f : ι → Ω → E} {g : Ω → E} (hf : TendstoInMeasure μ f l g) (c : M) :
    TendstoInMeasure μ (fun k ω ↦ c • f k ω) l (fun ω ↦ c • g ω) :=
  (uniformContinuous_const_smul c).comp_tendstoInMeasure hf

/-- Left multiplication by a constant preserves convergence in measure whenever left multiplication
is uniformly continuous via `UniformContinuousConstSMul R R`. -/
theorem const_mul {Ω R ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [Mul R] [PseudoEMetricSpace R] [UniformContinuousConstSMul R R] {l : Filter ι}
    {f : ι → Ω → R} {g : Ω → R} (hf : TendstoInMeasure μ f l g) (c : R) :
    TendstoInMeasure μ (fun k ω ↦ c * f k ω) l (fun ω ↦ c * g ω) :=
  hf.const_smul c

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
