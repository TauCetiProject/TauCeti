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

* `MeasureTheory.TendstoInMeasure.add`, `const_smul`,
  `MeasureTheory.AEStronglyMeasurable.tendstoInMeasure_smul`: algebraic operations preserving
  convergence in measure.
* `MeasureTheory.tendstoInMeasure_of_tendsto_integral_norm_sq`: convergence in mean square
  implies convergence in measure for any measure and filter.
* `TauCeti.tendsto_measure_ge_zero_const_mul`, `tendsto_measure_ge_zero_mul_of_ae_lt_top`,
  `tendsto_measure_ge_zero_of_ae_le`: tail-measure convergence under scaling, a.e.-finite weights,
  and a.e. sum bounds (including `∞`).
* `TauCeti.tendsto_measure_lintegral_rpow_enorm_of_tendsto_eLpNorm` and
  `tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm`: `Lᵖ(μ.prod ν)` convergence (`0 < p < ∞`)
  forces `ν`-tail measures of `μ`-slice `p`-th power integrals to tend to zero.
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
  · simp only [zero_mul, not_le_of_gt hε, Set.ofPred_false, measure_empty]; exact tendsto_const_nhds
  rcases eq_or_ne ε ∞ with rfl | _
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h 1 one_pos)
      (fun _ ↦ zero_le) fun i ↦ measure_mono fun x hx ↦ by_contra fun hnot ↦
        (ENNReal.mul_lt_top hc.lt_top ((not_le.1 hnot).trans ENNReal.one_lt_top)).not_ge hx
  · exact (h (ε / c) (ENNReal.div_pos hε.ne' hc)).congr fun i ↦ congrArg μ <| Set.ext fun x ↦ by
      simp only [Set.mem_ofPred_eq, ENNReal.div_le_iff_le_mul (.inl hc0) (.inl hc), mul_comm]

/-- On a finite measure space, multiplying an `ℝ≥0∞`-valued family by an a.e. measurable,
a.e. finite weight preserves convergence of all positive tail measures to zero (including `∞`). -/
theorem tendsto_measure_ge_zero_mul_of_ae_lt_top [IsFiniteMeasure μ]
    {E : ι → α → ℝ≥0∞} {c : α → ℝ≥0∞} (hc : AEMeasurable c μ) (hfin : ∀ᵐ x ∂μ, c x < ∞)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E i x}) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ μ {x | ε ≤ c x * E i x}) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]; intro δ hδ
  let A (M : ℕ) : Set α := {x | (M : ℝ≥0∞) ≤ c x}
  have hA_null : μ (⋂ M, A M) = 0 := measure_mono_null (fun x hx ↦ by
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, not_lt, top_le_iff] at hx ⊢
    exact by_contra fun hne ↦ (ENNReal.exists_nat_gt hne).elim fun M hM ↦ hM.not_ge (hx M))
    (ae_iff.1 hfin)
  have hA_lim : Tendsto (μ ∘ A) atTop (𝓝 0) := hA_null ▸ tendsto_measure_iInter_atTop
    (fun _ ↦ hc.nullMeasurable measurableSet_Ici)
    (fun _ _ hMN _ (hx : (_ : ℝ≥0∞) ≤ _) ↦ (Nat.cast_le.2 hMN).trans hx) ⟨0, measure_ne_top μ _⟩
  obtain ⟨M, hM⟩ := (hA_lim.eventually (eventually_le_nhds (ENNReal.half_pos hδ.ne'))).exists
  filter_upwards [(tendsto_measure_ge_zero_const_mul (ENNReal.natCast_ne_top M) h hε).eventually
    (eventually_le_nhds (ENNReal.half_pos hδ.ne'))] with i hi
  refine (measure_mono (t := A M ∪ {x | ε ≤ (M : ℝ≥0∞) * E i x}) fun x hx ↦
    if hxM : (M : ℝ≥0∞) ≤ c x then .inl hxM else .inr <|
      Set.mem_ofPred.2 <| (Set.mem_ofPred.1 hx).trans (by gcongr; exact le_of_not_ge hxM)).trans
    ((measure_union_le (A M) _).trans ((add_le_add hM hi).trans_eq (ENNReal.add_halves δ)))

/-- If `E` is eventually bounded `μ`-a.e. by `E₁ + E₂` and all positive tail measures of `E₁` and
`E₂` tend to zero along `l`, then all positive tail measures of `E` tend to zero along `l`
(including at threshold `∞`). -/
theorem tendsto_measure_ge_zero_of_ae_le {E E₁ E₂ : ι → α → ℝ≥0∞}
    (h₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E₁ i x}) l (𝓝 0))
    (h₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun i ↦ μ {x | ε ≤ E₂ i x}) l (𝓝 0))
    (hle : ∀ᶠ i in l, ∀ᵐ x ∂μ, E i x ≤ E₁ i x + E₂ i x) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ μ {x | ε ≤ E i x}) l (𝓝 0) := by
  let δ := min 1 (ε / 2)
  have hδ : 0 < δ := lt_min one_pos (ENNReal.div_pos hε.ne' (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using (h₁ δ hδ).add (h₂ δ hδ))
    (Eventually.of_forall fun _ ↦ zero_le) (hle.mono fun i hi ↦
      (measure_mono_ae (hi.mono fun x hx hge ↦ by_contra fun hnot ↦ ?_)).trans
        (measure_union_le _ _))
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, δ, lt_min_iff] at hnot
  rcases eq_or_ne ε ∞ with rfl | _
  · exact (hx.trans_lt (ENNReal.add_lt_top.2 ⟨hnot.1.1.trans ENNReal.one_lt_top,
      hnot.2.1.trans ENNReal.one_lt_top⟩)).not_ge hge
  · exact (hx.trans_lt ((ENNReal.add_lt_add hnot.1.2 hnot.2.2).trans_eq
      (ENNReal.add_halves ε))).not_ge hge

/-- If `eLpNorm (f i) p (μ.prod ν) → 0` for `0 < p < ∞` and `SFinite` measures `μ`, `ν`, then the
`ν`-measure of slices where `∫⁻ x, ‖f i (x, y)‖ₑ ^ p.toReal ∂μ ≥ ε` tends to zero for every `ε > 0`
(including `∞`). No explicit measurability hypothesis on `f` is needed. -/
theorem tendsto_measure_lintegral_rpow_enorm_of_tendsto_eLpNorm
    {β ε' : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite μ] [SFinite ν]
    [TopologicalSpace ε'] [ContinuousENorm ε'] {f : ι → α × β → ε'} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hlim : Tendsto (fun i ↦ eLpNorm (f i) p (μ.prod ν)) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ ν {y | ε ≤ ∫⁻ x, ‖f i (x, y)‖ₑ ^ p.toReal ∂μ}) l (𝓝 0) := by
  have hδ0 : min 1 ε ≠ 0 := (lt_min one_pos hε).ne'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by
      simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp0 hp),
        ENNReal.zero_div] using ENNReal.Tendsto.div_const
          (((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp hlim) (.inr hδ0))
    (.of_forall fun _ ↦ zero_le)
    ((hlim.eventually (eventually_lt_nhds ENNReal.zero_lt_top)).mono fun i hi ↦ ?_)
  have hsm := aestronglyMeasurable_of_eLpNorm_ne_top hi.ne; have hm := hsm.eNorm.pow_const p.toReal
  refine (measure_mono fun _ hy ↦ (min_le_right 1 ε).trans hy).trans
    ((MeasureTheory.meas_ge_le_lintegral_div hm.lintegral_prod_left' hδ0
      ((min_le_left 1 ε).trans_lt ENNReal.one_lt_top).ne).trans_eq ?_)
  rw [← lintegral_prod_symm _ hm, MeasureTheory.lintegral_rpow_enorm_eq_eLpNorm_rpow hp0 hp hsm]

/-- Natural-power form of `tendsto_measure_lintegral_rpow_enorm_of_tendsto_eLpNorm` for `n ≠ 0`. -/
theorem tendsto_measure_lintegral_enorm_pow_of_tendsto_eLpNorm
    {β ε' : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite μ] [SFinite ν]
    [TopologicalSpace ε'] [ContinuousENorm ε'] {f : ι → α × β → ε'} {n : ℕ} (hn : n ≠ 0)
    (hlim : Tendsto (fun i ↦ eLpNorm (f i) n (μ.prod ν)) l (𝓝 0)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun i ↦ ν {y | ε ≤ ∫⁻ x, ‖f i (x, y)‖ₑ ^ n ∂μ}) l (𝓝 0) := by
  simpa only [ENNReal.toReal_natCast, ENNReal.rpow_natCast] using
    tendsto_measure_lintegral_rpow_enorm_of_tendsto_eLpNorm
      (Nat.cast_ne_zero.2 hn) (ENNReal.natCast_ne_top n) hlim hε

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

section TendstoInMeasure

open ENNReal

variable {Ω E ι : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} {l : Filter ι}
  {f f₁ f₂ : ι → Ω → E} {g g₁ g₂ : Ω → E}

/-- Pointwise scalar multiplication by a constant preserves convergence in measure whenever
`(c • ·)` is uniformly continuous, for any measure and filter without measurability hypotheses. -/
theorem TendstoInMeasure.const_smul {M : Type*} [PseudoEMetricSpace E] [SMul M E]
    [UniformContinuousConstSMul M E] (h : TendstoInMeasure μ f l g) (c : M) :
    TendstoInMeasure μ (fun i ω ↦ c • f i ω) l (fun ω ↦ c • g ω) := fun ε hε ↦ by
  obtain ⟨δ, hδ, huc⟩ := EMetric.uniformContinuous_iff.1
    (uniformContinuous_const_smul c : UniformContinuous fun x : E ↦ c • x) ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ ↦ zero_le) fun _ ↦ measure_mono fun _ hω ↦ by_contra fun hlt ↦
      (huc (not_le.1 hlt)).not_ge hω

variable [SeminormedAddCommGroup E]

/-- Pointwise sums of functions converging in measure converge in measure to the sum of the
limits, for any measure and filter without measurability hypotheses. -/
theorem TendstoInMeasure.add (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i ω ↦ f₁ i ω + f₂ i ω) l (fun ω ↦ g₁ ω + g₂ ω) :=
  fun _ hε ↦ TauCeti.tendsto_measure_ge_zero_of_ae_le h₁ h₂
    (.of_forall fun _ ↦ .of_forall fun _ ↦ edist_add_add_le _ _ _ _) hε

/-- Pointwise negation preserves convergence in measure, for any measure and filter. -/
theorem TendstoInMeasure.neg (h : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i ω ↦ -f i ω) l (fun ω ↦ -g ω) := by
  simpa only [neg_one_smul] using h.const_smul (-1 : ℤ)

/-- Pointwise subtraction preserves convergence in measure, for any measure and filter. -/
theorem TendstoInMeasure.sub (h₁ : TendstoInMeasure μ f₁ l g₁) (h₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i ω ↦ f₁ i ω - f₂ i ω) l (fun ω ↦ g₁ ω - g₂ ω) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

/-- On a finite measure space, pointwise scalar multiplication by an a.e. strongly measurable
scalar function preserves convergence in measure along any filter. -/
theorem AEStronglyMeasurable.tendstoInMeasure_smul {𝕜 : Type*} [IsFiniteMeasure μ]
    [SeminormedAddCommGroup 𝕜] [DistribSMul 𝕜 E] [IsBoundedSMul 𝕜 E] {c : Ω → 𝕜}
    (hc : AEStronglyMeasurable c μ) (h : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i ω ↦ c ω • f i ω) l (fun ω ↦ c ω • g ω) := fun _ hε ↦
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (TauCeti.tendsto_measure_ge_zero_mul_of_ae_lt_top hc.eNorm (.of_forall fun _ ↦ eNorm_lt_top)
      h hε) (fun _ ↦ zero_le) fun i ↦ measure_mono fun ω hω ↦ Set.mem_ofPred.2 <|
    hω.trans <| (edist_smul_le (c ω) (f i ω) (g ω)).trans_eq (ENNReal.smul_def _ _)

end TendstoInMeasure

end MeasureTheory
