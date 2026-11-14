/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.Moments.Chebyshev

/-! # Convergence in measure: high-probability bounds and algebraic operations

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

This file also develops the algebraic stability of `MeasureTheory.TendstoInMeasure`:
* Uniformly continuous maps and binary operations (`TendstoInMeasure.uniformContinuous_comp`,
  `TendstoInMeasure.uniformContinuous₂_comp`), hence addition, negation, subtraction, and
  constant scalar multiplication, preserve convergence in measure on an arbitrary measure space
  without measurability hypotheses.
* On a finite measure space, almost-everywhere strongly measurable functions are tight in
  distance (`MeasureTheory.tendsto_measure_dist_ge_atTop`), so bounded scalar multiplication
  (`TendstoInMeasure.smul`, `Filter.Tendsto.smul_tendstoInMeasure`) and ring multiplication
  (`TendstoInMeasure.mul`) preserve convergence in measure along an arbitrary filter when the
  limits are almost-everywhere strongly measurable.

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
* `MeasureTheory.TendstoInMeasure.uniformContinuous_comp` and
  `MeasureTheory.TendstoInMeasure.uniformContinuous₂_comp`: post-composition with uniformly
  continuous unary and binary maps.
* `MeasureTheory.TendstoInMeasure.add`, `neg`, `sub`, `const_smul`: uniform-group and constant
  scalar operations on arbitrary measure spaces.
* `MeasureTheory.TendstoInMeasure.smul` and `MeasureTheory.TendstoInMeasure.mul`: joint
  scalar multiplication and multiplication on finite measure spaces.

## Source

The rate-squeeze lemmas in `namespace TauCeti` are adapted from the Davis--Kahan/DKPS
formalization, `ForMathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` at `fc38eb4`,
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
open scoped ENNReal

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
    TendstoInMeasure μ (fun i x ↦ Ψ (f₁ i x) (f₂ i x)) l (fun x ↦ Ψ (g₁ x) (g₂ x)) := by
  intro ε hε
  obtain ⟨δ, hδ, hΨδ⟩ := EMetric.uniformContinuous_iff.mp hΨ ε hε
  have hsum : Tendsto (fun i ↦ μ {x | δ ≤ edist (f₁ i x) (g₁ x)} +
      μ {x | δ ≤ edist (f₂ i x) (g₂ x)}) l (𝓝 0) := by
    simpa only [add_zero] using (hf₁ δ hδ).add (hf₂ δ hδ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun i ↦ (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  rw [Set.mem_ofPred_eq] at hx
  by_contra hnot
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
  have hprod : edist (f₁ i x, f₂ i x) (g₁ x, g₂ x) < δ := max_lt hnot.1 hnot.2
  exact hx.not_gt (hΨδ hprod)

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

/-- On a finite measure space, the measure of `{x | n ≤ dist (g x) y₀}` tends to `0` as
`n → ∞` for every almost-everywhere strongly measurable function `g`. Both finiteness of `μ`
and measurability of `g` are essential. -/
theorem tendsto_measure_dist_ge_atTop [PseudoMetricSpace E] [IsFiniteMeasure μ]
    {g : α → E} (hg : AEStronglyMeasurable g μ) (y₀ : E) :
    Tendsto (fun n : ℕ ↦ μ {x | (n : ℝ) ≤ dist (g x) y₀}) atTop (𝓝 0) := by
  let g' : α → E := hg.mk g
  have hmeas : ∀ n : ℕ, MeasurableSet {x | (n : ℝ) ≤ dist (g' x) y₀} := fun n ↦
    measurableSet_le measurable_const
      (hg.stronglyMeasurable_mk.dist stronglyMeasurable_const).measurable
  have hanti : Antitone (fun n : ℕ ↦ {x | (n : ℝ) ≤ dist (g' x) y₀}) := fun m n hmn x hx ↦ by
    rw [Set.mem_ofPred_eq] at hx ⊢
    exact (Nat.cast_le.mpr hmn).trans hx
  have hinter : (⋂ n : ℕ, {x | (n : ℝ) ≤ dist (g' x) y₀}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    exact exists_nat_gt (dist (g' x) y₀)
  have hlim := tendsto_measure_iInter_atTop (fun n ↦ (hmeas n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  rw [hinter, measure_empty] at hlim
  refine hlim.congr fun n ↦ measure_congr ?_
  filter_upwards [hg.ae_eq_mk] with x hx
  simp [g', hx]

private theorem dist_smul_lt_of_bounds [Zero 𝕜] [Zero E] [PseudoMetricSpace 𝕜]
    [PseudoMetricSpace E] [SMul 𝕜 E] [IsBoundedSMul 𝕜 E]
    {c₁ c₀ : 𝕜} {y₁ y₀ : E} {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (hc₀ : dist c₀ 0 < M) (hy₀ : dist y₀ 0 < M)
    (hc_sqrt : dist c₁ c₀ < Real.sqrt (ε / 3)) (hy_sqrt : dist y₁ y₀ < Real.sqrt (ε / 3))
    (hc_div : dist c₁ c₀ < ε / (3 * M)) (hy_div : dist y₁ y₀ < ε / (3 * M)) :
    dist (c₁ • y₁) (c₀ • y₀) < ε := by
  have hprod₁ : dist c₁ c₀ * dist y₁ y₀ < ε / 3 := by
    calc dist c₁ c₀ * dist y₁ y₀
        < Real.sqrt (ε / 3) * Real.sqrt (ε / 3) :=
          mul_lt_mul'' hc_sqrt hy_sqrt dist_nonneg dist_nonneg
      _ = ε / 3 := Real.mul_self_sqrt (by positivity)
  have hprod₂ : dist c₀ 0 * dist y₁ y₀ < ε / 3 := by
    calc dist c₀ 0 * dist y₁ y₀
        < M * (ε / (3 * M)) := mul_lt_mul'' hc₀ hy_div dist_nonneg dist_nonneg
      _ = ε / 3 := by field_simp [hM.ne']
  have hprod₃ : dist c₁ c₀ * dist y₀ 0 < ε / 3 := by
    calc dist c₁ c₀ * dist y₀ 0
        < (ε / (3 * M)) * M := mul_lt_mul'' hc_div hy₀ dist_nonneg dist_nonneg
      _ = ε / 3 := by field_simp [hM.ne']
  have htri : dist (c₁ • y₁) (c₀ • y₀) ≤
      dist c₁ c₀ * dist y₁ y₀ + dist c₀ 0 * dist y₁ y₀ + dist c₁ c₀ * dist y₀ 0 := by
    calc dist (c₁ • y₁) (c₀ • y₀)
        ≤ dist (c₁ • y₁) (c₁ • y₀) + dist (c₁ • y₀) (c₀ • y₀) := dist_triangle _ _ _
      _ ≤ dist c₁ 0 * dist y₁ y₀ + dist c₁ c₀ * dist y₀ 0 :=
          add_le_add (dist_smul_pair _ _ _) (dist_pair_smul _ _ _)
      _ ≤ (dist c₁ c₀ + dist c₀ 0) * dist y₁ y₀ + dist c₁ c₀ * dist y₀ 0 := by
          gcongr
          exact dist_triangle _ _ _
      _ = _ := by ring
  linarith

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
  obtain ⟨N₁, hN₁⟩ := ENNReal.tendsto_atTop_zero.mp
    (tendsto_measure_dist_ge_atTop hc₀ 0) (η / 2 / 2) hη4
  obtain ⟨N₂, hN₂⟩ := ENNReal.tendsto_atTop_zero.mp
    (tendsto_measure_dist_ge_atTop hg 0) (η / 2 / 2) hη4
  let M : ℕ := max 1 (max N₁ N₂)
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hMc₀ : μ {x | (M : ℝ) ≤ dist (c₀ x) 0} ≤ η / 2 / 2 :=
    hN₁ M ((le_max_left _ _).trans (le_max_right _ _))
  have hMg : μ {x | (M : ℝ) ≤ dist (g x) 0} ≤ η / 2 / 2 :=
    hN₂ M ((le_max_right _ _).trans (le_max_right _ _))
  let δ : ℝ := min (Real.sqrt (ε / 3)) (ε / (3 * M))
  have hδ : 0 < δ := lt_min (Real.sqrt_pos.mpr (by positivity)) (by positivity)
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp (hc δ hδ)) (η / 2 / 2) hη4,
    (ENNReal.tendsto_nhds_zero.mp (hf δ hδ)) (η / 2 / 2) hη4] with i hic hif
  have hsub : {x | ε ≤ dist (c i x • f i x) (c₀ x • g x)} ⊆
      ({x | (M : ℝ) ≤ dist (c₀ x) 0} ∪ {x | (M : ℝ) ≤ dist (g x) 0}) ∪
      ({x | δ ≤ dist (c i x) (c₀ x)} ∪ {x | δ ≤ dist (f i x) (g x)}) := by
    intro x hx
    rw [Set.mem_ofPred_eq] at hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot
    rcases hnot with ⟨⟨hc₀_lt, hg_lt⟩, ⟨hc_lt, hf_lt⟩⟩
    exact hx.not_gt (dist_smul_lt_of_bounds hε hM_pos hc₀_lt hg_lt
      (hc_lt.trans_le (min_le_left _ _)) (hf_lt.trans_le (min_le_left _ _))
      (hc_lt.trans_le (min_le_right _ _)) (hf_lt.trans_le (min_le_right _ _)))
  calc μ {x | ε ≤ dist (c i x • f i x) (c₀ x • g x)}
      ≤ (μ {x | (M : ℝ) ≤ dist (c₀ x) 0} + μ {x | (M : ℝ) ≤ dist (g x) 0}) +
          (μ {x | δ ≤ dist (c i x) (c₀ x)} + μ {x | δ ≤ dist (f i x) (g x)}) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add (measure_union_le _ _) (measure_union_le _ _)))
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

/-- On a finite measure space, pointwise multiplication in a non-unital seminormed ring
preserves convergence in measure along any filter when both limit functions are
almost-everywhere strongly measurable. -/
theorem TendstoInMeasure.mul [NonUnitalSeminormedRing R] [IsFiniteMeasure μ]
    {f₁ f₂ : ι → α → R} {g₁ g₂ : α → R}
    (hg₁ : AEStronglyMeasurable g₁ μ) (hg₂ : AEStronglyMeasurable g₂ μ)
    (hf₁ : TendstoInMeasure μ f₁ l g₁) (hf₂ : TendstoInMeasure μ f₂ l g₂) :
    TendstoInMeasure μ (fun i x ↦ f₁ i x * f₂ i x) l (fun x ↦ g₁ x * g₂ x) :=
  hf₁.smul hg₁ hg₂ hf₂

end Algebra

end MeasureTheory
