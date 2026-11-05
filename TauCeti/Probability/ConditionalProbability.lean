/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Conditional measures and the law of total probability

A finite measure is the sum, over the values of a random variable with countably many values, of
its conditional measures on the fibres weighted by the masses of the fibres:

```text
μ = Measure.sum fun b => μ (f ⁻¹' {b}) • μ[|f ⁻¹' {b}].
```

Mathlib's `ProbabilityTheory.sum_meas_smul_cond_fiber` is the same decomposition for a random
variable valued in a `Fintype`; this file extends it to countable value spaces with measurable
singletons, where the finite sum of measures becomes `MeasureTheory.Measure.sum`. Fibres of mass
zero contribute nothing, so no positivity hypothesis on the fibres is needed.

Conditioning on almost-everywhere equal events gives equal conditional measures, and a function
bounded on a measurable event is integrable for the conditional measure on it. A measurable map
that scales measure by a constant factor carries conditional measures to conditional measures.
Conditional measures also depend measurably on a measurable family of finite measures and a
jointly measurable family of conditioning events. In particular, conditioning between measurable
moving endpoints is measurable for all four endpoint conventions.
Conditioning a probability measure away from a single point removes that atom and rescales the
rest by `1 / (1 - μ {a})`; this computes the masses of, and integrals against, the conditioned
measure. Conditional measures on intervals agree across endpoint conventions whenever the relevant
endpoint atoms vanish. These identities apply to any partially ordered measurable space,
including atomless laws and atomic laws with null endpoints.

For any probability law, conditioning on a positive-mass measurable event has total variation
distance twice the excluded mass. Conditioning on events whose masses tend to one therefore
recovers the law.

## Main results

* `ProbabilityTheory.sum_meas_smul_cond_fiber_of_countable`
* `ProbabilityTheory.cond_congr_ae`
* `MeasureTheory.Measure.toNNReal_smul_integral_cond_eq_setIntegral`
* `Measurable.cond`, `Measurable.cond_const`, and `Measurable.cond_preimage_Ioc` (with the
  corresponding `Icc`, `Ioo`, and `Ico` forms)
* `ProbabilityTheory.integrable_cond_of_norm_le`
* `ProbabilityTheory.map_cond_preimage`
* `ProbabilityTheory.cond_compl_singleton_real`,
  `ProbabilityTheory.cond_compl_singleton_real_singleton`,
  `ProbabilityTheory.integrable_cond_compl_singleton_iff`,
  `ProbabilityTheory.integral_cond_compl_singleton`
* `MeasureTheory.Measure.cond_Icc_eq_cond_Ioc`, `MeasureTheory.Measure.cond_Ioo_eq_cond_Ioc`,
  `MeasureTheory.Measure.cond_Ico_eq_cond_Ioc`
* `MeasureTheory.Measure.tvDist_cond_self`, `MeasureTheory.Measure.tendsto_tvDist_cond` —
  the distance to a conditioned law and convergence as the retained mass tends to one
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]

/-- Conditioning on almost-everywhere equal events gives equal conditional measures. -/
theorem cond_congr_ae {μ : Measure Ω} {s t : Set Ω} (h : s =ᵐ[μ] t) :
    μ[|s] = μ[|t] := by
  rw [cond, cond, measure_congr h, Measure.restrict_congr_set h]

/-- Scaling an integral under a conditional measure by the finite mass of the conditioning
event recovers the corresponding set integral. -/
theorem _root_.MeasureTheory.Measure.toNNReal_smul_integral_cond_eq_setIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (s : Set Ω) (f : Ω → E)
    (h : μ s ≠ ⊤) :
    (μ s).toNNReal • ∫ x, f x ∂cond μ s = ∫ x in s, f x ∂μ := by
  have haverage := measure_smul_setAverage f h
  rw [setAverage_eq', ← cond, Measure.real, ← ENNReal.coe_toNNReal_eq_toReal] at haverage
  simpa only [NNReal.smul_def] using haverage

/-! ### Measurability in a law and a conditioning event -/

/-- Conditioning a measurable family of finite measures on a jointly measurable family of
events gives a measurable family of measures. The event at `a` is the section
`{x | (a, x) ∈ s}`. This statement includes the zero-mass totalization of `cond`. -/
theorem _root_.Measurable.cond {α : Type*} [MeasurableSpace α] {μ : α → Measure Ω}
    (hμ : Measurable μ) (hfinite : ∀ a, IsFiniteMeasure (μ a))
    {s : Set (α × Ω)} (hs : MeasurableSet s) :
    Measurable fun a ↦ ProbabilityTheory.cond (μ a) (Prod.mk a ⁻¹' s) := by
  let κ : Kernel α Ω := ⟨μ, hμ⟩
  have hfinite' (a : α) : IsFiniteMeasure (κ a) := hfinite a
  have hsection (a : α) : MeasurableSet (Prod.mk a ⁻¹' s) :=
    hs.preimage measurable_prodMk_left
  rw [Measure.measurable_measure]
  intro t ht
  have hmass : Measurable fun a ↦ μ a (Prod.mk a ⁻¹' s) := by
    simpa only [κ, Kernel.coe_mk] using
      Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hs hfinite'
  have hinter : Measurable fun a ↦ μ a ((Prod.mk a ⁻¹' s) ∩ t) := by
    have hst : MeasurableSet (s ∩ (Set.univ ×ˢ t)) := hs.inter (MeasurableSet.univ.prod ht)
    have h : Measurable fun a ↦ μ a (Prod.mk a ⁻¹' (s ∩ (Set.univ ×ˢ t))) := by
      simpa only [κ, Kernel.coe_mk] using
        Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hst hfinite'
    convert h using 1
    funext a
    congr 1
    ext x
    simp
  simp_rw [ProbabilityTheory.cond_apply (hsection _)]
  convert hmass.inv.mul hinter using 1

/-- Conditioning a measurable family of measures on a fixed measurable event is measurable. -/
theorem _root_.Measurable.cond_const {α : Type*} [MeasurableSpace α] {μ : α → Measure Ω}
    (hμ : Measurable μ) {s : Set Ω} (hs : MeasurableSet s) :
    Measurable fun a ↦ ProbabilityTheory.cond (μ a) s := by
  refine Measure.measurable_measure.2 fun t ht ↦ ?_
  simp_rw [ProbabilityTheory.cond_apply hs]
  exact ((Measure.measurable_coe hs).comp hμ).inv.mul
    ((Measure.measurable_coe (hs.inter ht)).comp hμ)

section MovingIntervals

variable {α δ : Type*} [MeasurableSpace α] [LinearOrder δ] [TopologicalSpace δ]
  [MeasurableSpace δ] [OpensMeasurableSpace δ] [SecondCountableTopology δ] [OrderClosedTopology δ]
  {μ : α → Measure Ω} {g : Ω → δ} {l r : α → δ}

/-- Conditioning on the inverse image of a moving half-open interval `(l, r]` is measurable. -/
theorem _root_.Measurable.cond_preimage_Ioc (hμ : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasure (μ a)) (hg : Measurable g)
    (hl : Measurable l) (hr : Measurable r) :
    Measurable fun a ↦ ProbabilityTheory.cond (μ a) (g ⁻¹' Set.Ioc (l a) (r a)) := by
  have hs : MeasurableSet {p : α × Ω | g p.2 ∈ Set.Ioc (l p.1) (r p.1)} := by
    simpa only [Function.comp_apply, Set.mem_Ioc, Set.ofPred_and] using
      (measurableSet_lt (hl.comp measurable_fst) (hg.comp measurable_snd)).inter
        (measurableSet_le (hg.comp measurable_snd) (hr.comp measurable_fst))
  convert hμ.cond hfinite hs using 1
  rfl

/-- Conditioning on the inverse image of a moving closed interval `[l, r]` is measurable. -/
theorem _root_.Measurable.cond_preimage_Icc (hμ : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasure (μ a)) (hg : Measurable g)
    (hl : Measurable l) (hr : Measurable r) :
    Measurable fun a ↦ ProbabilityTheory.cond (μ a) (g ⁻¹' Set.Icc (l a) (r a)) := by
  have hs : MeasurableSet {p : α × Ω | g p.2 ∈ Set.Icc (l p.1) (r p.1)} := by
    simpa only [Function.comp_apply, Set.mem_Icc, Set.ofPred_and] using
      (measurableSet_le (hl.comp measurable_fst) (hg.comp measurable_snd)).inter
        (measurableSet_le (hg.comp measurable_snd) (hr.comp measurable_fst))
  convert hμ.cond hfinite hs using 1
  rfl

/-- Conditioning on the inverse image of a moving open interval `(l, r)` is measurable. -/
theorem _root_.Measurable.cond_preimage_Ioo (hμ : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasure (μ a)) (hg : Measurable g)
    (hl : Measurable l) (hr : Measurable r) :
    Measurable fun a ↦ ProbabilityTheory.cond (μ a) (g ⁻¹' Set.Ioo (l a) (r a)) := by
  have hs : MeasurableSet {p : α × Ω | g p.2 ∈ Set.Ioo (l p.1) (r p.1)} := by
    simpa only [Function.comp_apply, Set.mem_Ioo, Set.ofPred_and] using
      (measurableSet_lt (hl.comp measurable_fst) (hg.comp measurable_snd)).inter
        (measurableSet_lt (hg.comp measurable_snd) (hr.comp measurable_fst))
  convert hμ.cond hfinite hs using 1
  rfl

/-- Conditioning on the inverse image of a moving half-open interval `[l, r)` is measurable. -/
theorem _root_.Measurable.cond_preimage_Ico (hμ : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasure (μ a)) (hg : Measurable g)
    (hl : Measurable l) (hr : Measurable r) :
    Measurable fun a ↦ ProbabilityTheory.cond (μ a) (g ⁻¹' Set.Ico (l a) (r a)) := by
  have hs : MeasurableSet {p : α × Ω | g p.2 ∈ Set.Ico (l p.1) (r p.1)} := by
    simpa only [Function.comp_apply, Set.mem_Ico, Set.ofPred_and] using
      (measurableSet_le (hl.comp measurable_fst) (hg.comp measurable_snd)).inter
        (measurableSet_lt (hg.comp measurable_snd) (hr.comp measurable_fst))
  convert hμ.cond hfinite hs using 1
  rfl

end MovingIntervals

/-- A function whose norm is bounded on a measurable event `s` is integrable for the conditional
measure `μ[|s]`. For instance, a point drawn uniformly from a bounded Borel set of a normed space
has integrable position. -/
theorem integrable_cond_of_norm_le {E : Type*} [NormedAddCommGroup E] {μ : Measure Ω}
    {s : Set Ω} {f : Ω → E} (hs : MeasurableSet s) (hf : AEStronglyMeasurable f μ[|s]) {C : ℝ}
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) : Integrable f μ[|s] :=
  Integrable.of_bound hf C ((ae_cond_mem hs).mono hC)

/-- A measurable map that scales measure by a constant factor transports conditional measures:
if `μ (f ⁻¹' A) = k * ν A` for every measurable `A`, with `k ≠ 0` finite, then `f` carries `μ`
conditioned on `f ⁻¹' t` to `ν` conditioned on `t`. Translations and linear isometries of a
Euclidean space (with `k = 1`) and nonzero dilations are the typical examples. -/
theorem map_cond_preimage {μ : Measure Ω} {ν : Measure β} {f : Ω → β} (hf : Measurable f)
    {k : ENNReal} (hk₀ : k ≠ 0) (hk : k ≠ ⊤) (h : ∀ A, MeasurableSet A → μ (f ⁻¹' A) = k * ν A)
    {t : Set β} (ht : MeasurableSet t) :
    (μ[|f ⁻¹' t]).map f = ν[|t] := by
  ext A hA
  rw [Measure.map_apply hf hA, cond_apply' (hf hA), cond_apply' hA, ← preimage_inter,
    h _ ht, h _ (ht.inter hA), ENNReal.mul_inv (.inl hk₀) (.inl hk), mul_mul_mul_comm,
    ENNReal.inv_mul_cancel hk₀ hk, one_mul]

/-- The **law of total probability** for a random variable with countably many values: a finite
measure `μ` is the sum of its conditional measures on the fibres of a measurable `f`, each weighted
by the mass of its fibre. -/
theorem sum_meas_smul_cond_fiber_of_countable [Countable β] [MeasurableSingletonClass β]
    {f : Ω → β} (hf : Measurable f) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Measure.sum (fun b => μ (f ⁻¹' {b}) • μ[|f ⁻¹' {b}]) = μ := by
  ext E hE
  have hfib : ∀ b, MeasurableSet (f ⁻¹' {b}) := fun b => hf (measurableSet_singleton b)
  calc (Measure.sum fun b => μ (f ⁻¹' {b}) • μ[|f ⁻¹' {b}]) E
      = ∑' b, μ (f ⁻¹' {b} ∩ E) := by
        simp only [MeasureTheory.Measure.sum_apply _ hE, _root_.smul_apply, smul_eq_mul]
        simp_rw [mul_comm (μ _), cond_mul_eq_inter (hfib _)]
    _ = μ E := by
        rw [← measure_iUnion (fun b c hbc =>
          ((Set.disjoint_singleton.2 hbc).preimage f).mono Set.inter_subset_left
            Set.inter_subset_left) fun b => (hfib b).inter hE]
        congr 1
        ext ω
        simp

/-! ### Removing one atom -/

section ComplSingleton

variable [MeasurableSingletonClass Ω] {μ : Measure Ω} {a : Ω}

/-- Conditioning away from a point leaves no mass at that point. -/
@[simp]
theorem cond_compl_singleton_apply_self : μ[|{a}ᶜ] {a} = 0 := by
  simp [cond_apply (measurableSet_singleton a).compl]

/-- A function is integrable for a finite measure conditioned away from a point exactly when it is
integrable for the measure itself: only the single atom at that point differs. -/
theorem integrable_cond_compl_singleton_iff [IsFiniteMeasure μ] {E : Type*}
    [NormedAddCommGroup E] {f : Ω → E} : Integrable f μ[|{a}ᶜ] ↔ Integrable f μ := by
  have hatom : IntegrableOn f {a} μ := integrableOn_singleton
  have hcompl : Integrable f μ[|{a}ᶜ] ↔ IntegrableOn f {a}ᶜ μ := by
    by_cases hμ : μ {a}ᶜ = 0
    · simp [IntegrableOn, cond, Measure.restrict_eq_zero.2 hμ]
    · rw [cond, integrable_smul_measure (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))
        (ENNReal.inv_ne_top.2 hμ), IntegrableOn]
  rw [hcompl, ← integrableOn_univ, ← compl_union_self {a}, integrableOn_union,
    and_iff_left hatom]

variable [IsProbabilityMeasure μ]

/-- Conditioning a probability measure away from a point removes all mass exactly when the measure
is the point mass there. -/
theorem cond_compl_singleton_eq_zero_iff : μ[|{a}ᶜ] = 0 ↔ μ {a} = 1 := by
  rw [cond_eq_zero, prob_compl_eq_one_sub (measurableSet_singleton a)]
  constructor
  · rintro (h | h)
    · exact absurd h (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    · exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.1 h)
  · intro h
    simp [h]

/-- A probability measure conditioned away from a point is a probability measure unless it is the
point mass there. -/
theorem isProbabilityMeasure_cond_compl_singleton (h : μ {a} ≠ 1) :
    IsProbabilityMeasure μ[|{a}ᶜ] :=
  cond_isProbabilityMeasure fun h' => h (cond_compl_singleton_eq_zero_iff.1 (by simp [h']))

/-- Conditioning a probability measure away from a point rescales the other singleton masses by
`1 / (1 - μ {a})`. -/
theorem cond_compl_singleton_apply_singleton {x : Ω} (hx : x ≠ a) :
    μ[|{a}ᶜ] {x} = (1 - μ {a})⁻¹ * μ {x} := by
  rw [cond_apply (measurableSet_singleton a).compl,
    prob_compl_eq_one_sub (measurableSet_singleton a),
    inter_eq_right.2 (singleton_subset_iff.2 hx)]

/-- Conditioning a probability measure away from a point removes that point from every set and
rescales the remaining real mass by `1 / (1 - μ.real {a})`. -/
theorem cond_compl_singleton_real (s : Set Ω) :
    (μ[|{a}ᶜ]).real s = μ.real (s \ {a}) / (1 - μ.real {a}) := by
  rw [measureReal_def, cond_apply (measurableSet_singleton a).compl,
    prob_compl_eq_one_sub (measurableSet_singleton a)]
  simp [measureReal_def, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
    sdiff_eq_compl_inter, div_eq_inv_mul]

/-- Conditioning a probability measure away from a point rescales the other real singleton masses
by `1 / (1 - μ.real {a})`. -/
theorem cond_compl_singleton_real_singleton {x : Ω} (hx : x ≠ a) :
    (μ[|{a}ᶜ]).real {x} = μ.real {x} / (1 - μ.real {a}) := by
  rw [cond_compl_singleton_real, sdiff_singleton_eq_self fun h => hx (mem_singleton_iff.1 h).symm]

/-- Integration against a probability measure conditioned away from a point removes the
contribution of the atom there and rescales by `1 / (1 - μ.real {a})`. -/
theorem integral_cond_compl_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : Ω → E} (hf : Integrable f μ) :
    ∫ x, f x ∂μ[|{a}ᶜ] = (1 - μ.real {a})⁻¹ • (∫ x, f x ∂μ - μ.real {a} • f a) := by
  rw [cond, integral_smul_measure, setIntegral_compl (measurableSet_singleton a) hf,
    integral_singleton, ENNReal.toReal_inv, ← measureReal_def,
    probReal_compl_eq_one_sub (measurableSet_singleton a)]

/-- For a function vanishing at `a`, integration against a probability measure conditioned away
from `a` is integration against the measure itself, rescaled by `1 / (1 - μ.real {a})`. No
integrability is needed: both sides vanish together when the function is not integrable. -/
theorem integral_cond_compl_singleton_of_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Ω → E} (hf : f a = 0) :
    ∫ x, f x ∂μ[|{a}ᶜ] = (1 - μ.real {a})⁻¹ • ∫ x, f x ∂μ := by
  rw [cond, integral_smul_measure,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [notMem_compl_iff, mem_singleton_iff] at hx
      rw [hx, hf],
    ENNReal.toReal_inv, ← measureReal_def, probReal_compl_eq_one_sub (measurableSet_singleton a)]

end ComplSingleton

end ProbabilityTheory

namespace MeasureTheory.Measure

open Filter ProbabilityTheory
open scoped ENNReal Topology

/-- Mathlib's total variation distance from a probability law conditioned on a positive-mass
measurable event to the original law is twice the excluded mass. -/
theorem tvDist_cond_self {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet A) (hμA : μ A ≠ 0) :
    tvDist (cond μ A) μ = 2 * (1 - μ.real A) := by
  let _ := cond_isProbabilityMeasure hμA
  have hH : IsHahnDecomposition μ (cond μ A) A := by
    refine ⟨hA, ?_, ?_⟩
    · rw [ProbabilityTheory.cond, Measure.restrict_smul, Measure.restrict_restrict hA,
        inter_self]
      apply Measure.le_iff.mpr
      intro B _
      rw [_root_.smul_apply, smul_eq_mul]
      have hi : 1 ≤ (μ A)⁻¹ := by
        simpa using ENNReal.inv_le_inv.mpr (prob_le_one (μ := μ) (s := A))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hi
        (bot_le : (0 : ℝ≥0∞) ≤ μ.restrict A B)
    · rw [ProbabilityTheory.cond, Measure.restrict_smul, Measure.restrict_restrict hA.compl]
      simp only [compl_inter_self, Measure.restrict_empty, smul_zero]
      exact bot_le
  have hfull : (cond μ A).real A = 1 := by
    simp only [measureReal_def, cond_apply_self hμA (measure_ne_top μ A), ENNReal.toReal_one]
  have hzero : (cond μ A).real Aᶜ = 0 := by
    simp [measureReal_def, cond_apply hA]
  rw [tvDist_comm, hH.tvDist_eq, hfull, hzero, probReal_compl_eq_one_sub hA]
  ring

/-- Conditioning a probability law on eventually measurable events whose masses tend to one
converges to that law in total variation. -/
theorem tendsto_tvDist_cond {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {l : Filter ι} {A : ι → Set Ω}
    (hA : ∀ᶠ i in l, MeasurableSet (A i))
    (hmass : Tendsto (fun i ↦ μ.real (A i)) l (𝓝 1)) :
    Tendsto (fun i ↦ tvDist (cond μ (A i)) μ) l (𝓝 0) := by
  have h : Tendsto (fun i ↦ 2 * (1 - μ.real (A i))) l (𝓝 (2 * (1 - 1 : ℝ))) :=
    (tendsto_const_nhds.sub hmass).const_mul 2
  simp only [sub_self, mul_zero] at h
  apply h.congr'
  filter_upwards [hA, hmass.eventually (eventually_gt_nhds zero_lt_one)] with i hi hpos
  exact (μ.tvDist_cond_self hi
    ((measureReal_ne_zero_iff (measure_ne_top μ _)).mp hpos.ne')).symm

variable {α : Type*} [PartialOrder α] [MeasurableSpace α] (μ : Measure α)

/-- Including the lower endpoint does not change the conditional law when its atom vanishes. -/
@[simp]
theorem cond_Icc_eq_cond_Ioc {l r : α} (hl : μ {l} = 0) :
    ProbabilityTheory.cond μ (Icc l r) = ProbabilityTheory.cond μ (Ioc l r) :=
  ProbabilityTheory.cond_congr_ae (Ioc_ae_eq_Icc' hl).symm

/-- Excluding the upper endpoint does not change the conditional law when its atom vanishes. -/
@[simp]
theorem cond_Ioo_eq_cond_Ioc {l r : α} (hr : μ {r} = 0) :
    ProbabilityTheory.cond μ (Ioo l r) = ProbabilityTheory.cond μ (Ioc l r) :=
  ProbabilityTheory.cond_congr_ae (Ioo_ae_eq_Ioc' hr)

/-- The two half-open conditional laws agree when both endpoint atoms vanish. -/
@[simp]
theorem cond_Ico_eq_cond_Ioc {l r : α} (hl : μ {l} = 0) (hr : μ {r} = 0) :
    ProbabilityTheory.cond μ (Ico l r) = ProbabilityTheory.cond μ (Ioc l r) :=
  ProbabilityTheory.cond_congr_ae (Ico_ae_eq_Ioc' hl hr)

end MeasureTheory.Measure
