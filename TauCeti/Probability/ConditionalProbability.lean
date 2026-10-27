/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Interval

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
Conditioning a probability measure away from a single point removes that atom and rescales the
rest by `1 / (1 - μ {a})`; this computes the masses of, and integrals against, the conditioned
measure. Conditional measures on intervals agree across endpoint conventions whenever the relevant
endpoint atoms vanish. These identities apply to any partially ordered measurable space,
including atomless laws and atomic laws with null endpoints.

## Main results

* `ProbabilityTheory.sum_meas_smul_cond_fiber_of_countable`
* `ProbabilityTheory.cond_congr_ae`
* `ProbabilityTheory.integrable_cond_of_norm_le`
* `ProbabilityTheory.map_cond_preimage`
* `ProbabilityTheory.cond_compl_singleton_real`,
  `ProbabilityTheory.cond_compl_singleton_real_singleton`,
  `ProbabilityTheory.integrable_cond_compl_singleton_iff`,
  `ProbabilityTheory.integral_cond_compl_singleton`
* `MeasureTheory.Measure.cond_Icc_eq_cond_Ioc`, `MeasureTheory.Measure.cond_Ioo_eq_cond_Ioc`,
  `MeasureTheory.Measure.cond_Ico_eq_cond_Ioc`
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]

/-- Conditioning on almost-everywhere equal events gives equal conditional measures. -/
theorem cond_congr_ae {μ : Measure Ω} {s t : Set Ω} (h : s =ᵐ[μ] t) :
    μ[|s] = μ[|t] := by
  rw [cond, cond, measure_congr h, Measure.restrict_congr_set h]

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
        simp only [Measure.sum_apply _ hE, Measure.smul_apply, smul_eq_mul]
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
    prob_compl_eq_one_sub (measurableSet_singleton a), ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
    ← sdiff_eq_compl_inter, div_eq_inv_mul, measureReal_def, measureReal_def]

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
