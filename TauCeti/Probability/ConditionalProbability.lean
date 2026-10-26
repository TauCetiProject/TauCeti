/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
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
Conditional measures on intervals agree across endpoint conventions whenever the relevant
endpoint atoms vanish. These identities apply to any partially ordered measurable space,
including atomless laws and atomic laws with null endpoints.

## Main results

* `ProbabilityTheory.sum_meas_smul_cond_fiber_of_countable`
* `ProbabilityTheory.cond_congr_ae`
* `ProbabilityTheory.integrable_cond_of_norm_le`
* `ProbabilityTheory.map_cond_preimage`
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
