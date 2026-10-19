/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
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

Conditioning on almost-everywhere equal events gives equal conditional measures.
Conditional measures on intervals agree across endpoint conventions whenever the relevant
endpoint atoms vanish. These identities apply to any partially ordered measurable space,
including atomless laws and atomic laws with null endpoints.

## Main results

* `ProbabilityTheory.sum_meas_smul_cond_fiber_of_countable`
* `ProbabilityTheory.cond_congr_ae`
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
