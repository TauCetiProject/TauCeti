/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Continuity of measures of intervals

Mathlib's `MeasureTheory.tendsto_measure_Ioc_atBot` lets the left endpoint of `(x, a]` go to
`-∞`. This file adds the analogous limits for `(x, a)` and `[x, a]`, and the right-continuity of
`x ↦ μ (-∞, x]` and `x ↦ μ (-∞, x)` at `a` from the right, where both tend to `μ (-∞, a]`.

## Main results

* `MeasureTheory.tendsto_measure_Ioo_atBot`, `MeasureTheory.tendsto_measure_Icc_atBot`:
  `μ (x, a) → μ (-∞, a)` and `μ [x, a] → μ (-∞, a]` as `x → -∞`.
* `MeasureTheory.tendsto_measure_Iio_nhdsGT`, `MeasureTheory.tendsto_measure_Iic_nhdsGT`:
  `μ (-∞, x) → μ (-∞, a]` and `μ (-∞, x] → μ (-∞, a]` as `x → a⁺`, provided some `μ (-∞, r)`,
  respectively `μ (-∞, r]`, with `r > a` is finite.
* `MeasureTheory.measurePreserving_sub_left_restrict_Ioc`: the reflection `s ↦ a + b - s` preserves
  Lebesgue measure restricted to `(a, b]`.
-/

public section

open Set Filter
open scoped Topology ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

section Preorder

variable [Preorder α] [(atBot : Filter α).IsCountablyGenerated]

/-- The measure of `(x, a)` tends to the measure of `(-∞, a)` as `x → -∞`. -/
theorem tendsto_measure_Ioo_atBot [NoMinOrder α] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ioo x a)) atBot (𝓝 (μ (Iio a))) := by
  rw [← iUnion_Ioo_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Ioo antitone_const)

/-- The measure of `[x, a]` tends to the measure of `(-∞, a]` as `x → -∞`. -/
theorem tendsto_measure_Icc_atBot (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Icc x a)) atBot (𝓝 (μ (Iic a))) := by
  rw [← iUnion_Icc_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Icc antitone_const)

end Preorder

section DenselyOrdered

variable [LinearOrder α] [DenselyOrdered α] [TopologicalSpace α] [OrderTopology α]
  [FirstCountableTopology α] [OpensMeasurableSpace α] {a : α}

/-- If some `μ (-∞, r)` with `r > a` is finite, then the measure of `(-∞, x)` tends to the
measure of `(-∞, a]` as `x → a⁺`. -/
theorem tendsto_measure_Iio_nhdsGT (hf : ∃ r > a, μ (Iio r) ≠ ∞) :
    Tendsto (fun x => μ (Iio x)) (𝓝[>] a) (𝓝 (μ (Iic a))) := by
  have h : ⋂ r > a, Iio r = Iic a := by
    ext x
    simp only [mem_iInter, mem_Iio, mem_Iic]
    exact ⟨fun h => le_of_forall_gt_imp_ge_of_dense fun r hr => (h r hr).le,
      fun h r hr => h.trans_lt hr⟩
  rw [← h]
  exact tendsto_measure_biInter_gt (fun _ _ => measurableSet_Iio.nullMeasurableSet)
    (fun _ _ _ hij => Iio_subset_Iio hij) hf

/-- If some `μ (-∞, r]` with `r > a` is finite, then `x ↦ μ (-∞, x]` is right-continuous
at `a`. -/
theorem tendsto_measure_Iic_nhdsGT (hf : ∃ r > a, μ (Iic r) ≠ ∞) :
    Tendsto (fun x => μ (Iic x)) (𝓝[>] a) (𝓝 (μ (Iic a))) := by
  have h : ⋂ r > a, Iic r = Iic a := by
    ext x
    simp only [mem_iInter, mem_Iic]
    exact ⟨le_of_forall_gt_imp_ge_of_dense, fun h r hr => h.trans hr.le⟩
  rw [← h]
  exact tendsto_measure_biInter_gt (fun _ _ => measurableSet_Iic.nullMeasurableSet)
    (fun _ _ _ hij => Iic_subset_Iic.2 hij) hf

end DenselyOrdered

/-- The reflection `s ↦ a + b - s` of the interval `(a, b]` preserves Lebesgue measure restricted
to `(a, b]`. -/
theorem measurePreserving_sub_left_restrict_Ioc (a b : ℝ) :
    MeasurePreserving (fun s : ℝ => a + b - s) (volume.restrict (Ioc a b))
      (volume.restrict (Ioc a b)) := by
  have hpre : (fun s : ℝ => a + b - s) ⁻¹' Ioc a b = Ico a b := by
    ext s
    simp only [mem_preimage, mem_Ioc, mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hmp := ((volume : Measure ℝ).measurePreserving_sub_left (a + b)).restrict_preimage
    (measurableSet_Ioc (a := a) (b := b))
  rwa [hpre, Measure.restrict_congr_set Ico_ae_eq_Ioc] at hmp

end MeasureTheory
