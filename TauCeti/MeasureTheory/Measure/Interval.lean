/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.AtTopBotIxx

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
* `MeasureTheory.Measure.continuousWithinAt_Iio_measure_Iic`: the cumulative function of an
  atomless measure is left-continuous, without a finiteness assumption.
* `MeasureTheory.Measure.continuous_cumulative_restrict_lt_top`: restricting an atomless
  measure to points with finite original cumulative mass makes its extended-valued cumulative
  function continuous, even in the presence of immediate right-hand explosion.
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

namespace Measure

omit [OpensMeasurableSpace α] in
/-- The cumulative function of an atomless measure is left-continuous, with values in
`ℝ≥0∞`. No finiteness assumption is needed. -/
theorem continuousWithinAt_Iio_measure_Iic (μ : Measure α) [NullSingletonClass μ] (a : α) :
    ContinuousWithinAt (fun x ↦ μ (Iic x)) (Iio a) a := by
  have : IsCountablyGenerated (atTop : Filter (Iio a)) := by
    rw [← comap_coe_Iio_nhdsLT a]
    infer_instance
  have hUnion : (⋃ x : Iio a, Iic (x : α)) = Iio a := by
    rw [iUnion_coe_set]
    exact isLUB_Iio.biUnion_Iic_eq_Iio (lt_irrefl a)
  have h := tendsto_measure_iUnion_atTop (μ := μ)
    (s := fun x : Iio a ↦ Iic (x : α)) (fun _ _ h ↦ Iic_subset_Iic.mpr h)
  rw [hUnion, measure_congr Iio_ae_eq_Iic] at h
  exact (tendsto_comp_coe_Iio_atTop (f := fun x ↦ μ (Iic x))).mp h

/-- Removing points with infinite original cumulative mass makes the cumulative function
of an atomless measure continuous, with values in `ℝ≥0∞`. No local finiteness is assumed. -/
theorem continuous_cumulative_restrict_lt_top (μ : Measure α) [NullSingletonClass μ] :
    Continuous (fun t ↦ (μ.restrict {s | μ (Iic s) < ∞}) (Iic t)) := by
  let ν := μ.restrict {s | μ (Iic s) < ∞}
  rw [continuous_iff_continuousAt]
  intro t
  refine continuousAt_iff_continuous_left'_right'.mpr
    ⟨ν.continuousWithinAt_Iio_measure_Iic t, ?_⟩
  by_cases hfinite : ∃ u, t < u ∧ μ (Iic u) < ∞
  · -- One finite original tail supplies continuity from above locally.
    obtain ⟨u, htu, hu⟩ := hfinite
    exact tendsto_measure_Iic_nhdsGT (μ := ν)
      ⟨u, htu, ne_top_of_le_ne_top hu.ne (Measure.restrict_le_self _)⟩
  · -- Otherwise the cutoff removes everything strictly to the right of `t`.
    have heq : ∀ x ∈ Ioi t, ν (Iic x) = ν (Iic t) := by
      intro x hx
      simp only [ν, Measure.restrict_apply measurableSet_Iic]
      congr 1
      ext y
      simp only [mem_inter_iff, mem_Iic, mem_ofPred_eq]
      constructor
      · rintro ⟨hyx, hy⟩
        exact ⟨le_of_not_gt (fun hty ↦ hfinite ⟨y, hty, hy⟩), hy⟩
      · exact fun ⟨hyt, hy⟩ ↦ ⟨hyt.trans hx.le, hy⟩
    exact continuousWithinAt_const.congr (fun x hx ↦ heq x hx) rfl

end Measure

end DenselyOrdered

end MeasureTheory
