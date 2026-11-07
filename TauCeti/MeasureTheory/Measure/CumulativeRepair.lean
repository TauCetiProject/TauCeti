/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Repairing an explosive cumulative measure

An atomless measure need not have a continuous extended-valued cumulative function:
it can have infinite mass immediately to the right of a point. Restricting it to the
points where its original cumulative mass is finite removes this right-hand explosion.
The repaired cumulative function is continuous, including at points where it tends to infinity.

For a weighted time measure this gives continuity of the accumulated energy after
turning an integrand off wherever its original accumulated energy is infinite. This
is the deterministic continuity input for stopping stochastic integrals at energy levels.
-/

public section

open Filter Set
open scoped Topology ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [FirstCountableTopology α] [DenselyOrdered α]
  [MeasurableSpace α] [OpensMeasurableSpace α]

/-- Removing points with infinite original cumulative mass makes the cumulative function
of an atomless measure continuous, with values in `ℝ≥0∞`. No local finiteness is assumed. -/
theorem continuous_cumulative_restrict_lt_top (μ : Measure α) [NullSingletonClass μ] :
    Continuous (fun t ↦ (μ.restrict {s | μ (Iic s) < ∞}) (Iic t)) := by
  let ν := μ.restrict {s | μ (Iic s) < ∞}
  rw [continuous_iff_continuousAt]
  intro t
  refine continuousAt_iff_continuous_left'_right'.mpr ⟨?_, ?_⟩
  · -- Continuity from below needs no finiteness, even at an infinite value.
    have : IsCountablyGenerated (atTop : Filter (Iio t)) := by
      rw [← comap_coe_Iio_nhdsLT t]
      infer_instance
    have hUnion : (⋃ x : Iio t, Iic (x : α)) = Iio t := by
      ext y
      simp only [mem_iUnion, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨x, hx⟩
        exact hx.trans_lt x.property
      · intro hy
        obtain ⟨x, hyx, hxt⟩ := exists_between hy
        exact ⟨⟨x, hxt⟩, hyx.le⟩
    have h := tendsto_measure_iUnion_atTop (μ := ν)
      (s := fun x : Iio t ↦ Iic (x : α)) (fun _ _ h ↦ Iic_subset_Iic.mpr h)
    rw [hUnion, measure_congr Iio_ae_eq_Iic] at h
    exact (tendsto_comp_coe_Iio_atTop (f := fun x ↦ ν (Iic x))).mp h
  · have : IsCountablyGenerated (atBot : Filter (Ioi t)) := by
      rw [← comap_coe_Ioi_nhdsGT t]
      infer_instance
    by_cases hfinite : ∃ u, t < u ∧ μ (Iic u) < ∞
    · -- One finite original tail supplies continuity from above locally.
      obtain ⟨u, htu, hu⟩ := hfinite
      have hInter : (⋂ x : Ioi t, Iic (x : α)) = Iic t := by
        ext y
        simp only [mem_iInter, mem_Iic]
        constructor
        · intro hy
          by_contra hyt
          obtain ⟨x, htx, hxy⟩ := exists_between (lt_of_not_ge hyt)
          exact hxy.not_ge (hy ⟨x, htx⟩)
        · intro hy x
          exact hy.trans x.property.le
      have h := tendsto_measure_iInter_atBot (μ := ν)
        (s := fun x : Ioi t ↦ Iic (x : α)) (fun _ ↦ measurableSet_Iic.nullMeasurableSet)
        (fun _ _ h ↦ Iic_subset_Iic.mpr h)
        ⟨⟨u, htu⟩, ne_top_of_le_ne_top hu.ne (Measure.restrict_le_self _)⟩
      rw [hInter] at h
      exact (tendsto_comp_coe_Ioi_atBot (f := fun x ↦ ν (Iic x))).mp h
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

end MeasureTheory.Measure
