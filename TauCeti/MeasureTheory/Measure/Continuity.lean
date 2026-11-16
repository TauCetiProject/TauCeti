/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.LeftRight

/-!
# Continuity of the measure of strict superlevel sets

For a measure `μ` and a function `f` into a linear order `β` with the order topology, the map
`s ↦ μ {y | s < f y}` is the distribution function of `f`. We assume that `β` is first countable
and show that this map is right continuous at every point `t`, with no measurability, finiteness
or integrability hypothesis on `μ` or `f`.

The point `t` is right isolated if the right neighbourhood filter `𝓝[>] t` is trivial, which
happens when `t` is maximal or has an immediate successor; right continuity is then automatic.
Otherwise `t` is a right accumulation point, and right continuity is continuity from below of `μ`
along the sets `{s < f}` for `s ↓ t`, which increase to `{t < f}`. In a densely ordered `β`, a
point `t` with `c < μ {y | t < f y}` is not maximal, hence is a right accumulation point, which
gives a strictly higher level `s > t` with `c < μ {y | s < f y}`.

## Main statements

* `MeasureTheory.Measure.continuousWithinAt_Ici_measure_setOf_lt`: right continuity of
  `s ↦ μ {y | s < f y}`.
* `MeasureTheory.Measure.exists_lt_lt_measure_setOf_lt`: if `c < μ {y | t < f y}`, then
  `c < μ {y | s < f y}` for some `s > t`, when the order is dense.
-/

@[expose] public section

open Set Filter Topology
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
  [FirstCountableTopology β] (μ : Measure α) {f : α → β} {t : β}

/-- **Right continuity of the distribution function.** For every `t`, the map
`s ↦ μ {y | s < f y}` is continuous within `Ici t` at `t`, for an arbitrary measure `μ` and an
arbitrary function `f`, in a first countable linear order with the order topology. -/
theorem continuousWithinAt_Ici_measure_setOf_lt :
    ContinuousWithinAt (fun s ↦ μ {y | s < f y}) (Ici t) t := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  by_cases ht : Order.IsPredPrelimit t
  · have : (atBot : Filter (Ioi t)).IsCountablyGenerated := by
      rw [← comap_coe_Ioi_nhdsGT t ht]
      infer_instance
    have hunion : {y | t < f y} = ⋃ s : Ioi t, {y | (s : β) < f y} := by
      ext y
      simp only [mem_ofPred_eq, mem_iUnion, Subtype.exists, mem_Ioi, exists_prop]
      refine ⟨fun hy ↦ ?_, fun ⟨s, hts, hsy⟩ ↦ hts.trans hsy⟩
      obtain ⟨s, hts, hsy⟩ := (not_covBy_iff hy).1 (ht _)
      exact ⟨s, hts, hsy⟩
    have hanti : Antitone fun s : Ioi t ↦ {y | (s : β) < f y} :=
      fun a b hab y hy ↦ (Subtype.coe_le_coe.2 hab).trans_lt hy
    rw [ContinuousWithinAt, ← map_coe_Ioi_atBot t ht, tendsto_map'_iff, hunion]
    exact tendsto_measure_iUnion_atBot hanti
  · obtain ⟨b, hb⟩ := Order.not_isPredPrelimit_iff.1 ht
    simp [ContinuousWithinAt, hb.nhdsGT]

/-- In a densely ordered first countable linear order with the order topology, if
`c < μ {y | t < f y}`, then `c < μ {y | s < f y}` for some `s > t`. No measurability or finiteness
hypothesis on `μ` or `f` is needed. -/
theorem exists_lt_lt_measure_setOf_lt [DenselyOrdered β] {c : ℝ≥0∞} (h : c < μ {y | t < f y}) :
    ∃ s, t < s ∧ c < μ {y | s < f y} := by
  obtain ⟨y, hy⟩ := nonempty_of_measure_ne_zero (zero_le.trans_lt h).ne'
  have : (𝓝[>] t).NeBot := nhdsGT_neBot_of_exists_gt ⟨f y, hy⟩
  have hc := (continuousWithinAt_Ioi_iff_Ici.2 (continuousWithinAt_Ici_measure_setOf_lt μ (f := f)
    (t := t))).tendsto.eventually_const_lt h
  exact (hc.and self_mem_nhdsWithin).exists.imp fun s hs ↦ ⟨hs.2, hs.1⟩

end MeasureTheory.Measure
