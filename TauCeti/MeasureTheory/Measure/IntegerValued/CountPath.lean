/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Count paths of integer-valued measures on the half-line

For a measure `μ` on `ℝ≥0`, the natural count of occurrences in `(0,t]` is
`⌊(μ (Ioc 0 t)).toNNReal⌋₊`. It vanishes at zero, and it is nondecreasing when `μ` is locally
finite. If moreover `μ` is integer-valued, the count is right-continuous, and an atom of mass at
most one at `t` bounds the jump of the count at `t` by one. These are the path properties of the
counting process of a locally finite simple point measure; no occurrence at zero is counted.

`TauCeti.Probability.exists_measure_of_countingPath` is the converse construction of a counting
measure from a nondecreasing right-continuous natural-valued path.

## Main results

* `MeasureTheory.Measure.monotone_natFloor_Ioc`: the count of a locally finite measure is
  nondecreasing.
* `MeasureTheory.Measure.IsIntegerValued.continuousWithinAt_natFloor_Ioc`: the count of a
  locally finite integer-valued measure is right-continuous.
* `MeasureTheory.Measure.IsIntegerValued.eventually_natFloor_Ioc_le_add_one`: if `μ {t} ≤ 1`,
  then just before `t` the count is at least its value at `t` minus one.
-/

public section

open Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0}

/-- The count `t ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊` of a locally finite measure on the half-line is
nondecreasing. -/
theorem monotone_natFloor_Ioc [IsLocallyFiniteMeasure μ] :
    Monotone fun t ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊ := fun _ _ hst ↦
  Nat.floor_mono (ENNReal.toNNReal_mono measure_Ioc_lt_top.ne
    (measure_mono (Ioc_subset_Ioc_right hst)))

/-- The count `t ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊` of a locally finite integer-valued measure on the
half-line is right-continuous: it is constant on a right neighbourhood of every time. -/
theorem IsIntegerValued.continuousWithinAt_natFloor_Ioc [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) (t : ℝ≥0) :
    ContinuousWithinAt (fun s ↦ ⌊(μ (Ioc 0 s)).toNNReal⌋₊) (Ici t) t := by
  set f : ℝ≥0 → ℕ := fun s ↦ ⌊(μ (Ioc 0 s)).toNNReal⌋₊
  have hcast (s : ℝ≥0) : (f s : ℝ≥0∞) = μ (Ioc 0 s) :=
    hμ.natCast_natFloor_eq measurableSet_Ioc measure_Ioc_lt_top
  -- Continuity from above of the window masses, with the atom at zero removed.
  have hlim : Tendsto (fun s ↦ μ (Ioc 0 s)) (𝓝[>] t) (𝓝 (μ (Ioc 0 t))) := by
    have h := tendsto_measure_Iic_nhdsGT (μ := μ.restrict (Ioi 0)) (a := t)
      ⟨t + 1, lt_add_one t, by
        rw [restrict_apply measurableSet_Iic, Iic_inter_Ioi]
        exact measure_Ioc_lt_top.ne⟩
    simpa only [restrict_apply measurableSet_Iic, Iic_inter_Ioi] using h
  have hlt : μ (Ioc 0 t) < f t + 1 := by
    rw [← hcast]
    exact ENNReal.lt_add_right (ENNReal.natCast_ne_top _) one_ne_zero
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hlim.eventually (gt_mem_nhds hlt), self_mem_nhdsWithin] with s hs hts
  have hle : f t ≤ f s := monotone_natFloor_Ioc (le_of_lt hts)
  have hsucc : f s < f t + 1 := by
    rw [← hcast] at hs
    exact_mod_cast hs
  exact le_antisymm hle (Nat.lt_succ_iff.mp hsucc)

/-- If a locally finite integer-valued measure on the half-line has mass at most one at `t`,
then the count `s ↦ ⌊(μ (Ioc 0 s)).toNNReal⌋₊` jumps by at most one at `t`: for all `s < t`
close enough to `t`, the count at `t` is at most the count at `s` plus one. -/
theorem IsIntegerValued.eventually_natFloor_Ioc_le_add_one [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) {t : ℝ≥0} (ht : μ {t} ≤ 1) :
    ∀ᶠ s in 𝓝[<] t, ⌊(μ (Ioc 0 t)).toNNReal⌋₊ ≤ ⌊(μ (Ioc 0 s)).toNNReal⌋₊ + 1 := by
  rcases eq_zero_or_pos t with rfl | ht0
  · exact Eventually.of_forall fun _ ↦ by simp
  have hcast (s : ℝ≥0) : (⌊(μ (Ioc 0 s)).toNNReal⌋₊ : ℝ≥0∞) = μ (Ioc 0 s) :=
    hμ.natCast_natFloor_eq measurableSet_Ioc measure_Ioc_lt_top
  -- Continuity from above along windows `(u n, t]` shrinking to the atom `{t}`.
  obtain ⟨u, hu_mono, hu, hu_lim⟩ := exists_seq_strictMono_tendsto' ht0
  have hinter : ⋂ n, Ioc (u n) t = {t} := by
    ext x
    simp only [mem_iInter, mem_Ioc, mem_singleton_iff]
    refine ⟨fun h ↦ le_antisymm (h 0).2 (le_of_tendsto' hu_lim fun n ↦ (h n).1.le), ?_⟩
    rintro rfl n
    exact ⟨(hu n).2, le_rfl⟩
  have hmass := tendsto_measure_iInter_atTop (μ := μ) (s := fun n ↦ Ioc (u n) t)
    (fun _ ↦ measurableSet_Ioc.nullMeasurableSet)
    (fun _ _ hmn ↦ Ioc_subset_Ioc_left (hu_mono.monotone hmn)) ⟨0, measure_Ioc_lt_top.ne⟩
  rw [hinter] at hmass
  obtain ⟨n, hn⟩ := (hmass.eventually (gt_mem_nhds (ht.trans_lt ENNReal.one_lt_two))).exists
  filter_upwards [Ioo_mem_nhdsLT (hu n).2] with s hs
  obtain ⟨k, hk⟩ := hμ.exists_eq_natCast measurableSet_Ioc (measure_Ioc_lt_top (a := s) (b := t))
  have hk2 : k < 2 := by
    have hwin : μ (Ioc s t) < 2 := (measure_mono (Ioc_subset_Ioc_left hs.1.le)).trans_lt hn
    rw [hk] at hwin
    exact_mod_cast hwin
  have hsplit : (⌊(μ (Ioc 0 t)).toNNReal⌋₊ : ℝ≥0∞) = ⌊(μ (Ioc 0 s)).toNNReal⌋₊ + k := by
    rw [hcast, hcast, ← hk, ← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc (a := 0) bot_le hs.2.le]
  have hsplit' : ⌊(μ (Ioc 0 t)).toNNReal⌋₊ = ⌊(μ (Ioc 0 s)).toNNReal⌋₊ + k := by
    exact_mod_cast hsplit
  omega

end MeasureTheory.Measure
