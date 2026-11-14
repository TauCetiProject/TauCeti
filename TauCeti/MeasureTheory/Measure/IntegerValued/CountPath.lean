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
# Count paths of integer-valued measures on an ordered space

For a measure `μ` on an ordered space and a left endpoint `a`, the natural count of occurrences
in `(a, t]` is `⌊(μ (Ioc a t)).toNNReal⌋₊`. When `μ` is locally finite, the count is nondecreasing
and right-continuous in `t`. If moreover `μ` is integer-valued, the count jumps at `t > a` by
exactly the mass `μ {t}`, so an atom of mass at most one at `t` bounds the jump of the count at
`t` by one. On `ℝ≥0` with `a = 0` these are the path properties of the counting process of a
locally finite simple point measure; no occurrence at zero is counted.

`TauCeti.Probability.exists_measure_of_countingPath` is the converse construction of a counting
measure from a nondecreasing right-continuous natural-valued path.

## Main results

* `MeasureTheory.Measure.monotone_natFloor_Ioc`: the count of a locally finite measure is
  nondecreasing.
* `MeasureTheory.Measure.continuousWithinAt_natFloor_Ioc_Ici`: the count of a locally finite
  measure is right-continuous.
* `MeasureTheory.Measure.IsIntegerValued.eventually_natFloor_Ioc_add_eq_nhdsLT`: just before
  `t > a`, the count of a locally finite integer-valued measure plus the mass of `{t}` is the
  count at `t`.
* `MeasureTheory.Measure.IsIntegerValued.eventually_natFloor_Ioc_le_add_one_nhdsLT`: if
  `μ {t} ≤ 1`, then just before `t` the count is at least its value at `t` minus one.
-/

public section

open Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

variable {α : Type*} {mα : MeasurableSpace α}

/-- The count `t ↦ ⌊(μ (Ioc a t)).toNNReal⌋₊` of a locally finite measure is nondecreasing. -/
theorem monotone_natFloor_Ioc [Preorder α] [TopologicalSpace α] [CompactIccSpace α]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] (a : α) :
    Monotone fun t ↦ ⌊(μ (Ioc a t)).toNNReal⌋₊ := fun _ _ hst ↦
  Nat.floor_mono (ENNReal.toNNReal_mono measure_Ioc_lt_top.ne
    (measure_mono (Ioc_subset_Ioc_right hst)))

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α]
  [CompactIccSpace α] [OpensMeasurableSpace α]

/-- The count `t ↦ ⌊(μ (Ioc a t)).toNNReal⌋₊` of a locally finite measure is right-continuous:
it is constant on a right neighbourhood of every time. -/
theorem continuousWithinAt_natFloor_Ioc_Ici (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (a t : α) : ContinuousWithinAt (fun s ↦ ⌊(μ (Ioc a s)).toNNReal⌋₊) (Ici t) t := by
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  rcases (Ioi t).eq_empty_or_nonempty with hempty | ⟨r, hr⟩
  · rw [hempty, nhdsWithin_empty]
    exact tendsto_bot
  -- Continuity from above of the window masses, with the mass up to `a` removed.
  have hlim : Tendsto (fun s ↦ μ (Ioc a s)) (𝓝[>] t) (𝓝 (μ (Ioc a t))) := by
    simpa only [restrict_apply measurableSet_Iic, Iic_inter_Ioi] using
      tendsto_measure_Iic_nhdsGT (μ := μ.restrict (Ioi a)) ⟨r, hr, by
        rw [restrict_apply measurableSet_Iic, Iic_inter_Ioi]
        exact measure_Ioc_lt_top.ne⟩
  have hlt : μ (Ioc a t) < ((⌊(μ (Ioc a t)).toNNReal⌋₊ + 1 : ℕ) : ℝ≥0) := by
    rw [← ENNReal.coe_toNNReal measure_Ioc_lt_top.ne, ENNReal.coe_lt_coe]
    exact_mod_cast Nat.lt_floor_add_one _
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hlim.eventually (gt_mem_nhds hlt), self_mem_nhdsWithin] with s hs hts
  have hsucc : ⌊(μ (Ioc a s)).toNNReal⌋₊ < ⌊(μ (Ioc a t)).toNNReal⌋₊ + 1 :=
    (Nat.floor_lt zero_le).2 (by exact_mod_cast ENNReal.toNNReal_lt_of_lt_coe hs)
  exact le_antisymm (μ.monotone_natFloor_Ioc a (le_of_lt hts)) (Nat.lt_succ_iff.mp hsucc)

variable {μ : Measure α} [IsLocallyFiniteMeasure μ]

/-- For a locally finite integer-valued measure and `a < t`, the count
`s ↦ ⌊(μ (Ioc a s)).toNNReal⌋₊` jumps at `t` by exactly the mass of `{t}`: for all `s < t` close
enough to `t`, the count at `s` plus `⌊(μ {t}).toNNReal⌋₊` is the count at `t`. -/
theorem IsIntegerValued.eventually_natFloor_Ioc_add_eq_nhdsLT (hμ : μ.IsIntegerValued)
    {a t : α} (hat : a < t) :
    ∀ᶠ s in 𝓝[<] t,
      ⌊(μ (Ioc a s)).toNNReal⌋₊ + ⌊(μ {t}).toNNReal⌋₊ = ⌊(μ (Ioc a t)).toNNReal⌋₊ := by
  have ht : μ {t} < ∞ :=
    (measure_mono (singleton_subset_iff.2 (right_mem_Ioc.2 hat))).trans_lt measure_Ioc_lt_top
  -- Continuity from above along windows `(s, t]` shrinking to the atom `{t}`.
  have hlim := tendsto_measure_Ioc_nhdsLT (μ := μ) ⟨a, hat, measure_Ioc_lt_top.ne⟩
  rw [← hμ.natCast_natFloor_eq ht] at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds (ENNReal.lt_add_right (ENNReal.natCast_ne_top _)
    one_ne_zero)), Ioo_mem_nhdsLT hat] with s hs has
  have hle : μ {t} ≤ μ (Ioc s t) := measure_mono (singleton_subset_iff.2 (right_mem_Ioc.2 has.2))
  rw [← hμ.natCast_natFloor_eq ht, ← hμ.natCast_natFloor_eq (measure_Ioc_lt_top (a := s))]
    at hle
  rw [← hμ.natCast_natFloor_eq (measure_Ioc_lt_top (a := s))] at hs
  have hwin : ⌊(μ (Ioc s t)).toNNReal⌋₊ = ⌊(μ {t}).toNNReal⌋₊ := by
    have hle' : ⌊(μ {t}).toNNReal⌋₊ ≤ ⌊(μ (Ioc s t)).toNNReal⌋₊ := by exact_mod_cast hle
    have hs' : ⌊(μ (Ioc s t)).toNNReal⌋₊ < ⌊(μ {t}).toNNReal⌋₊ + 1 := by exact_mod_cast hs
    omega
  have hsplit : μ (Ioc a t) = μ (Ioc a s) + μ (Ioc s t) := by
    rw [← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Ioc_union_Ioc_eq_Ioc has.1.le has.2.le]
  rw [← hμ.natCast_natFloor_eq (measure_Ioc_lt_top (a := a) (b := t)),
    ← hμ.natCast_natFloor_eq (measure_Ioc_lt_top (a := a) (b := s)),
    ← hμ.natCast_natFloor_eq (measure_Ioc_lt_top (a := s) (b := t)), hwin] at hsplit
  exact_mod_cast hsplit.symm

/-- If a locally finite integer-valued measure has mass at most one at `t`, then the count
`s ↦ ⌊(μ (Ioc a s)).toNNReal⌋₊` jumps by at most one at `t`: for all `s < t` close enough to `t`,
the count at `t` is at most the count at `s` plus one. -/
theorem IsIntegerValued.eventually_natFloor_Ioc_le_add_one_nhdsLT (hμ : μ.IsIntegerValued)
    {a t : α} (ht : μ {t} ≤ 1) :
    ∀ᶠ s in 𝓝[<] t, ⌊(μ (Ioc a t)).toNNReal⌋₊ ≤ ⌊(μ (Ioc a s)).toNNReal⌋₊ + 1 := by
  rcases lt_or_ge a t with hat | hta
  · filter_upwards [hμ.eventually_natFloor_Ioc_add_eq_nhdsLT hat] with s hs
    rw [← hs]
    gcongr
    exact Nat.floor_le_one_of_le_one
      ((ENNReal.toNNReal_mono ENNReal.one_ne_top ht).trans_eq ENNReal.toNNReal_one)
  · exact Eventually.of_forall fun _ ↦ by simp [Ioc_eq_empty_of_le hta]

end MeasureTheory.Measure
