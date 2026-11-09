/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Interval
public import TauCeti.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Occurrence times on the half-line

`Measure.occurrenceTime μ n` is the infimum of times at which the cumulative mass of
`μ` reaches `n + 1`, with value infinity if this never happens. For a locally finite
counting measure this enumerates occurrences, starting at index zero and retaining
multiplicities. It does not insert an artificial occurrence at zero.

The construction is measurable for the evaluation σ-algebra on measures. For locally
finite measures, its sublevel sets are exactly the corresponding count events.
The definition also applies to noninteger measures, where it is a unit-mass threshold
inverse rather than an enumeration of atoms.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge
  University Press, 2018, Chapters 2 and 7, for counting measures and arrival times.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

/-- The infimum of times with cumulative mass at least `n + 1`, or infinity if
there are none. For locally finite counting measures this is occurrence `n`, indexed
from zero, with repeated locations retained. -/
noncomputable def occurrenceTime (μ : Measure ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : (n + 1 : ℝ≥0∞) ≤ μ (Iic t)), (t : ℝ≥0∞)

/-- Occurrence times are the infima of the times with sufficient cumulative mass. -/
theorem occurrenceTime_def (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceTime n = ⨅ (t : ℝ≥0) (_ : (n + 1 : ℝ≥0∞) ≤ μ (Iic t)), (t : ℝ≥0∞) :=
  (rfl)

/-- An occurrence is strictly before a bound exactly when some earlier finite time
already has sufficient cumulative mass. No local finiteness is required. -/
theorem occurrenceTime_lt_iff (μ : Measure ℝ≥0) (n : ℕ) (b : ℝ≥0∞) :
    μ.occurrenceTime n < b ↔
      ∃ t : ℝ≥0, (t : ℝ≥0∞) < b ∧ (n + 1 : ℝ≥0∞) ≤ μ (Iic t) := by
  simp only [occurrenceTime_def, iInf_lt_iff]
  exact ⟨fun ⟨t, ht, hb⟩ => ⟨t, hb, ht⟩, fun ⟨t, hb, ht⟩ => ⟨t, ht, hb⟩⟩

/-- Sufficient cumulative mass at a time bounds the corresponding occurrence time. -/
theorem occurrenceTime_le_of_le (μ : Measure ℝ≥0) {n : ℕ} {t : ℝ≥0}
    (h : (n + 1 : ℝ≥0∞) ≤ μ (Iic t)) : μ.occurrenceTime n ≤ t :=
  iInf_le_of_le t (iInf_le_of_le h le_rfl)

/-- Occurrences are ordered, allowing equal times for multiple occurrences. -/
theorem monotone_occurrenceTime (μ : Measure ℝ≥0) : Monotone μ.occurrenceTime := by
  intro m n hmn
  simp only [occurrenceTime_def, le_iInf_iff]
  intro t ht
  have hmn' : (m + 1 : ℝ≥0∞) ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
  exact μ.occurrenceTime_le_of_le (hmn'.trans ht)

/-- Adding mass can only move occurrence times earlier. -/
theorem occurrenceTime_antitone {μ ν : Measure ℝ≥0} (h : μ ≤ ν) (n : ℕ) :
    ν.occurrenceTime n ≤ μ.occurrenceTime n := by
  simp only [occurrenceTime_def, le_iInf_iff]
  intro t ht
  exact ν.occurrenceTime_le_of_le (ht.trans (h _))

/-- Infinity records that the indicated cumulative-mass threshold is never reached. -/
theorem occurrenceTime_eq_top_iff (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceTime n = ∞ ↔ ∀ t, μ (Iic t) < (n + 1 : ℝ≥0∞) := by
  rw [← not_lt_top_iff, occurrenceTime_lt_iff]
  simp

@[simp]
theorem occurrenceTime_zero_measure (n : ℕ) : (0 : Measure ℝ≥0).occurrenceTime n = ∞ := by
  simp [occurrenceTime_eq_top_iff]

/-- For a locally finite measure the threshold is attained at every finite occurrence
time. The closed endpoint includes all occurrences at the observation time. -/
@[simp]
theorem occurrenceTime_le_iff (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ]
    (n : ℕ) (t : ℝ≥0) :
    μ.occurrenceTime n ≤ t ↔ (n + 1 : ℝ≥0∞) ≤ μ (Iic t) := by
  refine ⟨fun h => ?_, μ.occurrenceTime_le_of_le⟩
  apply ge_of_tendsto (tendsto_measure_Iic_nhdsGT (μ := μ)
    ⟨t + 1, lt_add_one t, (measure_Iic_lt_top (μ := μ)).ne⟩)
  filter_upwards [self_mem_nhdsWithin] with s hs
  obtain ⟨u, hus, hu⟩ := (μ.occurrenceTime_lt_iff n s).1
    (h.trans_lt (by exact_mod_cast hs))
  exact hu.trans (measure_mono (Iic_subset_Iic.2 (by exact_mod_cast hus.le)))

/-- Restricting to a closed observation window retains exactly the occurrences in
that window; all subsequent occurrence times become infinite. -/
@[simp]
theorem occurrenceTime_restrict_Iic (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ]
    (b : ℝ≥0) (n : ℕ) :
    (μ.restrict (Iic b)).occurrenceTime n =
      if μ.occurrenceTime n ≤ b then μ.occurrenceTime n else ∞ := by
  have : IsLocallyFiniteMeasure (μ.restrict (Iic b)) :=
    isLocallyFiniteMeasure_of_le Measure.restrict_le_self
  apply ENNReal.eq_of_forall_le_nnreal_iff
  intro t
  rw [occurrenceTime_le_iff, Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic,
    ← occurrenceTime_le_iff]
  by_cases h : μ.occurrenceTime n ≤ b
  · simp [h, ENNReal.coe_min, le_min_iff]
  · simp [h, ENNReal.coe_min, le_min_iff]

private theorem occurrenceTime_lt_iff_rat (μ : Measure ℝ≥0) (n : ℕ) (b : ℝ≥0∞) :
    μ.occurrenceTime n < b ↔ ∃ q : ℚ,
      ENNReal.ofReal (q : ℝ) < b ∧
        (n + 1 : ℝ≥0∞) ≤ μ (Iic (Real.toNNReal (q : ℝ))) := by
  refine ⟨fun h => ?_, fun ⟨q, hq, hm⟩ => ?_⟩
  · obtain ⟨t, htb, ht⟩ := (μ.occurrenceTime_lt_iff n b).1 h
    obtain ⟨u, htu, hub⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htb
    have htu' : (t : ℝ) < u := by exact_mod_cast htu
    obtain ⟨q, htq, hqu⟩ := exists_rat_btwn htu'
    have hq0 : 0 ≤ (q : ℝ) := t.coe_nonneg.trans htq.le
    refine ⟨q, ?_, ht.trans (measure_mono (Iic_subset_Iic.2 ?_))⟩
    · exact ((ENNReal.ofReal_lt_coe_iff hq0).2 hqu).trans hub
    · exact (Real.le_toNNReal_iff_coe_le hq0).2 htq.le
  · exact (μ.occurrenceTime_lt_iff n b).2 ⟨Real.toNNReal (q : ℝ), hq, hm⟩

/-- Occurrence-time extraction is measurable, including on finite configurations and
without imposing local finiteness on the domain of the map. -/
@[fun_prop]
theorem measurable_occurrenceTime (n : ℕ) :
    Measurable fun μ : Measure ℝ≥0 => μ.occurrenceTime n := by
  apply measurable_of_Iio
  intro b
  have heq : {μ : Measure ℝ≥0 | μ.occurrenceTime n < b} =
      ⋃ q : ℚ, {μ : Measure ℝ≥0 | ENNReal.ofReal (q : ℝ) < b ∧
        (n + 1 : ℝ≥0∞) ≤ μ (Iic (Real.toNNReal (q : ℝ)))} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iUnion, occurrenceTime_lt_iff_rat]
  simp only [Iio, preimage_ofPred_eq, heq]
  exact MeasurableSet.iUnion fun q =>
    MeasurableSet.inter (MeasurableSet.const _)
      (measurableSet_le measurable_const (measurable_coe measurableSet_Iic))

/-- A location with multiplicity `k` occurs exactly `k` times, all at the same time. -/
@[simp]
theorem occurrenceTime_nsmul_dirac (k : ℕ) (t : ℝ≥0) (n : ℕ) :
    (k • dirac t).occurrenceTime n =
      if n < k then (t : ℝ≥0∞) else ∞ := by
  apply ENNReal.eq_of_forall_le_nnreal_iff
  intro s
  rw [occurrenceTime_le_iff]
  by_cases hnk : n < k
  · have hnk' : (n + 1 : ℝ≥0∞) ≤ k := by exact_mod_cast hnk
    by_cases hts : t ≤ s <;> simp [hnk, hts, hnk']
  · have hnk' : (k : ℝ≥0∞) < n + 1 := by
      exact_mod_cast Nat.lt_succ_of_le (le_of_not_gt hnk)
    by_cases hts : t ≤ s <;> simp [hnk, hts, hnk'.not_ge]

/-- The single-atom counting measure has exactly one finite occurrence. -/
@[simp]
theorem occurrenceTime_dirac (t : ℝ≥0) (n : ℕ) :
    (dirac t).occurrenceTime n = if n = 0 then (t : ℝ≥0∞) else ∞ := by
  simpa using occurrenceTime_nsmul_dirac 1 t n

end MeasureTheory.Measure
