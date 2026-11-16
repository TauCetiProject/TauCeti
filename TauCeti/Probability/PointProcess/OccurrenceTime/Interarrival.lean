/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Reconstruction
import TauCeti.Probability.PointProcess.OccurrenceTime.Count

/-!
# Interarrival times on the half-line

`Measure.interarrival μ n` is the waiting time preceding occurrence `n` of a measure `μ` on
`ℝ≥0`, indexed from zero: index zero is the first occurrence time `μ.occurrenceTime 0`, and
index `n + 1` is `μ.occurrenceTime (n + 1) - μ.occurrenceTime n` when occurrence `n` is finite,
and infinity otherwise.

Using infinity rather than `∞ - ∞ = 0` when an earlier occurrence is absent preserves the
unconditional partial-sum identity `∑ i ∈ Finset.range (n + 1), μ.interarrival i =
μ.occurrenceTime n` and ensures that an interarrival is infinite precisely when the
corresponding occurrence time is infinite. Multiple occurrences at one location produce zero
gaps; an atom at zero gives a zero initial interarrival.

The map `μ ↦ μ.interarrival n` is measurable for the evaluation σ-algebra on measures, without
imposing local finiteness or integrality. For locally finite integer-valued measures, the
interarrival sequence reconstructs the measure and its law determines the law of the random
measure.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge
  University Press, 2018, Chapter 7, for occurrence and interarrival times on the half-line.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {μ ν : Measure ℝ≥0}

/-- The waiting time preceding occurrence `n` of a measure on the half-line, indexed from zero.
Index zero is `μ.occurrenceTime 0`; index `n + 1` is the gap
`μ.occurrenceTime (n + 1) - μ.occurrenceTime n` when `μ.occurrenceTime n` is finite, and
infinity otherwise. -/
noncomputable def interarrival (μ : Measure ℝ≥0) : ℕ → ℝ≥0∞
  | 0 => μ.occurrenceTime 0
  | n + 1 =>
    if μ.occurrenceTime n = ∞ then ∞
    else μ.occurrenceTime (n + 1) - μ.occurrenceTime n

/-- The initial interarrival is the first occurrence time. -/
@[simp]
theorem interarrival_zero (μ : Measure ℝ≥0) :
    μ.interarrival 0 = μ.occurrenceTime 0 := (rfl)

/-- Each subsequent interarrival is the gap between consecutive occurrences, or infinity when
the preceding occurrence is absent. -/
theorem interarrival_succ (μ : Measure ℝ≥0) (n : ℕ) :
    μ.interarrival (n + 1) =
      if μ.occurrenceTime n = ∞ then ∞
      else μ.occurrenceTime (n + 1) - μ.occurrenceTime n := (rfl)

/-- After a finite occurrence, the next interarrival is the difference of occurrence times. -/
theorem interarrival_succ_of_ne_top {n : ℕ} (hn : μ.occurrenceTime n ≠ ∞) :
    μ.interarrival (n + 1) = μ.occurrenceTime (n + 1) - μ.occurrenceTime n := by
  simp [interarrival_succ, hn]

/-- Once an occurrence time is infinite, every later interarrival is infinite. -/
theorem interarrival_succ_of_eq_top {n : ℕ} (hn : μ.occurrenceTime n = ∞) :
    μ.interarrival (n + 1) = ∞ := by
  simp [interarrival_succ, hn]

/-- Summing the first `n + 1` interarrivals recovers occurrence time `n`, unconditionally for
every measure on the half-line, including finite configurations and explosive measures. -/
@[simp]
theorem sum_range_succ_interarrival (μ : Measure ℝ≥0) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), μ.interarrival i = μ.occurrenceTime n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, interarrival_succ]
    by_cases hn : μ.occurrenceTime n = ∞
    · have hnext : μ.occurrenceTime (n + 1) = ∞ :=
        top_unique (hn ▸ μ.monotone_occurrenceTime (Nat.le_succ n))
      simp [hn, hnext]
    · simp [hn, add_tsub_cancel_of_le (μ.monotone_occurrenceTime (Nat.le_succ n))]

/-- Every interarrival is bounded above by its corresponding occurrence time. -/
theorem interarrival_le_occurrenceTime (μ : Measure ℝ≥0) (n : ℕ) :
    μ.interarrival n ≤ μ.occurrenceTime n := by
  rw [← sum_range_succ_interarrival]
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.self_mem_range_succ n)

/-- An interarrival is infinite if and only if the corresponding occurrence time is infinite. -/
theorem interarrival_eq_top_iff (μ : Measure ℝ≥0) (n : ℕ) :
    μ.interarrival n = ∞ ↔ μ.occurrenceTime n = ∞ := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [interarrival_succ]
    by_cases hn : μ.occurrenceTime n = ∞
    · have hnext : μ.occurrenceTime (n + 1) = ∞ :=
        top_unique (hn ▸ μ.monotone_occurrenceTime (Nat.le_succ n))
      simp [hn, hnext]
    · simp [hn]

/-- An interarrival is finite if and only if the corresponding occurrence time is finite. -/
theorem interarrival_lt_top_iff (μ : Measure ℝ≥0) (n : ℕ) :
    μ.interarrival n < ∞ ↔ μ.occurrenceTime n < ∞ := by
  simp only [lt_top_iff_ne_top, ne_eq, interarrival_eq_top_iff]

/-- For consecutive finite occurrences, the nonnegative-real interarrival is the difference of
the nonnegative-real occurrence times. -/
theorem toNNReal_interarrival_succ {n : ℕ} (h : μ.occurrenceTime (n + 1) ≠ ∞) :
    (μ.interarrival (n + 1)).toNNReal =
      (μ.occurrenceTime (n + 1)).toNNReal - (μ.occurrenceTime n).toNNReal := by
  have hn : μ.occurrenceTime n ≠ ∞ :=
    ne_top_of_le_ne_top h (μ.monotone_occurrenceTime (Nat.le_succ n))
  rw [interarrival_succ_of_ne_top hn, ENNReal.toNNReal_sub hn]

/-- For consecutive finite occurrences, the real-valued interarrival is the difference of the
real-valued occurrence times. -/
theorem toReal_interarrival_succ {n : ℕ} (h : μ.occurrenceTime (n + 1) ≠ ∞) :
    (μ.interarrival (n + 1)).toReal =
      (μ.occurrenceTime (n + 1)).toReal - (μ.occurrenceTime n).toReal := by
  have hn : μ.occurrenceTime n ≠ ∞ :=
    ne_top_of_le_ne_top h (μ.monotone_occurrenceTime (Nat.le_succ n))
  rw [interarrival_succ_of_ne_top hn,
    ENNReal.toReal_sub_of_le (μ.monotone_occurrenceTime (Nat.le_succ n)) h]

/-- Summing the first `n + 1` nonnegative-real interarrivals recovers the nonnegative-real
occurrence time whenever that occurrence is finite. -/
theorem sum_range_succ_toNNReal_interarrival {n : ℕ} (h : μ.occurrenceTime n ≠ ∞) :
    ∑ i ∈ Finset.range (n + 1), (μ.interarrival i).toNNReal = (μ.occurrenceTime n).toNNReal := by
  have hfin : ∀ i ∈ Finset.range (n + 1), μ.interarrival i ≠ ∞ := fun i hi => by
    rw [ne_eq, interarrival_eq_top_iff]
    exact ne_top_of_le_ne_top h
      (μ.monotone_occurrenceTime (Nat.le_of_lt_succ (Finset.mem_range.1 hi)))
  rw [← ENNReal.toNNReal_sum hfin, sum_range_succ_interarrival]

/-- Summing the first `n + 1` real-valued interarrivals recovers the real-valued occurrence time
whenever that occurrence is finite. -/
theorem sum_range_succ_toReal_interarrival {n : ℕ} (h : μ.occurrenceTime n ≠ ∞) :
    ∑ i ∈ Finset.range (n + 1), (μ.interarrival i).toReal = (μ.occurrenceTime n).toReal := by
  have hfin : ∀ i ∈ Finset.range (n + 1), μ.interarrival i ≠ ∞ := fun i hi => by
    rw [ne_eq, interarrival_eq_top_iff]
    exact ne_top_of_le_ne_top h
      (μ.monotone_occurrenceTime (Nat.le_of_lt_succ (Finset.mem_range.1 hi)))
  rw [← ENNReal.toReal_sum hfin, sum_range_succ_interarrival]

/-- The zero measure has infinite interarrivals at every index. -/
@[simp]
theorem interarrival_zero_measure (n : ℕ) : (0 : Measure ℝ≥0).interarrival n = ∞ := by
  rw [interarrival_eq_top_iff, occurrenceTime_zero_measure]

/-- A single location with multiplicity `k` has initial interarrival `t`, `k - 1` zero gaps for
the coincident occurrences, and infinite interarrivals thereafter. -/
@[simp]
theorem interarrival_nsmul_dirac (k : ℕ) (t : ℝ≥0) (n : ℕ) :
    (k • dirac t).interarrival n =
      if n < k then (if n = 0 then (t : ℝ≥0∞) else 0) else ∞ := by
  cases n with
  | zero => simp
  | succ n =>
    rw [interarrival_succ]
    by_cases hnk : n + 1 < k
    · have hn : n < k := Nat.lt_of_succ_lt hnk
      simp [hnk, hn]
    · by_cases hn : n < k <;> simp [hnk, hn]

/-- A single Dirac occurrence has initial interarrival `t` and infinite later interarrivals. -/
@[simp]
theorem interarrival_dirac (t : ℝ≥0) (n : ℕ) :
    (dirac t).interarrival n = if n = 0 then (t : ℝ≥0∞) else ∞ := by
  cases n with
  | zero => simp
  | succ n => simpa using interarrival_nsmul_dirac 1 t (n + 1)

/-- Restricting to a closed observation window retains the interarrivals of occurrences in that
window and makes all subsequent interarrivals infinite. -/
@[simp]
theorem interarrival_restrict_Iic (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ]
    (b : ℝ≥0) (n : ℕ) :
    (μ.restrict (Iic b)).interarrival n =
      if μ.occurrenceTime n ≤ b then μ.interarrival n else ∞ := by
  cases n with
  | zero => simp
  | succ n =>
    rw [interarrival_succ, occurrenceTime_restrict_Iic, occurrenceTime_restrict_Iic]
    by_cases hnext : μ.occurrenceTime (n + 1) ≤ b
    · have hn : μ.occurrenceTime n ≤ b :=
        (μ.monotone_occurrenceTime (Nat.le_succ n)).trans hnext
      have hnfin : μ.occurrenceTime n ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hn
      simp [hnext, hn, hnfin, interarrival_succ_of_ne_top hnfin]
    · by_cases hn : μ.occurrenceTime n ≤ b
      · have hnfin : μ.occurrenceTime n ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hn
        simp [hnext, hn, hnfin]
      · simp [hnext, hn]

/-- For a locally finite measure, the first interarrival is positive exactly when the origin
carries mass strictly less than one. -/
theorem interarrival_zero_pos_iff (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ] :
    0 < μ.interarrival 0 ↔ μ {0} < 1 := by
  have hIic : Iic (0 : ℝ≥0) = {0} := by ext x; simp
  rw [interarrival_zero, lt_iff_not_ge, ← ENNReal.coe_zero,
    μ.occurrenceTime_le_iff 0 0, hIic, Nat.cast_zero, zero_add, not_le]

/-- After a finite occurrence of multiplicity at most one, the next interarrival is strictly
positive (possibly infinite). -/
theorem IsIntegerValued.interarrival_succ_pos [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) {n : ℕ} (hn : μ.occurrenceTime n ≠ ∞)
    (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1) :
    0 < μ.interarrival (n + 1) := by
  rw [interarrival_succ_of_ne_top hn]
  exact tsub_pos_of_lt (hμ.occurrenceTime_lt_succ hn hs)

/-- Interarrival extraction is measurable for the evaluation σ-algebra on measures, without
local finiteness or integrality assumptions on the domain. -/
@[fun_prop]
theorem measurable_interarrival (n : ℕ) :
    Measurable fun μ : Measure ℝ≥0 => μ.interarrival n := by
  cases n with
  | zero => exact measurable_occurrenceTime 0
  | succ n =>
    simp only [interarrival_succ]
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_occurrenceTime n) measurable_const)
      measurable_const
      ((measurable_occurrenceTime (n + 1)).sub (measurable_occurrenceTime n))

/-- Every locally finite counting measure is reconstructed from the partial sums of its
interarrivals. Multiplicities are retained and infinite interarrivals contribute no mass. -/
theorem IsIntegerValued.eq_occurrenceTimeMeasure_sum_interarrival [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) :
    μ = TauCeti.Probability.occurrenceTimeMeasure
      (fun n => ∑ i ∈ Finset.range (n + 1), μ.interarrival i) := by
  simp_rw [sum_range_succ_interarrival]
  exact hμ.eq_occurrenceTimeMeasure

/-- On locally finite counting measures, equality of interarrival sequences is equivalent to
equality of measures. The integrality assumption is essential. -/
@[simp]
theorem IsIntegerValued.interarrival_inj [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] (hμ : μ.IsIntegerValued) (hν : ν.IsIntegerValued) :
    μ.interarrival = ν.interarrival ↔ μ = ν := by
  constructor
  · intro h
    rw [hμ.eq_occurrenceTimeMeasure_sum_interarrival,
      hν.eq_occurrenceTimeMeasure_sum_interarrival, h]
  · rintro rfl
    rfl

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- Reading interarrival `n` of the occurrence measure formed by partial sums of a sequence
recovers entry `n`, provided every strictly earlier entry is finite. Entry `n` itself may be
zero or infinite, and no nonaccumulation assumption is needed. -/
theorem interarrival_occurrenceTimeMeasure_sum {t : ℕ → ℝ≥0∞} {n : ℕ}
    (ht : ∀ i < n, t i ≠ ∞) :
    (occurrenceTimeMeasure fun k => ∑ i ∈ Finset.range (k + 1), t i).interarrival n = t n := by
  have hmono : Monotone fun k => ∑ i ∈ Finset.range (k + 1), t i :=
    fun a b hab => Finset.sum_le_sum_of_subset
      (Finset.range_mono (Nat.succ_le_succ hab))
  cases n with
  | zero =>
    rw [Measure.interarrival_zero, occurrenceTime_occurrenceTimeMeasure hmono]
    simp
  | succ n =>
    have hfin : ∑ i ∈ Finset.range (n + 1), t i ≠ ∞ :=
      ENNReal.sum_ne_top.mpr fun i hi => ht i (Finset.mem_range.1 hi)
    rw [Measure.interarrival_succ_of_ne_top (by
        rw [occurrenceTime_occurrenceTimeMeasure hmono]; exact hfin),
      occurrenceTime_occurrenceTimeMeasure hmono]
    dsimp only
    rw [Finset.sum_range_succ]
    exact ENNReal.add_sub_cancel_left hfin

end TauCeti.Probability

namespace ProbabilityTheory.IdentDistrib

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {N : Ω → Measure ℝ≥0} {N' : Ω' → Measure ℝ≥0}

/-- Equality in law of the whole interarrival sequence implies equality in law of locally
finite integer-valued temporal random measures, including finite configurations and
multiplicities. -/
theorem of_interarrival
    (h : IdentDistrib (fun ω => (N ω).interarrival) (fun ω => (N' ω).interarrival) P P')
    (hN : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) ∧ (N ω).IsIntegerValued)
    (hN' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (N' ω) ∧ (N' ω).IsIntegerValued) :
    IdentDistrib N N' P P' := by
  have hsum : Measurable fun (g : ℕ → ℝ≥0∞) (n : ℕ) => ∑ i ∈ Finset.range (n + 1), g i :=
    measurable_pi_iff.mpr fun n =>
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  apply of_occurrenceTime _ hN hN'
  simpa only [Function.comp_def, Measure.sum_range_succ_interarrival] using h.comp hsum

end ProbabilityTheory.IdentDistrib
