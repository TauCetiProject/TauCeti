/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Count

/-!
# Interarrival gaps of measures on the half-line

`Measure.occurrenceGap μ n` is the extended waiting time preceding occurrence `n` of a
measure `μ` on `ℝ≥0`: at index zero it is `μ.occurrenceTime 0`, and at `n + 1` it is
`μ.occurrenceTime (n + 1) - μ.occurrenceTime n` when occurrence `n` is finite and `∞`
otherwise. Assigning `∞` after a missing occurrence avoids the spurious zero difference
`∞ - ∞ = 0` in `ℝ≥0∞`.

With this convention, the partial sum of the first `n + 1` extended gaps equals
`μ.occurrenceTime n` for every measure `μ` and every index `n`, without local finiteness,
integrality, or nonexplosion hypotheses, and `μ.occurrenceGap n` is finite if and only if
`μ.occurrenceTime n` is finite. Every locally finite integer-valued measure is therefore
reconstructed from its extended gap sequence.

For locally finite counting measures, exceeding a threshold duration in gap `0` means `[0, s]`
is empty, and exceeding a threshold duration in gap `n + 1` after a simple finite occurrence `n`
means the window of length `s` after that occurrence is empty, even when occurrence `n + 1` is
infinite.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 7.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-- The extended interarrival gap preceding occurrence `n` of a measure on `ℝ≥0`. Index zero
is the waiting time `μ.occurrenceTime 0` from the origin; index `n + 1` is the elapsed time
since occurrence `n`, or `∞` if occurrence `n` never happens. -/
noncomputable def occurrenceGap (μ : Measure ℝ≥0) : ℕ → ℝ≥0∞
  | 0 => μ.occurrenceTime 0
  | n + 1 =>
    if μ.occurrenceTime n = ∞ then ∞ else μ.occurrenceTime (n + 1) - μ.occurrenceTime n

/-- The initial gap is the time of the first occurrence, without inserting an atom at zero. -/
@[simp]
theorem occurrenceGap_zero (μ : Measure ℝ≥0) :
    μ.occurrenceGap 0 = μ.occurrenceTime 0 := (rfl)

/-- Each subsequent gap is the difference of consecutive occurrence times when the earlier
occurrence is finite, and `∞` otherwise. -/
theorem occurrenceGap_succ (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceGap (n + 1) =
      if μ.occurrenceTime n = ∞ then ∞
      else μ.occurrenceTime (n + 1) - μ.occurrenceTime n := (rfl)

/-- After a finite occurrence, the next extended gap is the difference of the two occurrence
times, including when the next occurrence is infinite. -/
theorem occurrenceGap_succ_of_ne_top {μ : Measure ℝ≥0} {n : ℕ} (h : μ.occurrenceTime n ≠ ∞) :
    μ.occurrenceGap (n + 1) = μ.occurrenceTime (n + 1) - μ.occurrenceTime n := by
  simp [occurrenceGap_succ, h]

/-- Between two finite consecutive occurrences, the finite `ℝ≥0` representative of the gap is
the difference of their finite occurrence times. -/
theorem toNNReal_occurrenceGap_succ {μ : Measure ℝ≥0} {n : ℕ}
    (hn : μ.occurrenceTime n ≠ ∞) :
    (μ.occurrenceGap (n + 1)).toNNReal =
      (μ.occurrenceTime (n + 1)).toNNReal - (μ.occurrenceTime n).toNNReal := by
  rw [occurrenceGap_succ_of_ne_top hn, ENNReal.toNNReal_sub hn]

/-- Between two finite consecutive occurrences, the real representative of the gap is the
difference of their real occurrence times. -/
theorem toReal_occurrenceGap_succ {μ : Measure ℝ≥0} {n : ℕ}
    (hn : μ.occurrenceTime n ≠ ∞) (hnext : μ.occurrenceTime (n + 1) ≠ ∞) :
    (μ.occurrenceGap (n + 1)).toReal =
      (μ.occurrenceTime (n + 1)).toReal - (μ.occurrenceTime n).toReal := by
  rw [occurrenceGap_succ_of_ne_top hn,
    ENNReal.toReal_sub_of_le (μ.monotone_occurrenceTime (Nat.le_succ n)) hnext]

/-- Extracting an extended interarrival gap is measurable on the space of measures, without
local finiteness or integrality assumptions. -/
@[fun_prop]
theorem measurable_occurrenceGap (n : ℕ) :
    Measurable fun μ : Measure ℝ≥0 => μ.occurrenceGap n := by
  cases n with
  | zero => exact measurable_occurrenceTime 0
  | succ n =>
    simp only [occurrenceGap_succ]
    exact Measurable.ite (measurableSet_eq_fun (measurable_occurrenceTime n) measurable_const)
      measurable_const
      ((measurable_occurrenceTime (n + 1)).sub (measurable_occurrenceTime n))

/-- An extended gap is infinite if and only if the corresponding occurrence never happens. -/
@[simp]
theorem occurrenceGap_eq_top_iff (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceGap n = ∞ ↔ μ.occurrenceTime n = ∞ := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [occurrenceGap_succ]
    by_cases hn : μ.occurrenceTime n = ∞
    · have hnext : μ.occurrenceTime (n + 1) = ∞ :=
        top_unique (hn ▸ μ.monotone_occurrenceTime (Nat.le_succ n))
      simp [hn, hnext]
    · simp [hn, ENNReal.sub_eq_top_iff]

/-- An extended gap is finite if and only if the corresponding occurrence time is finite. -/
theorem occurrenceGap_ne_top_iff (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceGap n ≠ ∞ ↔ μ.occurrenceTime n ≠ ∞ :=
  (μ.occurrenceGap_eq_top_iff n).not

/-- Strict finiteness of an extended gap is equivalent to strict finiteness of the
corresponding occurrence time. -/
theorem occurrenceGap_lt_top_iff (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceGap n < ∞ ↔ μ.occurrenceTime n < ∞ := by
  simp only [lt_top_iff_ne_top, occurrenceGap_ne_top_iff]

/-- Summing the first `n + 1` extended gaps recovers occurrence time `n` for every measure,
including finite configurations, multiple points, and non-locally-finite measures. -/
@[simp]
theorem sum_occurrenceGap_range (μ : Measure ℝ≥0) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), μ.occurrenceGap i = μ.occurrenceTime n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, occurrenceGap_succ]
    by_cases hn : μ.occurrenceTime n = ∞
    · have hnext : μ.occurrenceTime (n + 1) = ∞ :=
        top_unique (hn ▸ μ.monotone_occurrenceTime (Nat.le_succ n))
      simp [hn, hnext]
    · simp only [hn, ↓reduceIte]
      exact add_tsub_cancel_of_le (μ.monotone_occurrenceTime (Nat.le_succ n))

/-- When occurrence `n` is finite, summing the finite `ℝ≥0` gap representatives recovers its
finite occurrence time. -/
theorem sum_toNNReal_occurrenceGap_range {μ : Measure ℝ≥0} {n : ℕ}
    (h : μ.occurrenceTime n ≠ ∞) :
    ∑ i ∈ Finset.range (n + 1), (μ.occurrenceGap i).toNNReal =
      (μ.occurrenceTime n).toNNReal := by
  rw [← ENNReal.toNNReal_sum fun i hi => ?_, μ.sum_occurrenceGap_range n]
  rw [μ.occurrenceGap_ne_top_iff]
  exact ne_top_of_le_ne_top h
    (μ.monotone_occurrenceTime (Nat.le_of_lt_succ (Finset.mem_range.1 hi)))

/-- Every interarrival gap of the zero measure is infinite. -/
@[simp]
theorem occurrenceGap_zero_measure (n : ℕ) :
    (0 : Measure ℝ≥0).occurrenceGap n = ∞ := by
  simp [occurrenceGap_eq_top_iff]

/-- A single location of multiplicity `k` has initial gap `t` when `k ≥ 1`, `k - 1` zero gaps
for its simultaneous repetitions, and infinite gaps thereafter. -/
@[simp]
theorem occurrenceGap_nsmul_dirac (k : ℕ) (t : ℝ≥0) (n : ℕ) :
    (k • dirac t).occurrenceGap n =
      if n < k then (if n = 0 then (t : ℝ≥0∞) else 0) else ∞ := by
  cases n with
  | zero => simp
  | succ n =>
    rw [occurrenceGap_succ, occurrenceTime_nsmul_dirac, occurrenceTime_nsmul_dirac]
    by_cases hnk : n + 1 < k
    · have hn : n < k := Nat.lt_of_succ_lt hnk
      simp [hnk, hn]
    · by_cases hn : n < k
      · simp [hnk, hn]
      · simp [hnk, hn]

/-- A single Dirac atom has initial gap equal to its location and infinite subsequent gaps. -/
@[simp]
theorem occurrenceGap_dirac (t : ℝ≥0) (n : ℕ) :
    (dirac t).occurrenceGap n = if n = 0 then (t : ℝ≥0∞) else ∞ := by
  cases n <;> simp [occurrenceGap_succ]

section Counting

variable {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]

/-- Every locally finite integer-valued measure is reconstructed from the partial sums of its
extended interarrival gaps, including when the total mass is finite. -/
theorem IsIntegerValued.eq_occurrenceTimeMeasure_sum_occurrenceGap (hμ : μ.IsIntegerValued) :
    μ = TauCeti.Probability.occurrenceTimeMeasure
      (fun n => ∑ i ∈ Finset.range (n + 1), μ.occurrenceGap i) := by
  simpa only [sum_occurrenceGap_range] using hμ.eq_occurrenceTimeMeasure

/-- For a locally finite counting measure, the initial gap exceeds `s` exactly when `[0, s]`
contains no occurrences. -/
theorem IsIntegerValued.lt_occurrenceGap_zero_iff (hμ : μ.IsIntegerValued) (s : ℝ≥0) :
    (s : ℝ≥0∞) < μ.occurrenceGap 0 ↔ μ (Iic s) = 0 := by
  rw [occurrenceGap_zero, ← not_le, μ.occurrenceTime_le_iff 0 s, Nat.cast_zero, zero_add, not_le]
  obtain ⟨k, hk⟩ := hμ.exists_eq_natCast measurableSet_Iic (measure_Iic_lt_top (μ := μ))
  rw [hk]
  norm_cast
  omega

/-- After a finite occurrence of multiplicity at most one, the next extended gap exceeds `s`
exactly when the closed-right window of duration `s` after that occurrence is empty. The next
occurrence may be infinite. -/
theorem IsIntegerValued.lt_occurrenceGap_succ_iff (hμ : μ.IsIntegerValued) {n : ℕ}
    (hn : μ.occurrenceTime n ≠ ∞) (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1) (s : ℝ≥0) :
    (s : ℝ≥0∞) < μ.occurrenceGap (n + 1) ↔
      μ (Ioc (μ.occurrenceTime n).toNNReal ((μ.occurrenceTime n).toNNReal + s)) = 0 := by
  by_cases hnext : μ.occurrenceTime (n + 1) = ∞
  · rw [hμ.apply_Ioc_toNNReal_occurrenceTime_eq_zero_iff hn hs (le_add_of_nonneg_right s.2),
      occurrenceGap_succ_of_ne_top hn, hnext, ENNReal.top_sub hn]
    simp
  · have hfin : μ.occurrenceGap (n + 1) ≠ ∞ := (μ.occurrenceGap_ne_top_iff (n + 1)).2 hnext
    rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_lt_coe, toNNReal_occurrenceGap_succ hn]
    exact hμ.lt_toNNReal_occurrenceTime_sub_iff hn hnext hs s

/-- For a simple locally finite counting measure with no atom at zero, every extended
interarrival gap is strictly positive, including infinite missing gaps. -/
theorem IsIntegerValued.occurrenceGap_pos (hμ : μ.IsIntegerValued)
    (h0 : μ {0} = 0) (hsimple : ∀ x, μ {x} ≤ 1) (n : ℕ) :
    0 < μ.occurrenceGap n := by
  cases n with
  | zero =>
    have hIic : μ (Iic (0 : ℝ≥0)) = 0 := by
      have heq : (Iic (0 : ℝ≥0)) = {0} := Iic_bot
      rwa [heq]
    exact_mod_cast (hμ.lt_occurrenceGap_zero_iff 0).2 hIic
  | succ n =>
    rw [occurrenceGap_succ]
    by_cases hn : μ.occurrenceTime n = ∞
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      exact tsub_pos_iff_lt.2 (hμ.occurrenceTime_lt_succ hn (hsimple _))

end Counting

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- Forming `occurrenceTimeMeasure` from cumulative sums of finite `ℝ≥0` increments and taking
`occurrenceGap` recovers the original increment sequence. -/
@[simp]
theorem occurrenceGap_occurrenceTimeMeasure_sum (s : ℕ → ℝ≥0) (n : ℕ) :
    (occurrenceTimeMeasure fun k =>
      ∑ i ∈ Finset.range (k + 1), (s i : ℝ≥0∞)).occurrenceGap n = (s n : ℝ≥0∞) := by
  let t : ℕ → ℝ≥0∞ := fun k => ∑ i ∈ Finset.range (k + 1), (s i : ℝ≥0∞)
  have hmono : Monotone t := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  have ht := congrFun (occurrenceTime_occurrenceTimeMeasure hmono)
  cases n with
  | zero =>
    simpa [t, Measure.occurrenceGap_zero] using ht 0
  | succ n =>
    have hfin : ∑ i ∈ Finset.range (n + 1), (s i : ℝ≥0∞) ≠ ∞ :=
      (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.coe_lt_top).ne
    have hne : (occurrenceTimeMeasure t).occurrenceTime n ≠ ∞ := (ht n).symm ▸ hfin
    rw [Measure.occurrenceGap_succ_of_ne_top hne, ht n, ht (n + 1)]
    dsimp only [t]
    rw [Finset.sum_range_succ (n := n + 1)]
    exact ENNReal.add_sub_cancel_left hfin

end TauCeti.Probability
