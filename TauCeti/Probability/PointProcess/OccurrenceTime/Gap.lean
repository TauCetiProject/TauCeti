/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Count

/-!
# Interarrival gaps of measures on the half-line

`Measure.occurrenceGap μ n` is the `n`-th interarrival gap extracted from the ordered
`Measure.occurrenceTime`s of `μ`, indexed from zero: gap `0` is the first occurrence time,
and gap `n + 1` is the difference `μ.occurrenceTime (n + 1) - μ.occurrenceTime n` whenever
occurrence `n` is finite, and `∞` once occurrences have terminated. Retaining `∞` after the
last finite occurrence avoids spurious zero gaps on finite configurations.

Unconditionally, partial sums of gaps telescope back to occurrence times, and gap extraction
is measurable for the evaluation σ-algebra on measures. Restricting to `[0, b]` retains exactly
the gaps of occurrences in `[0, b]` and sets later gaps to `∞`. For locally finite integer-valued
measures, the gap sequence determines the measure and its law; positivity of the first gap is
equivalent to having no mass at zero; positivity of all subsequent gaps is equivalent to
simplicity (`∀ t, μ {t} ≤ 1`); exceeding a threshold duration in gap `0` means `[0, s]` is empty;
and, when occurrence `n` is finite and its location is simple (`μ {T_n} ≤ 1`), survival of
gap `n + 1` past `s` is equivalent to emptiness of `(T_n, T_n + s]`, including when occurrence
`n + 1` is infinite.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2 and 7.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

/-- The `n`-th interarrival gap of a measure on the half-line, indexed from zero.
Gap `0` is the first occurrence time; gap `n + 1` is the elapsed time from occurrence `n` to
occurrence `n + 1`, or `∞` if occurrence `n` never happens. -/
noncomputable def occurrenceGap (μ : Measure ℝ≥0) : ℕ → ℝ≥0∞
  | 0 => μ.occurrenceTime 0
  | n + 1 =>
    if μ.occurrenceTime n = ∞ then ∞ else μ.occurrenceTime (n + 1) - μ.occurrenceTime n

/-- The initial gap is the first occurrence time. -/
@[simp]
theorem occurrenceGap_zero (μ : Measure ℝ≥0) :
    μ.occurrenceGap 0 = μ.occurrenceTime 0 := (rfl)

/-- Subsequent gaps are consecutive differences of occurrence times, remaining `∞` once
occurrences terminate. -/
theorem occurrenceGap_succ (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceGap (n + 1) =
      if μ.occurrenceTime n = ∞ then ∞ else μ.occurrenceTime (n + 1) - μ.occurrenceTime n :=
  (rfl)

/-- When occurrence `n` is finite, gap `n + 1` is the difference to the next occurrence. -/
theorem occurrenceGap_succ_of_ne_top {μ : Measure ℝ≥0} {n : ℕ} (hn : μ.occurrenceTime n ≠ ∞) :
    μ.occurrenceGap (n + 1) = μ.occurrenceTime (n + 1) - μ.occurrenceTime n := by
  simp [occurrenceGap_succ, hn]

/-- Once occurrence `n` is infinite, gap `n + 1` is also infinite. -/
theorem occurrenceGap_succ_of_eq_top {μ : Measure ℝ≥0} {n : ℕ} (hn : μ.occurrenceTime n = ∞) :
    μ.occurrenceGap (n + 1) = ∞ := by
  simp [occurrenceGap_succ, hn]

/-- The `ℝ≥0` representative `(μ.occurrenceGap (n + 1)).toNNReal` equals the truncated
difference of the `toNNReal` occurrence times, including when occurrence `n` or `n + 1` is `∞`
(where both sides vanish). -/
theorem toNNReal_occurrenceGap_succ (μ : Measure ℝ≥0) (n : ℕ) :
    (μ.occurrenceGap (n + 1)).toNNReal =
      (μ.occurrenceTime (n + 1)).toNNReal - (μ.occurrenceTime n).toNNReal := by
  by_cases hn : μ.occurrenceTime n = ∞
  · have hnext : μ.occurrenceTime (n + 1) = ∞ :=
      μ.occurrenceTime_eq_top_of_le (Nat.le_succ n) hn
    simp [occurrenceGap_succ_of_eq_top hn, hn, hnext]
  · rw [occurrenceGap_succ_of_ne_top hn, ENNReal.toNNReal_sub hn]

/-- When occurrence `n + 1` is finite, occurrence `n` is automatically finite and the real
representative of gap `n + 1` is the difference of the two real occurrence times. -/
theorem toReal_occurrenceGap_succ {μ : Measure ℝ≥0} {n : ℕ}
    (hnext : μ.occurrenceTime (n + 1) ≠ ∞) :
    (μ.occurrenceGap (n + 1)).toReal =
      (μ.occurrenceTime (n + 1)).toReal - (μ.occurrenceTime n).toReal := by
  have hn : μ.occurrenceTime n ≠ ∞ :=
    ne_top_of_le_ne_top hnext (μ.monotone_occurrenceTime (Nat.le_succ n))
  rw [occurrenceGap_succ_of_ne_top hn,
    ENNReal.toReal_sub_of_le (μ.monotone_occurrenceTime (Nat.le_succ n)) hnext]

/-- Gap `n` is infinite if and only if occurrence `n` never happens. -/
theorem occurrenceGap_eq_top_iff (μ : Measure ℝ≥0) (n : ℕ) :
    μ.occurrenceGap n = ∞ ↔ μ.occurrenceTime n = ∞ := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [occurrenceGap_succ]
    by_cases hn : μ.occurrenceTime n = ∞
    · have hnext : μ.occurrenceTime (n + 1) = ∞ :=
        μ.occurrenceTime_eq_top_of_le (Nat.le_succ n) hn
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

/-- When occurrence `n` is finite, gap `n + 1` is positive if and only if the next occurrence
(possibly infinite) is strictly later. -/
theorem occurrenceGap_succ_pos_iff {μ : Measure ℝ≥0} {n : ℕ} (hn : μ.occurrenceTime n ≠ ∞) :
    0 < μ.occurrenceGap (n + 1) ↔ μ.occurrenceTime n < μ.occurrenceTime (n + 1) := by
  rw [occurrenceGap_succ_of_ne_top hn, tsub_pos_iff_lt]

/-- The zero measure has all interarrival gaps infinite. -/
@[simp]
theorem occurrenceGap_zero_measure (n : ℕ) : (0 : Measure ℝ≥0).occurrenceGap n = ∞ :=
  (occurrenceGap_eq_top_iff 0 n).2 (occurrenceTime_zero_measure n)

/-- A location with multiplicity `k` has initial gap `t`, followed by `k - 1` zero gaps and
then infinite gaps. -/
@[simp]
theorem occurrenceGap_nsmul_dirac (k : ℕ) (t : ℝ≥0) (n : ℕ) :
    (k • dirac t).occurrenceGap n =
      if n < k then (if n = 0 then (t : ℝ≥0∞) else 0) else ∞ := by
  cases n with
  | zero => simp
  | succ n =>
    rw [occurrenceGap_succ]
    by_cases hnk : n + 1 < k
    · have hn : n < k := Nat.lt_of_succ_lt hnk
      simp [hnk, hn]
    · by_cases hn : n < k
      · simp [hnk, hn]
      · simp [hnk, hn]

/-- A single atom at `t` has initial gap `t` and all subsequent gaps infinite. -/
@[simp]
theorem occurrenceGap_dirac (t : ℝ≥0) (n : ℕ) :
    (dirac t).occurrenceGap n = if n = 0 then (t : ℝ≥0∞) else ∞ := by
  cases n with
  | zero => simp
  | succ n =>
    by_cases hn : n = 0 <;> simp [occurrenceGap_succ, hn]

/-- Partial sums of interarrival gaps recover occurrence times unconditionally, including on
finite configurations and noninteger measures. -/
@[simp]
theorem sum_range_succ_occurrenceGap (μ : Measure ℝ≥0) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), μ.occurrenceGap i = μ.occurrenceTime n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, occurrenceGap_succ]
    by_cases hn : μ.occurrenceTime n = ∞
    · have hnext : μ.occurrenceTime (n + 1) = ∞ :=
        μ.occurrenceTime_eq_top_of_le (Nat.le_succ n) hn
      simp [hn, hnext]
    · rw [ite_eq_right hn, add_tsub_cancel_of_le (μ.monotone_occurrenceTime (Nat.le_succ n))]

/-- When occurrence `n` is finite, summing the finite `ℝ≥0` gap representatives recovers its
finite occurrence time. -/
theorem sum_range_toNNReal_occurrenceGap {μ : Measure ℝ≥0} {n : ℕ}
    (h : μ.occurrenceTime n ≠ ∞) :
    ∑ i ∈ Finset.range (n + 1), (μ.occurrenceGap i).toNNReal =
      (μ.occurrenceTime n).toNNReal := by
  rw [← ENNReal.toNNReal_sum fun i hi => ?_, μ.sum_range_succ_occurrenceGap n]
  rw [μ.occurrenceGap_ne_top_iff]
  exact ne_top_of_le_ne_top h
    (μ.monotone_occurrenceTime (Nat.le_of_lt_succ (Finset.mem_range.1 hi)))

/-- When occurrence `n` is finite, casting the sum of the `ℝ≥0`-valued interarrival gaps up to
index `n` recovers occurrence time `n`. -/
theorem coe_sum_range_succ_toNNReal_occurrenceGap {μ : Measure ℝ≥0} {n : ℕ}
    (hn : μ.occurrenceTime n ≠ ∞) :
    ((∑ i ∈ Finset.range (n + 1), (μ.occurrenceGap i).toNNReal : ℝ≥0) : ℝ≥0∞) =
      μ.occurrenceTime n := by
  rw [μ.sum_range_toNNReal_occurrenceGap hn, ENNReal.coe_toNNReal hn]

/-- Interarrival gaps and occurrence times carry the same information for every measure on the
half-line. -/
theorem occurrenceGap_eq_iff_occurrenceTime_eq (μ ν : Measure ℝ≥0) :
    μ.occurrenceGap = ν.occurrenceGap ↔ μ.occurrenceTime = ν.occurrenceTime := by
  constructor
  · intro h
    funext n
    rw [← sum_range_succ_occurrenceGap, ← sum_range_succ_occurrenceGap, h]
  · intro h
    funext n
    cases n with
    | zero => simp [h]
    | succ n => simp [occurrenceGap_succ, h]

/-- Interarrival-gap extraction is measurable for the evaluation σ-algebra on measures,
without assuming local finiteness or integrality. -/
@[fun_prop]
theorem measurable_occurrenceGap (n : ℕ) :
    Measurable fun μ : Measure ℝ≥0 => μ.occurrenceGap n := by
  cases n with
  | zero => exact measurable_occurrenceTime 0
  | succ n =>
    simp only [occurrenceGap_succ]
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_occurrenceTime n) measurable_const)
      measurable_const
      ((measurable_occurrenceTime (n + 1)).sub (measurable_occurrenceTime n))

/-- Restricting to a closed observation window retains exactly the interarrival gaps whose
cumulative mass threshold is already met on `[0, b]`, setting all subsequent gaps to `∞`.
No finiteness assumption is required, including when `μ (Iic b) = ∞` or `μ` explodes immediately
after `b`. -/
theorem occurrenceGap_restrict_Iic_eq_ite (μ : Measure ℝ≥0) (b : ℝ≥0) (n : ℕ) :
    (μ.restrict (Iic b)).occurrenceGap n =
      if (n + 1 : ℝ≥0∞) ≤ μ (Iic b) then μ.occurrenceGap n else ∞ := by
  by_cases h : (n + 1 : ℝ≥0∞) ≤ μ (Iic b)
  · rw [ite_eq_left h]
    cases n with
    | zero =>
      rw [occurrenceGap_zero, occurrenceGap_zero, occurrenceTime_restrict_Iic_eq_ite, ite_eq_left h]
    | succ n =>
      have hn : (n + 1 : ℝ≥0∞) ≤ μ (Iic b) := le_trans (by simp) h
      have ht_res : (μ.restrict (Iic b)).occurrenceTime n = μ.occurrenceTime n := by
        rw [occurrenceTime_restrict_Iic_eq_ite, ite_eq_left hn]
      have htsucc_res :
          (μ.restrict (Iic b)).occurrenceTime (n + 1) = μ.occurrenceTime (n + 1) := by
        rw [occurrenceTime_restrict_Iic_eq_ite, ite_eq_left h]
      have ht_ne : μ.occurrenceTime n ≠ ∞ :=
        ne_top_of_le_ne_top ENNReal.coe_ne_top (μ.occurrenceTime_le_of_le hn)
      rw [occurrenceGap_succ, occurrenceGap_succ, ht_res, htsucc_res, ite_eq_right ht_ne]
  · rw [ite_eq_right h, occurrenceGap_eq_top_iff, occurrenceTime_restrict_Iic_eq_ite,
      ite_eq_right h]

/-- Restricting to a closed observation window retains exactly the interarrival gaps of
occurrences in `[0, b]`, setting all subsequent gaps to `∞`, whenever the measure is finite on
some larger closed window. No global local finiteness is required. -/
theorem occurrenceGap_restrict_Iic_of_measure_Iic_ne_top (μ : Measure ℝ≥0)
    (b : ℝ≥0) (n : ℕ) (hfin : ∃ s > b, μ (Iic s) ≠ ∞) :
    (μ.restrict (Iic b)).occurrenceGap n =
      if μ.occurrenceTime n ≤ b then μ.occurrenceGap n else ∞ := by
  simp only [occurrenceGap_restrict_Iic_eq_ite,
    occurrenceTime_le_iff_of_measure_Iic_ne_top μ n b hfin]

/-- Restricting to a closed observation window retains exactly the interarrival gaps of
occurrences in `[0, b]`; all subsequent gaps become infinite. -/
@[simp]
theorem occurrenceGap_restrict_Iic (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ]
    (b : ℝ≥0) (n : ℕ) :
    (μ.restrict (Iic b)).occurrenceGap n =
      if μ.occurrenceTime n ≤ b then μ.occurrenceGap n else ∞ :=
  occurrenceGap_restrict_Iic_of_measure_Iic_ne_top μ b n
    ⟨b + 1, lt_add_one b, (measure_Iic_lt_top (μ := μ)).ne⟩

section LocallyFinite

open TauCeti.Probability

variable {μ ν : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]

/-- A locally finite integer-valued measure is reconstructed from the partial sums of its
interarrival gaps. -/
theorem IsIntegerValued.eq_occurrenceTimeMeasure_sum_occurrenceGap (hμ : μ.IsIntegerValued) :
    μ = occurrenceTimeMeasure (fun n => ∑ i ∈ Finset.range (n + 1), μ.occurrenceGap i) := by
  simpa only [sum_range_succ_occurrenceGap] using hμ.eq_occurrenceTimeMeasure

/-- On locally finite counting measures, equality of interarrival gap sequences is equivalent
to equality of measures. -/
@[simp]
theorem IsIntegerValued.occurrenceGap_inj [IsLocallyFiniteMeasure ν]
    (hμ : μ.IsIntegerValued) (hν : ν.IsIntegerValued) :
    μ.occurrenceGap = ν.occurrenceGap ↔ μ = ν := by
  rw [occurrenceGap_eq_iff_occurrenceTime_eq, hμ.occurrenceTime_inj hν]

/-- For a locally finite counting measure, the initial gap exceeds `s` exactly when `[0, s]`
contains no occurrences. -/
theorem IsIntegerValued.lt_occurrenceGap_zero_iff (hμ : μ.IsIntegerValued) (s : ℝ≥0) :
    (s : ℝ≥0∞) < μ.occurrenceGap 0 ↔ μ (Iic s) = 0 := by
  rw [occurrenceGap_zero, ← not_le, μ.occurrenceTime_le_iff 0 s, Nat.cast_zero, zero_add]
  exact ⟨fun h => by_contra fun hne => h (hμ.one_le_apply hne), fun h => by simp [h]⟩

/-- For a locally finite counting measure, the first gap is positive if and only if there is
no occurrence at zero. Empty configurations satisfy both sides. -/
theorem IsIntegerValued.occurrenceGap_zero_pos_iff (hμ : μ.IsIntegerValued) :
    0 < μ.occurrenceGap 0 ↔ μ {0} = 0 := by
  have hIic : Iic (0 : ℝ≥0) = {0} := by rw [← bot_eq_zero, Iic_bot]
  simpa only [ENNReal.coe_zero, hIic] using hμ.lt_occurrenceGap_zero_iff 0

/-- For a locally finite counting measure, simplicity (every singleton has mass at most one)
is equivalent to positivity of every interarrival gap after the first. Finite configurations
and an atom of mass one at zero are included. -/
theorem IsIntegerValued.forall_singleton_le_one_iff_forall_occurrenceGap_succ_pos
    (hμ : μ.IsIntegerValued) :
    (∀ t : ℝ≥0, μ {t} ≤ 1) ↔ ∀ n : ℕ, 0 < μ.occurrenceGap (n + 1) := by
  classical
  constructor
  · intro hsimp n
    by_cases hn : μ.occurrenceTime n = ∞
    · simp [occurrenceGap_succ_of_eq_top hn]
    · exact (occurrenceGap_succ_pos_iff hn).2 (hμ.occurrenceTime_lt_succ hn (hsimp _))
  · intro hpos t
    let P : ℕ → Prop := fun n => μ.occurrenceTime n ≠ ∞ ∧ (μ.occurrenceTime n).toNNReal = t
    have hlt : ∀ {m n}, m < n → P m → P n → False := fun hmn hm hn =>
      (((occurrenceGap_succ_pos_iff hm.1).1 (hpos _)).trans_le
        (μ.monotone_occurrenceTime (Nat.succ_le_of_lt hmn))).ne
        (by rw [← ENNReal.coe_toNNReal hm.1, ← ENNReal.coe_toNNReal hn.1, hm.2, hn.2])
    have hsub : ∀ {m n}, P m → P n → m = n := fun hm hn =>
      ((lt_trichotomy _ _).resolve_left fun h => hlt h hm hn).resolve_right
        fun h => hlt h hn hm
    rw [congrArg (fun ρ : Measure ℝ≥0 => ρ {t}) hμ.eq_occurrenceTimeMeasure,
      occurrenceTimeMeasure_apply]
    simp only [mem_singleton_iff]
    by_cases hex : ∃ n, P n
    · obtain ⟨n, hn⟩ := hex
      rw [tsum_eq_single n (fun k hk => ite_eq_right fun hPk => hk (hsub hPk hn))]
      simp [P, hn]
    · push Not at hex
      simp [P, hex]

/-- After a simple finite occurrence `n`, gap `n + 1` exceeds `s` exactly when the window
`(T_n, T_n + s]` is empty. This includes the case where occurrence `n + 1` is infinite. -/
theorem IsIntegerValued.lt_occurrenceGap_succ_iff (hμ : μ.IsIntegerValued) {n : ℕ}
    (hn : μ.occurrenceTime n ≠ ∞) (hs : μ {(μ.occurrenceTime n).toNNReal} ≤ 1) (s : ℝ≥0) :
    (s : ℝ≥0∞) < μ.occurrenceGap (n + 1) ↔
      μ (Ioc (μ.occurrenceTime n).toNNReal ((μ.occurrenceTime n).toNNReal + s)) = 0 := by
  rw [hμ.apply_Ioc_toNNReal_occurrenceTime_eq_zero_iff hn hs (le_add_of_nonneg_right s.property),
    occurrenceGap_succ_of_ne_top hn]
  cases hnext : μ.occurrenceTime (n + 1) using ENNReal.recTopCoe with
  | top => simp [hn, lt_top_iff_ne_top.mpr hn]
  | coe u =>
    rw [← ENNReal.coe_toNNReal hn, ← ENNReal.coe_sub, ENNReal.coe_lt_coe, ENNReal.coe_lt_coe]
    exact lt_tsub_iff_left

/-- For a simple locally finite counting measure with no atom at zero, every extended
interarrival gap is strictly positive, including infinite missing gaps. -/
theorem IsIntegerValued.occurrenceGap_pos (hμ : μ.IsIntegerValued)
    (h0 : μ {0} = 0) (hsimple : ∀ x, μ {x} ≤ 1) (n : ℕ) :
    0 < μ.occurrenceGap n := by
  cases n with
  | zero => exact hμ.occurrenceGap_zero_pos_iff.mpr h0
  | succ n => exact hμ.forall_singleton_le_one_iff_forall_occurrenceGap_succ_pos.mp hsimple n

end LocallyFinite

end MeasureTheory.Measure

namespace TauCeti.Probability

/-- Reading interarrival gaps from the measure placed at partial sums of `g` recovers `g`,
except that every gap after an infinite entry becomes `∞`. -/
theorem occurrenceGap_occurrenceTimeMeasure_sum (g : ℕ → ℝ≥0∞) (n : ℕ) :
    (occurrenceTimeMeasure (fun k => ∑ i ∈ Finset.range (k + 1), g i)).occurrenceGap n =
      if (∑ i ∈ Finset.range n, g i) = ∞ then ∞ else g n := by
  have hmono : Monotone fun k => ∑ i ∈ Finset.range (k + 1), g i :=
    fun _ _ h => Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h))
  have htime (k : ℕ) :
      (occurrenceTimeMeasure (fun j => ∑ i ∈ Finset.range (j + 1), g i)).occurrenceTime k =
        ∑ i ∈ Finset.range (k + 1), g i :=
    congrFun (occurrenceTime_occurrenceTimeMeasure hmono) k
  cases n with
  | zero => simp [htime]
  | succ n =>
    rw [Measure.occurrenceGap_succ, htime, htime]
    by_cases hn : (∑ i ∈ Finset.range (n + 1), g i) = ∞
    · rw [ite_eq_left hn, ite_eq_left hn]
    · rw [ite_eq_right hn, ite_eq_right hn, Finset.sum_range_succ, ENNReal.add_sub_cancel_left hn]

end TauCeti.Probability

namespace ProbabilityTheory.IdentDistrib

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {N : Ω → Measure ℝ≥0} {N' : Ω' → Measure ℝ≥0}

/-- Equality in law of the full interarrival-gap sequence implies equality in law of the
temporal counting measures. Local finiteness and integrality are required only almost surely. -/
theorem of_occurrenceGap
    (h : IdentDistrib (fun ω => (N ω).occurrenceGap)
      (fun ω => (N' ω).occurrenceGap) P P')
    (hN : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) ∧ (N ω).IsIntegerValued)
    (hN' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (N' ω) ∧ (N' ω).IsIntegerValued) :
    IdentDistrib N N' P P' := by
  have hsum : Measurable (fun (g : ℕ → ℝ≥0∞) (n : ℕ) => ∑ i ∈ Finset.range (n + 1), g i) :=
    measurable_pi_iff.mpr fun n =>
      Finset.measurable_fun_sum _ fun i _ => measurable_pi_apply i
  have htime : IdentDistrib (fun ω => (N ω).occurrenceTime)
      (fun ω => (N' ω).occurrenceTime) P P' := by
    simpa only [Function.comp_def, Measure.sum_range_succ_occurrenceGap] using h.comp hsum
  exact of_occurrenceTime htime hN hN'

end ProbabilityTheory.IdentDistrib
