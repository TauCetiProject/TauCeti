/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.NNRat.Defs
public import TauCeti.MeasureTheory.Measure.IntegerValued.Stieltjes
public import TauCeti.Probability.PointProcess.OccurrenceTime.Reconstruction
public import TauCeti.Topology.Order.Cadlag
import Mathlib.Data.NNRat.Encodable
import TauCeti.MeasureTheory.Measure.Interval
import TauCeti.Topology.Instances.NNRat

/-!
# The counting measure of a counting path

A nondecreasing right-continuous natural-valued path `N : ℝ≥0 → ℕ` is the cumulative count of
exactly one measure on the half-line. `countingPathMeasure N` constructs it explicitly, with one
occurrence at each `pathOccurrenceTime N n`, the first time at which the path exceeds `n`.
Jumps larger than one give repeated occurrences, and the mass at zero is `N 0`.

Occurrence times are infima over rational times. For a nondecreasing path that is right-continuous
at `t`, `pathOccurrenceTime N n ≤ t ↔ n < N t`, and for an arbitrary path the construction depends
only on nonnegative rational times, so it is measurable as soon as the process is measurable at
nonnegative rational times (`measurable_countingPathMeasure_of_nnrat`). Monotonicity alone ensures
that `countingPathMeasure N` is locally finite
(`isLocallyFiniteMeasure_countingPathMeasure_of_monotone`).
Combined with cumulative-floor reconstruction, this allows natural-valued count processes to be
recognized as random measures, for instance as Poisson random measures.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2 and 7.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal NNRat

namespace TauCeti.Probability

/-- Occurrence `n`, indexed from zero, of a natural-valued path: the infimum of the rational
times `q` (read in `ℝ≥0` through `Real.toNNReal`) at which the path exceeds `n`, or `∞` if
there are none. For a nondecreasing path right-continuous at `t`, it occurs by `t` exactly when
`n < N t` (`pathOccurrenceTime_le_iff_of_continuousWithinAt`). -/
noncomputable def pathOccurrenceTime (N : ℝ≥0 → ℕ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (q : ℚ) (_ : n < N (Real.toNNReal q)), (Real.toNNReal q : ℝ≥0∞)

/-- Unfold a path occurrence time as an infimum over rational times. -/
theorem pathOccurrenceTime_def (N : ℝ≥0 → ℕ) (n : ℕ) :
    pathOccurrenceTime N n =
      ⨅ (q : ℚ) (_ : n < N (Real.toNNReal q)), (Real.toNNReal q : ℝ≥0∞) :=
  (rfl)

/-- Express `pathOccurrenceTime` as an infimum over nonnegative rational times `ℚ≥0`. -/
theorem pathOccurrenceTime_eq_iInf_nnrat (N : ℝ≥0 → ℕ) (n : ℕ) :
    pathOccurrenceTime N n = ⨅ (q : ℚ≥0) (_ : n < N q), ((q : ℝ≥0) : ℝ≥0∞) := by
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    intro q hq
    rw [pathOccurrenceTime_def]
    refine iInf_le_of_le (q : ℚ) (iInf_le_of_le ?_ ?_)
    · simpa only [Rat.cast_nnratCast, NNRat.toNNReal_cast] using hq
    · simp only [Rat.cast_nnratCast, NNRat.toNNReal_cast, le_rfl]
  · simp only [pathOccurrenceTime_def, le_iInf_iff]
    intro q hq
    refine iInf_le_of_le q.toNNRat (iInf_le_of_le ?_ ?_)
    · simpa only [← Rat.toNNReal_cast] using hq
    · simp only [← Rat.toNNReal_cast, le_rfl]

/-- Path occurrence times are nondecreasing in their index, for every path. -/
theorem monotone_pathOccurrenceTime (N : ℝ≥0 → ℕ) : Monotone (pathOccurrenceTime N) :=
  fun _ _ hnm ↦ iInf_mono fun _ ↦ iInf_mono' fun h ↦ ⟨hnm.trans_lt h, le_rfl⟩

/-- A jump time is strictly below a bound exactly when some earlier nonnegative rational time
already exceeds `n`. -/
theorem pathOccurrenceTime_lt_iff (f : ℝ≥0 → ℕ) (n : ℕ) (b : ℝ≥0∞) :
    pathOccurrenceTime f n < b ↔ ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < b ∧ n + 1 ≤ f q := by
  simp only [pathOccurrenceTime_eq_iInf_nnrat, iInf_lt_iff, Nat.succ_le_iff]
  exact ⟨fun ⟨q, hq, hb⟩ ↦ ⟨q, hb, hq⟩, fun ⟨q, hb, hq⟩ ↦ ⟨q, hq, hb⟩⟩

/-- Exceeding `n` at a nonnegative rational time bounds the `n`-th jump time. -/
theorem pathOccurrenceTime_le_nnrat {f : ℝ≥0 → ℕ} {n : ℕ} {q : ℚ≥0} (hq : n + 1 ≤ f q) :
    pathOccurrenceTime f n ≤ (q : ℝ≥0) := by
  rw [pathOccurrenceTime_eq_iInf_nnrat]
  exact iInf₂_le q (Nat.succ_le_iff.1 hq)

/-- Extracting the `n`-th jump time is measurable whenever the process is measurable at
nonnegative rational times. -/
theorem measurable_pathOccurrenceTime_of_nnrat {Ω : Type*} [MeasurableSpace Ω]
    {N : ℝ≥0 → Ω → ℕ} (hN : ∀ q : ℚ≥0, Measurable (N q)) (n : ℕ) :
    Measurable fun ω ↦ pathOccurrenceTime (N · ω) n := by
  simp only [pathOccurrenceTime_eq_iInf_nnrat, iInf_eq_if]
  exact Measurable.iInf fun q ↦
    measurable_const.ite (measurableSet_lt measurable_const (hN q)) measurable_const

/-- Extracting the jump-time sequence is measurable whenever the process is measurable at
nonnegative rational times. -/
theorem measurable_pathOccurrenceTime_pi_of_nnrat {Ω : Type*} [MeasurableSpace Ω]
    {N : ℝ≥0 → Ω → ℕ} (hN : ∀ q : ℚ≥0, Measurable (N q)) :
    Measurable fun ω ↦ pathOccurrenceTime (N · ω) :=
  measurable_pi_iff.2 (measurable_pathOccurrenceTime_of_nnrat hN)

/-- Each path occurrence time is measurable for the product sigma-algebra on all paths. -/
@[fun_prop]
theorem measurable_pathOccurrenceTime (n : ℕ) :
    Measurable fun N : ℝ≥0 → ℕ ↦ pathOccurrenceTime N n :=
  measurable_pathOccurrenceTime_of_nnrat (fun q ↦ measurable_pi_apply (q : ℝ≥0)) n

/-- If `f` stays at least `n + 1` throughout a nonempty open interval `(t, δ)`, then
`pathOccurrenceTime f n ≤ t`, without global monotonicity or right-continuity assumptions. -/
theorem pathOccurrenceTime_le_of_forall_Ioo {f : ℝ≥0 → ℕ} {t δ : ℝ≥0} (hδ : t < δ) {n : ℕ}
    (h : ∀ s ∈ Ioo t δ, n + 1 ≤ f s) : pathOccurrenceTime f n ≤ t := by
  refine le_of_forall_gt fun b hb ↦ ?_
  obtain ⟨q, htq, hqb⟩ := ENNReal.lt_iff_exists_nnrat_btwn.1 (lt_min hb (ENNReal.coe_lt_coe.2 hδ))
  exact (pathOccurrenceTime_le_nnrat (h q ⟨ENNReal.coe_lt_coe.1 htq,
    ENNReal.coe_lt_coe.1 (hqb.trans_le (min_le_right _ _))⟩)).trans_lt
    (hqb.trans_le (min_le_left _ _))

/-- On a monotone path, reaching `n + 1` at any real time `t` bounds `pathOccurrenceTime f n` by
`t`. -/
theorem pathOccurrenceTime_le_of_monotone_of_le {f : ℝ≥0 → ℕ} (hf : Monotone f) {n : ℕ} {t : ℝ≥0}
    (ht : n + 1 ≤ f t) : pathOccurrenceTime f n ≤ t :=
  pathOccurrenceTime_le_of_forall_Ioo (lt_add_one t) fun _ hs ↦ ht.trans (hf hs.1.le)

/-- For a monotone path that is right-continuous at `t`, the `n`-th jump occurs on `[0, t]` if and
only if `n < f t`. -/
theorem pathOccurrenceTime_le_iff_of_continuousWithinAt {f : ℝ≥0 → ℕ} (hf : Monotone f) {t : ℝ≥0}
    (hrc : ContinuousWithinAt f (Ioi t) t) (n : ℕ) :
    pathOccurrenceTime f n ≤ t ↔ n < f t := by
  refine ⟨fun h ↦ Nat.succ_le_iff.1 ?_, fun h ↦
    pathOccurrenceTime_le_of_monotone_of_le hf (Nat.succ_le_iff.2 h)⟩
  apply ge_of_tendsto hrc
  filter_upwards [self_mem_nhdsWithin] with s hs
  obtain ⟨q, hqs, hq⟩ := (pathOccurrenceTime_lt_iff f n s).1 (h.trans_lt (ENNReal.coe_lt_coe.2 hs))
  exact hq.trans (hf (ENNReal.coe_le_coe.1 hqs.le))

/-- Every monotone natural-valued path has jump times tending to `∞`: finiteness of `f` at each
time prevents finite-time explosion even without right-continuity. -/
theorem tendsto_pathOccurrenceTime_nhds_top {f : ℝ≥0 → ℕ} (hf : Monotone f) :
    Tendsto (pathOccurrenceTime f) atTop (𝓝 ∞) := by
  refine ENNReal.tendsto_nhds_top_iff_nnreal.2 fun x ↦ ?_
  let q : ℚ≥0 := ⌈x⌉₊ + 1
  have hxq : x < (q : ℝ≥0) := (Nat.le_ceil x).trans_lt (by simp [q])
  filter_upwards [eventually_ge_atTop (f q)] with n hn
  refine (ENNReal.coe_lt_coe.2 hxq).trans_le ?_
  simp only [pathOccurrenceTime_eq_iInf_nnrat, le_iInf_iff]
  intro r hr
  refine ENNReal.coe_le_coe.2 (le_of_not_gt fun hqr : (r : ℝ≥0) < q ↦ ?_)
  exact not_le_of_gt (Nat.lt_succ_of_le ((hf hqr.le).trans hn)) (Nat.succ_le_iff.2 hr)

/-- The counting measure of a natural-valued path, with one occurrence at each finite
`pathOccurrenceTime`. For a nondecreasing right-continuous path it is the unique measure whose
mass on `[0,t]` is the value of the path at `t` (`eq_countingPathMeasure_iff`). -/
noncomputable def countingPathMeasure (N : ℝ≥0 → ℕ) : Measure ℝ≥0 :=
  occurrenceTimeMeasure (pathOccurrenceTime N)

/-- Unfold the counting measure of a path as the measure of its occurrence times. -/
theorem countingPathMeasure_def (N : ℝ≥0 → ℕ) :
    countingPathMeasure N = occurrenceTimeMeasure (pathOccurrenceTime N) :=
  (rfl)

/-- Reconstructing the temporal measure from a counting process is measurable as soon as the
process is measurable at nonnegative rational times. No measurability of any regular-path event is
required. -/
theorem measurable_countingPathMeasure_of_nnrat {Ω : Type*} [MeasurableSpace Ω] {N : ℝ≥0 → Ω → ℕ}
    (hN : ∀ q : ℚ≥0, Measurable (N q)) :
    Measurable fun ω ↦ countingPathMeasure (N · ω) := by
  simp_rw [countingPathMeasure_def]
  exact measurable_occurrenceTimeMeasure.comp (measurable_pathOccurrenceTime_pi_of_nnrat hN)

/-- Forming the counting measure is measurable for the product sigma-algebra on all paths. -/
@[fun_prop]
theorem measurable_countingPathMeasure : Measurable countingPathMeasure :=
  measurable_countingPathMeasure_of_nnrat fun q ↦ measurable_pi_apply (q : ℝ≥0)

/-- The counting measure of every path is integer-valued. -/
@[simp]
theorem isIntegerValued_countingPathMeasure (N : ℝ≥0 → ℕ) :
    (countingPathMeasure N).IsIntegerValued :=
  isIntegerValued_occurrenceTimeMeasure _

/-- The ordered occurrence times of the counting measure of a path are its path occurrence
times, for every path. -/
@[simp]
theorem occurrenceTime_countingPathMeasure (N : ℝ≥0 → ℕ) :
    (countingPathMeasure N).occurrenceTime = pathOccurrenceTime N :=
  occurrenceTime_occurrenceTimeMeasure (monotone_pathOccurrenceTime N)

/-- For any monotone natural-valued path, `countingPathMeasure f` is locally finite without
assuming right continuity. -/
theorem isLocallyFiniteMeasure_countingPathMeasure_of_monotone {f : ℝ≥0 → ℕ} (hf : Monotone f) :
    IsLocallyFiniteMeasure (countingPathMeasure f) := by
  rw [countingPathMeasure_def]
  exact isLocallyFiniteMeasure_occurrenceTimeMeasure (tendsto_pathOccurrenceTime_nhds_top hf)

/-- For a monotone path that is right-continuous at `t`, the cumulative mass of
`countingPathMeasure f` on `[0, t]` equals `f t`. -/
@[simp]
theorem countingPathMeasure_Iic_of_continuousWithinAt {f : ℝ≥0 → ℕ} (hf : Monotone f) {t : ℝ≥0}
    (hrc : ContinuousWithinAt f (Ioi t) t) :
    countingPathMeasure f (Iic t) = f t := by
  classical
  rw [countingPathMeasure_def, occurrenceTimeMeasure_Iic]
  simp_rw [pathOccurrenceTime_le_iff_of_continuousWithinAt hf hrc]
  rw [tsum_eq_sum (s := Finset.range (f t)) (fun n hn ↦ by simp_all)]
  simp [← Finset.mem_range]

/-- The counting measure of a nondecreasing right-continuous path gives `(s,t]` the mass
`N t - N s`, which is zero when `t ≤ s`. -/
@[simp]
theorem countingPathMeasure_Ioc {N : ℝ≥0 → ℕ} (hmono : Monotone N) (hrc : IsRightContinuous N)
    (s t : ℝ≥0) : countingPathMeasure N (Ioc s t) = (N t - N s : ℕ) :=
  Measure.measure_Ioc_eq_natCast_sub
    (countingPathMeasure_Iic_of_continuousWithinAt hmono (hrc s))
    (countingPathMeasure_Iic_of_continuousWithinAt hmono (hrc t))

/-- **Characterization of the counting measure of a path.** For a nondecreasing
right-continuous path, a measure is its counting measure exactly when its mass on each `[0,t]`
is the value of the path at `t`. No finiteness or integrality is assumed of the measure. -/
theorem eq_countingPathMeasure_iff {N : ℝ≥0 → ℕ} (hmono : Monotone N)
    (hrc : IsRightContinuous N) {μ : Measure ℝ≥0} :
    μ = countingPathMeasure N ↔ ∀ t, μ (Iic t) = N t := by
  refine ⟨fun h t ↦ h ▸ countingPathMeasure_Iic_of_continuousWithinAt hmono (hrc t), fun h ↦ ?_⟩
  exact Measure.ext_of_Iic' _ _ (fun t ↦ by simp [h t]) fun t ↦ by
    rw [h t, countingPathMeasure_Iic_of_continuousWithinAt hmono (hrc t)]

end TauCeti.Probability
