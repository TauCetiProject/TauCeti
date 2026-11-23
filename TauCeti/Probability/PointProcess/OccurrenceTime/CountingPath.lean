/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Stieltjes
public import TauCeti.Probability.PointProcess.OccurrenceTime.Reconstruction
public import TauCeti.Topology.Order.Cadlag

/-!
# The counting measure of a counting path

A nondecreasing right-continuous natural-valued path `N : ℝ≥0 → ℕ` is the cumulative count of
exactly one measure on the half-line. `countingPathMeasure N` constructs it explicitly, with one
occurrence at each `pathOccurrenceTime N n`, the first time at which the path exceeds `n`.
Jumps larger than one give repeated occurrences, and the mass at zero is `N 0`.

Occurrence times are infima over rational times. For a nondecreasing right-continuous path this
is the first passage time, and for an arbitrary path it makes the construction measurable for
the product sigma-algebra on paths. Consequently a natural-valued process with measurable
coordinates gives a measurable random measure, whose cumulative counts recover the process at
all times simultaneously wherever the path is nondecreasing and right-continuous. This is how
count processes are recognized as random measures, for instance as Poisson random measures.

Conversely, the count path `t ↦ ⌊μ (0,t]⌋` of a locally finite integer-valued measure `μ`
without an atom at zero has counting measure `μ` (`countingPathMeasure_nat_count`), so every such
measure is the counting measure of a counting path.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2 and 7.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- Occurrence `n`, indexed from zero, of a natural-valued path: the infimum of the rational
times `q` (read in `ℝ≥0` through `Real.toNNReal`) at which the path exceeds `n`, or `∞` if
there are none. For a nondecreasing right-continuous path it is the first time at which the
path exceeds `n` (`pathOccurrenceTime_le_iff`). -/
noncomputable def pathOccurrenceTime (N : ℝ≥0 → ℕ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (q : ℚ) (_ : n < N (Real.toNNReal q)), (Real.toNNReal q : ℝ≥0∞)

/-- Unfold a path occurrence time as an infimum over rational times. -/
theorem pathOccurrenceTime_def (N : ℝ≥0 → ℕ) (n : ℕ) :
    pathOccurrenceTime N n =
      ⨅ (q : ℚ) (_ : n < N (Real.toNNReal q)), (Real.toNNReal q : ℝ≥0∞) :=
  (rfl)

/-- Path occurrence times are nondecreasing in their index, for every path. -/
theorem monotone_pathOccurrenceTime (N : ℝ≥0 → ℕ) : Monotone (pathOccurrenceTime N) :=
  fun _ _ hnm ↦ iInf_mono fun _ ↦ iInf_mono' fun h ↦ ⟨hnm.trans_lt h, le_rfl⟩

/-- Each path occurrence time is measurable for the product sigma-algebra on all paths. -/
@[fun_prop]
theorem measurable_pathOccurrenceTime (n : ℕ) :
    Measurable fun N : ℝ≥0 → ℕ ↦ pathOccurrenceTime N n := by
  simp_rw [pathOccurrenceTime_def, iInf_eq_if]
  exact Measurable.iInf fun q ↦ Measurable.ite
    (measurableSet_lt measurable_const (measurable_pi_apply _)) measurable_const measurable_const

/-- For a nondecreasing right-continuous path, occurrence `n` has happened by time `t` exactly
when the path exceeds `n` at `t`. -/
theorem pathOccurrenceTime_le_iff {N : ℝ≥0 → ℕ} (hmono : Monotone N)
    (hrc : IsRightContinuous N) {n : ℕ} {t : ℝ≥0} :
    pathOccurrenceTime N n ≤ t ↔ n < N t := by
  obtain ⟨u, htu, hu⟩ : ∃ u, t < u ∧ ∀ s ∈ Ioo t u, N s = N t :=
    mem_nhdsGT_iff_exists_Ioo_subset.1 (hrc.eventually_eq t)
  constructor
  · intro h
    by_contra hle
    -- Every rational time at which the path exceeds `n` is at least `u`.
    have hu_le : (u : ℝ≥0∞) ≤ pathOccurrenceTime N n := by
      refine le_iInf₂ fun q hq ↦ ENNReal.coe_le_coe.2 (le_of_not_gt fun hqu ↦ ?_)
      rcases le_or_gt (Real.toNNReal q) t with hqt | hqt
      · exact hle (hq.trans_le (hmono hqt))
      · exact hle (hu _ ⟨hqt, hqu⟩ ▸ hq)
    exact (not_le.2 htu) (ENNReal.coe_le_coe.1 (hu_le.trans h))
  · intro h
    refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
    obtain ⟨q, -, htq, hqc⟩ :=
      ENNReal.lt_iff_exists_rat_btwn.1 (lt_min (ENNReal.coe_lt_coe.2 htu) hc)
    have hqu : Real.toNNReal q < u := ENNReal.coe_lt_coe.1 (hqc.trans_le (min_le_left _ _))
    have hN : n < N (Real.toNNReal q) := hu _ ⟨ENNReal.coe_lt_coe.1 htq, hqu⟩ ▸ h
    exact (iInf₂_le q hN).trans (hqc.le.trans (min_le_right _ _))

/-- The counting measure of a natural-valued path, with one occurrence at each finite
`pathOccurrenceTime`. For a nondecreasing right-continuous path it is the unique measure whose
mass on `[0,t]` is the value of the path at `t` (`eq_countingPathMeasure_iff`). -/
noncomputable def countingPathMeasure (N : ℝ≥0 → ℕ) : Measure ℝ≥0 :=
  occurrenceTimeMeasure (pathOccurrenceTime N)

/-- Unfold the counting measure of a path as the measure of its occurrence times. -/
theorem countingPathMeasure_def (N : ℝ≥0 → ℕ) :
    countingPathMeasure N = occurrenceTimeMeasure (pathOccurrenceTime N) :=
  (rfl)

/-- Forming the counting measure is measurable for the product sigma-algebra on all paths. -/
@[fun_prop]
theorem measurable_countingPathMeasure : Measurable countingPathMeasure :=
  measurable_occurrenceTimeMeasure.comp (measurable_pi_iff.2 measurable_pathOccurrenceTime)

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

/-- The counting measure of a nondecreasing right-continuous path gives `[0,t]` the mass `N t`,
including occurrences at zero. -/
theorem countingPathMeasure_Iic {N : ℝ≥0 → ℕ} (hmono : Monotone N) (hrc : IsRightContinuous N)
    (t : ℝ≥0) : countingPathMeasure N (Iic t) = N t := by
  classical
  rw [countingPathMeasure_def, occurrenceTimeMeasure_Iic]
  simp_rw [pathOccurrenceTime_le_iff hmono hrc]
  rw [tsum_eq_sum (s := Finset.range (N t)) (fun n hn ↦ by simp_all)]
  simp [← Finset.mem_range]

/-- The counting measure of a nondecreasing right-continuous path gives `(s,t]` the mass
`N t - N s`, which is zero when `t ≤ s`. -/
theorem countingPathMeasure_Ioc {N : ℝ≥0 → ℕ} (hmono : Monotone N) (hrc : IsRightContinuous N)
    (s t : ℝ≥0) : countingPathMeasure N (Ioc s t) = (N t - N s : ℕ) := by
  rcases le_total s t with hst | hts
  · rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.2 hst) measurableSet_Iic.nullMeasurableSet
      (by simp [countingPathMeasure_Iic hmono hrc]), countingPathMeasure_Iic hmono hrc,
      countingPathMeasure_Iic hmono hrc, ENNReal.natCast_sub]
  · simp [Ioc_eq_empty_of_le hts, Nat.sub_eq_zero_of_le (hmono hts)]

/-- The counting measure of a nondecreasing right-continuous path is locally finite. -/
theorem isLocallyFiniteMeasure_countingPathMeasure {N : ℝ≥0 → ℕ} (hmono : Monotone N)
    (hrc : IsRightContinuous N) : IsLocallyFiniteMeasure (countingPathMeasure N) :=
  (countingPathMeasure N).isLocallyFiniteMeasure_of_measure_Iic_lt_top fun t ↦ by
    simp [countingPathMeasure_Iic hmono hrc]

/-- **Characterization of the counting measure of a path.** For a nondecreasing
right-continuous path, a measure is its counting measure exactly when its mass on each `[0,t]`
is the value of the path at `t`. No finiteness or integrality is assumed of the measure. -/
theorem eq_countingPathMeasure_iff {N : ℝ≥0 → ℕ} (hmono : Monotone N)
    (hrc : IsRightContinuous N) {μ : Measure ℝ≥0} :
    μ = countingPathMeasure N ↔ ∀ t, μ (Iic t) = N t := by
  refine ⟨fun h t ↦ h ▸ countingPathMeasure_Iic hmono hrc t, fun h ↦ ?_⟩
  exact Measure.ext_of_Iic' _ _ (fun t ↦ by simp [h t]) fun t ↦ by
    rw [h t, countingPathMeasure_Iic hmono hrc]

/-- The counting measure of the count path `t ↦ ⌊μ (0,t]⌋` of a locally finite integer-valued
measure without an atom at zero is the measure itself. -/
theorem countingPathMeasure_nat_count {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) (h0 : μ {0} = 0) :
    countingPathMeasure (fun t ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊) = μ := by
  refine ((eq_countingPathMeasure_iff Measure.monotone_nat_count
    hμ.isRightContinuous_nat_count).2 fun t ↦ ?_).symm
  rw [hμ.natCast_nat_count_Ioc, ← Iic_sdiff_Iic,
    measure_sdiff_null (by rwa [show Iic (0 : ℝ≥0) = {0} from Iic_bot])]

end TauCeti.Probability
