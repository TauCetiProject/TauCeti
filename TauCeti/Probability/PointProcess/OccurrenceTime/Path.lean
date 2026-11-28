/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.CountingPath
public import TauCeti.Probability.RandomMeasure.Cumulative
public import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNRat.Encodable
import TauCeti.MeasureTheory.Measure.Interval
import TauCeti.MeasureTheory.Measure.Typeclasses.Finite
import TauCeti.Probability.IdentDistrib

/-!
# Further properties of counting-path measures and law equivalences

Building on `TauCeti.Probability.PointProcess.OccurrenceTime.CountingPath`, this module records
structural, injectivity, additivity, simplicity, and law-equivalence properties of
`pathOccurrenceTime` and `countingPathMeasure`.

In particular:
* `pathOccurrenceTime` and `countingPathMeasure` depend only on the path's restriction to `ℚ≥0`,
  and whenever `f` is either monotone or right-continuous, `pathOccurrenceTime f n` equals the
  infimum over all `t : ℝ≥0`.
* When `f` is monotone and right-continuous, `countingPathMeasure` is injective and additive,
  characterizes singleton simplicity at positive times via `∃ s < t, f t ≤ f s + 1`, and recovers
  any locally finite integer-valued measure from its cumulative counts on `[0, t]` or `(a, t]`.
* Combined with the cumulative-floor maps in `TauCeti.Probability.RandomMeasure.Cumulative`, this
  gives two-sided distributional equivalences (`identDistrib_countingPathMeasure_iff`,
  `identDistrib_measure_iff_natFloor_Iic`, `identDistrib_measure_countingPathMeasure_iff`, and
  `identDistrib_measure_countingPathMeasure_iff_natFloor_Ioc`) requiring path regularity only on
  one event of full measure.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2 and 7.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal NNRat Topology

namespace TauCeti.Probability

/-! ### Rational-grid jump times of a counting path -/

/-- Jump times depend only on the restriction of the counting path to nonnegative rational
times. -/
theorem pathOccurrenceTime_congr {f g : ℝ≥0 → ℕ} (h : ∀ q : ℚ≥0, f q = g q) :
    pathOccurrenceTime f = pathOccurrenceTime g := by
  funext n
  simp only [pathOccurrenceTime_eq_iInf_nnrat, h]

/-- Larger counting paths have earlier jump times. -/
theorem pathOccurrenceTime_anti {f g : ℝ≥0 → ℕ} (h : f ≤ g) (n : ℕ) :
    pathOccurrenceTime g n ≤ pathOccurrenceTime f n := by
  simp only [pathOccurrenceTime_eq_iInf_nnrat, le_iInf_iff]
  intro q hq
  exact iInf₂_le q (hq.trans_le (h _))

/-- A jump time is infinite precisely when the path stays at most `n` at all nonnegative rational
times. -/
theorem pathOccurrenceTime_eq_top_iff (f : ℝ≥0 → ℕ) (n : ℕ) :
    pathOccurrenceTime f n = ∞ ↔ ∀ q : ℚ≥0, f q ≤ n := by
  rw [← not_lt_top_iff, pathOccurrenceTime_lt_iff]
  simp

/-- The identically zero path has all jump times infinite. -/
@[simp]
theorem pathOccurrenceTime_zero (n : ℕ) : pathOccurrenceTime 0 n = ∞ := by
  simp [pathOccurrenceTime_eq_top_iff]

private theorem pathOccurrenceTime_eq_iInf_of_le {f : ℝ≥0 → ℕ} {n : ℕ}
    (h : ∀ t : ℝ≥0, n + 1 ≤ f t → pathOccurrenceTime f n ≤ t) :
    pathOccurrenceTime f n = ⨅ (t : ℝ≥0) (_ : n + 1 ≤ f t), (t : ℝ≥0∞) := by
  refine le_antisymm ?_ ?_
  · exact le_iInf fun t ↦ le_iInf fun ht ↦ h t ht
  · simp only [pathOccurrenceTime_eq_iInf_nnrat, le_iInf_iff]
    intro q hq
    exact iInf₂_le (q : ℝ≥0) (Nat.succ_le_iff.2 hq)

/-- On a monotone path, `pathOccurrenceTime` agrees with the infimum over all `t : ℝ≥0`, without
assuming right-continuity. -/
theorem pathOccurrenceTime_eq_iInf_of_monotone {f : ℝ≥0 → ℕ} (hf : Monotone f) (n : ℕ) :
    pathOccurrenceTime f n = ⨅ (t : ℝ≥0) (_ : n + 1 ≤ f t), (t : ℝ≥0∞) :=
  pathOccurrenceTime_eq_iInf_of_le fun _ ht ↦ pathOccurrenceTime_le_of_monotone_of_le hf ht

/-- On a path that is right-continuous at `t`, reaching `n + 1` at `t` bounds
`pathOccurrenceTime f n` by `t`, without assuming monotonicity. -/
theorem pathOccurrenceTime_le_of_continuousWithinAt_of_le {f : ℝ≥0 → ℕ} {t : ℝ≥0}
    (hrc : ContinuousWithinAt f (Ioi t) t) {n : ℕ} (ht : n + 1 ≤ f t) :
    pathOccurrenceTime f n ≤ t := by
  obtain ⟨δ, hδt, hδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hrc.eventually_eq
  exact pathOccurrenceTime_le_of_forall_Ioo hδt fun s hs ↦ (hδ hs).symm ▸ ht

/-- On a right-continuous path, `pathOccurrenceTime` agrees with the infimum over all `t : ℝ≥0`,
without assuming monotonicity. -/
theorem pathOccurrenceTime_eq_iInf_of_isRightContinuous {f : ℝ≥0 → ℕ} (hrc : IsRightContinuous f)
    (n : ℕ) : pathOccurrenceTime f n = ⨅ (t : ℝ≥0) (_ : n + 1 ≤ f t), (t : ℝ≥0∞) :=
  pathOccurrenceTime_eq_iInf_of_le fun t ht ↦
    pathOccurrenceTime_le_of_continuousWithinAt_of_le (hrc t) ht

/-! ### Further properties of `countingPathMeasure` -/

/-- The reconstructed counting measure depends only on the restriction of the counting path to
nonnegative rational times. -/
theorem countingPathMeasure_congr {f g : ℝ≥0 → ℕ} (h : ∀ q : ℚ≥0, f q = g q) :
    countingPathMeasure f = countingPathMeasure g := by
  simp only [countingPathMeasure_def, pathOccurrenceTime_congr h]

/-- The zero counting path gives the zero measure. -/
@[simp]
theorem countingPathMeasure_zero : countingPathMeasure 0 = 0 := by
  ext s _
  simp [countingPathMeasure_def, occurrenceTimeMeasure_apply]

/-- Recovering cumulative counts from `countingPathMeasure f` reproduces `f` whenever `f` is
monotone and right-continuous. -/
theorem natFloor_countingPathMeasure_Iic {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) :
    (fun t ↦ ⌊(countingPathMeasure f (Iic t)).toNNReal⌋₊) = f := by
  funext t
  simp [countingPathMeasure_Iic_of_continuousWithinAt hf (hrc t)]

/-- Recovering cumulative counts on `(a, t]` from `countingPathMeasure f` reproduces
`fun t ↦ f t - f a` whenever `f` is monotone and right-continuous. -/
theorem natFloor_countingPathMeasure_Ioc {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) (a : ℝ≥0) :
    (fun t ↦ ⌊(countingPathMeasure f (Ioc a t)).toNNReal⌋₊) = fun t ↦ f t - f a := by
  funext t
  simp [countingPathMeasure_Ioc hf hrc a t]

/-- On monotone right-continuous paths, `countingPathMeasure` is injective. -/
theorem countingPathMeasure_inj {f g : ℝ≥0 → ℕ} (hf : Monotone f) (hrcf : IsRightContinuous f)
    (hg : Monotone g) (hrcg : IsRightContinuous g) :
    countingPathMeasure f = countingPathMeasure g ↔ f = g :=
  ⟨fun h ↦ by rw [← natFloor_countingPathMeasure_Iic hf hrcf, h,
    natFloor_countingPathMeasure_Iic hg hrcg], congrArg countingPathMeasure⟩

/-- On monotone right-continuous paths, `pathOccurrenceTime` is injective. -/
theorem pathOccurrenceTime_inj {f g : ℝ≥0 → ℕ} (hf : Monotone f) (hrcf : IsRightContinuous f)
    (hg : Monotone g) (hrcg : IsRightContinuous g) :
    pathOccurrenceTime f = pathOccurrenceTime g ↔ f = g :=
  ⟨fun h ↦ (countingPathMeasure_inj hf hrcf hg hrcg).1
    (by simp only [countingPathMeasure_def, h]), congrArg pathOccurrenceTime⟩

/-- On monotone right-continuous paths, `countingPathMeasure` is additive. -/
@[simp]
theorem countingPathMeasure_add {f g : ℝ≥0 → ℕ} (hf : Monotone f) (hrcf : IsRightContinuous f)
    (hg : Monotone g) (hrcg : IsRightContinuous g) :
    countingPathMeasure (f + g) = countingPathMeasure f + countingPathMeasure g := by
  have hadd : Monotone (f + g) := hf.add hg
  have hrc : IsRightContinuous (f + g) := hrcf.continuous_comp₂ hrcg continuous_add
  refine ((eq_countingPathMeasure_iff hadd hrc).2 fun t ↦ ?_).symm
  simp [countingPathMeasure_Iic_of_continuousWithinAt hf (hrcf t),
    countingPathMeasure_Iic_of_continuousWithinAt hg (hrcg t)]

/-- On a monotone right-continuous path, the atom at the origin equals the initial count `f 0`. -/
@[simp]
theorem countingPathMeasure_singleton_zero {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) :
    countingPathMeasure f {0} = f 0 := by
  rw [← NNReal.bot_eq_zero, ← Set.Iic_bot,
    countingPathMeasure_Iic_of_continuousWithinAt hf (hrc _), NNReal.bot_eq_zero]

/-- At any positive time `t > 0`, the atom mass of `countingPathMeasure f` at `{t}` equals
`f t - f s` for some strictly earlier time `s < t`. -/
theorem exists_lt_countingPathMeasure_singleton_eq {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) {t : ℝ≥0} (ht : 0 < t) :
    ∃ s < t, countingPathMeasure f {t} = ((f t - f s : ℕ) : ℝ≥0∞) := by
  have : IsLocallyFiniteMeasure (countingPathMeasure f) :=
    isLocallyFiniteMeasure_countingPathMeasure_of_monotone hf
  obtain ⟨s, hst, hs⟩ :=
    (isIntegerValued_countingPathMeasure f).exists_nat_count_le_add_floor ht
  rw [countingPathMeasure_Ioc hf hrc, countingPathMeasure_Ioc hf hrc] at hs
  simp only [ENNReal.toNNReal_natCast, Nat.floor_natCast] at hs
  have hle : countingPathMeasure f {t} ≤ ((f t - f s : ℕ) : ℝ≥0∞) :=
    Measure.measure_singleton_le_natCast_sub
      (countingPathMeasure_Iic_of_continuousWithinAt hf (hrc s))
      (countingPathMeasure_Iic_of_continuousWithinAt hf (hrc t)) hst
  have hfin : countingPathMeasure f {t} < ∞ :=
    hle.trans_lt (ENNReal.natCast_lt_top _)
  have hf0_s : f 0 ≤ f s := hf (zero_le (a := s))
  have hf0_t : f 0 ≤ f t := hf (zero_le (a := t))
  have hsub : f t - f s ≤ ⌊(countingPathMeasure f {t}).toNNReal⌋₊ := by omega
  have hge : ((f t - f s : ℕ) : ℝ≥0∞) ≤ countingPathMeasure f {t} := by
    rw [← (isIntegerValued_countingPathMeasure f).natCast_natFloor_apply hfin]
    exact_mod_cast hsub
  exact ⟨s, hst, le_antisymm hle hge⟩

/-- At any positive time `t > 0`, the point measure of a monotone right-continuous path has
multiplicity at most one if and only if some strictly earlier time `s < t` satisfies
`f t ≤ f s + 1`. -/
theorem countingPathMeasure_singleton_le_one_iff {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) {t : ℝ≥0} (ht : 0 < t) :
    countingPathMeasure f {t} ≤ 1 ↔ ∃ s < t, f t ≤ f s + 1 := by
  refine ⟨fun hle ↦ ?_, fun ⟨s, hst, hs⟩ ↦ ?_⟩
  · obtain ⟨s, hst, hs⟩ := exists_lt_countingPathMeasure_singleton_eq hf hrc ht
    have hsub : ((f t - f s : ℕ) : ℝ≥0∞) ≤ 1 := hs ▸ hle
    have hsub' : f t - f s ≤ 1 := by exact_mod_cast hsub
    exact ⟨s, hst, by omega⟩
  · calc
      countingPathMeasure f {t} ≤ ((f t - f s : ℕ) : ℝ≥0∞) :=
        Measure.measure_singleton_le_natCast_sub
          (countingPathMeasure_Iic_of_continuousWithinAt hf (hrc s))
          (countingPathMeasure_Iic_of_continuousWithinAt hf (hrc t)) hst
      _ ≤ 1 := by
        have : f t - f s ≤ 1 := by omega
        exact_mod_cast this

/-- A monotone right-continuous path produces a simple point measure on `ℝ≥0` if and only if
`f 0 ≤ 1` and no positive time has a left-hand jump of size two or more. -/
theorem forall_countingPathMeasure_singleton_le_one_iff {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) :
    (∀ t, countingPathMeasure f {t} ≤ 1) ↔ f 0 ≤ 1 ∧ ∀ t > 0, ∃ s < t, f t ≤ f s + 1 := by
  refine ⟨fun h ↦ ⟨?_, fun t ht ↦ (countingPathMeasure_singleton_le_one_iff hf hrc ht).1 (h t)⟩,
    fun ⟨h0, hpos⟩ t ↦ ?_⟩
  · have h0 := h 0
    rw [countingPathMeasure_singleton_zero hf hrc] at h0
    exact_mod_cast h0
  · rcases eq_or_lt_of_le (zero_le (a := t)) with rfl | ht
    · rw [countingPathMeasure_singleton_zero hf hrc]
      exact_mod_cast h0
    · exact (countingPathMeasure_singleton_le_one_iff hf hrc ht).2 (hpos t ht)

/-- Any measure on `ℝ≥0` whose cumulative masses agree with a natural-valued path `f` equals
`countingPathMeasure f`. Local finiteness and integrality of `μ`, as well as monotonicity and
right-continuity of `f`, follow rather than being assumed. -/
theorem eq_countingPathMeasure_of_measure_Iic_eq {μ : Measure ℝ≥0} {f : ℝ≥0 → ℕ}
    (hμ : ∀ t, μ (Iic t) = f t) :
    μ = countingPathMeasure f := by
  have : IsLocallyFiniteMeasure μ := μ.isLocallyFiniteMeasure_of_measure_Iic_lt_top fun t ↦ by
    rw [hμ t]; exact ENNReal.natCast_lt_top _
  have hf_eq : f = fun t ↦ ⌊(μ (Iic t)).toNNReal⌋₊ := funext fun t ↦ by simp [hμ t]
  have hf : Monotone f := hf_eq ▸ μ.monotone_natFloor_Iic
  have hrc : IsRightContinuous f := hf_eq ▸ μ.isRightContinuous_natFloor_Iic
  exact (eq_countingPathMeasure_iff hf hrc).2 hμ

/-- If the sample paths of `N` are monotone and right-continuous on one event of full measure, then
the reconstructed measure `countingPathMeasure (N · ω)` has cumulative mass `N t ω` on `[0, t]`
simultaneously at all times almost surely. -/
theorem ae_forall_countingPathMeasure_Iic_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : ℝ≥0 → Ω → ℕ} (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    ∀ᵐ ω ∂P, ∀ t, countingPathMeasure (N · ω) (Iic t) = N t ω :=
  hreg.mono fun _ ⟨hf, hrc⟩ t ↦ countingPathMeasure_Iic_of_continuousWithinAt hf (hrc t)

end TauCeti.Probability

open TauCeti.Probability

namespace MeasureTheory.Measure

/-! ### Reconstructing measures from cumulative count floors -/

variable {μ : Measure ℝ≥0}

/-- Reconstructing a temporal measure from its cumulative natural-valued counts on `[0, t]`
recovers any locally finite integer-valued measure, including any atom at zero. -/
@[simp]
theorem IsIntegerValued.countingPathMeasure_natFloor_Iic [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) :
    countingPathMeasure (fun t ↦ ⌊(μ (Iic t)).toNNReal⌋₊) = μ :=
  (eq_countingPathMeasure_of_measure_Iic_eq fun t ↦ (hμ.natCast_natFloor_Iic t).symm).symm

/-- Jump times of the cumulative natural-valued counts on `[0, t]` agree with `μ.occurrenceTime`
for any locally finite integer-valued measure. -/
@[simp]
theorem IsIntegerValued.pathOccurrenceTime_natFloor_Iic [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) :
    pathOccurrenceTime (fun t ↦ ⌊(μ (Iic t)).toNNReal⌋₊) = μ.occurrenceTime := by
  rw [← occurrenceTime_countingPathMeasure, hμ.countingPathMeasure_natFloor_Iic]

/-- Reconstructing a temporal measure from its natural-valued counts on `(a, t]` retains the
restriction to `(a, ∞)`. -/
@[simp]
theorem IsIntegerValued.countingPathMeasure_natFloor_Ioc [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) (a : ℝ≥0) :
    countingPathMeasure (fun t ↦ ⌊(μ (Ioc a t)).toNNReal⌋₊) = μ.restrict (Ioi a) := by
  simpa only [μ.restrict_Ioi_apply_Iic a] using
    (hμ.restrict (A := Ioi a)).countingPathMeasure_natFloor_Iic

end MeasureTheory.Measure

namespace TauCeti.Probability

/-! ### Equivalence of count-path laws and random-measure laws -/

section LawEquivalence

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'}

private theorem natFloor_Iic_countingPathMeasure_ae_eq {N : ℝ≥0 → Ω → ℕ}
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    (fun ω t ↦ ⌊(countingPathMeasure (N · ω) (Iic t)).toNNReal⌋₊) =ᵐ[P] fun ω t ↦ N t ω := by
  filter_upwards [hreg] with ω ⟨hf, hrc⟩
  exact natFloor_countingPathMeasure_Iic hf hrc

private theorem countingPathMeasure_natFloor_Iic_ae_eq {M : Ω → Measure ℝ≥0}
    (hreg : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω) ∧ (M ω).IsIntegerValued) :
    (fun ω ↦ countingPathMeasure (fun t ↦ ⌊(M ω (Iic t)).toNNReal⌋₊)) =ᵐ[P] M := by
  filter_upwards [hreg] with ω ⟨_, hint⟩
  exact hint.countingPathMeasure_natFloor_Iic

/-- For natural-valued processes whose paths are monotone and right-continuous on one event of
full measure, equality in law of the reconstructed random measures is equivalent to equality in
law of the processes on `ℝ≥0 → ℕ`. -/
theorem identDistrib_countingPathMeasure_iff {N : ℝ≥0 → Ω → ℕ} {N' : ℝ≥0 → Ω' → ℕ}
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω))
    (hreg' : ∀ᵐ ω ∂Q, Monotone (N' · ω) ∧ IsRightContinuous (N' · ω)) :
    IdentDistrib (fun ω ↦ countingPathMeasure (N · ω))
        (fun ω ↦ countingPathMeasure (N' · ω)) P Q ↔
      IdentDistrib (fun ω t ↦ N t ω) (fun ω t ↦ N' t ω) P Q :=
  ⟨fun h ↦ (h.comp measurable_natFloor_measure_Iic).congr
    (natFloor_Iic_countingPathMeasure_ae_eq hreg)
    (natFloor_Iic_countingPathMeasure_ae_eq hreg'),
  fun h ↦ h.comp measurable_countingPathMeasure⟩

/-- For almost surely locally finite integer-valued random measures on `ℝ≥0`, equality in law is
equivalent to equality in law of their natural-valued cumulative count processes on `[0, t]`. -/
theorem identDistrib_measure_iff_natFloor_Iic {M : Ω → Measure ℝ≥0} {M' : Ω' → Measure ℝ≥0}
    (hreg : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω) ∧ (M ω).IsIntegerValued)
    (hreg' : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (M' ω) ∧ (M' ω).IsIntegerValued) :
    IdentDistrib M M' P Q ↔
      IdentDistrib (fun ω t ↦ ⌊(M ω (Iic t)).toNNReal⌋₊)
        (fun ω t ↦ ⌊(M' ω (Iic t)).toNNReal⌋₊) P Q :=
  ⟨fun h ↦ h.comp measurable_natFloor_measure_Iic,
  fun h ↦ (h.comp measurable_countingPathMeasure).congr
    (countingPathMeasure_natFloor_Iic_ae_eq hreg)
    (countingPathMeasure_natFloor_Iic_ae_eq hreg')⟩

/-- Direct law comparison between an almost surely locally finite integer-valued random measure
`M` and the measure reconstructed from an almost surely monotone right-continuous count process
`N`. -/
theorem identDistrib_measure_countingPathMeasure_iff {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω' → ℕ}
    (hregM : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω) ∧ (M ω).IsIntegerValued)
    (hregN : ∀ᵐ ω ∂Q, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IdentDistrib M (fun ω ↦ countingPathMeasure (N · ω)) P Q ↔
      IdentDistrib (fun ω t ↦ ⌊(M ω (Iic t)).toNNReal⌋₊) (fun ω t ↦ N t ω) P Q :=
  ⟨fun h ↦ (h.comp measurable_natFloor_measure_Iic).congr
    .rfl (natFloor_Iic_countingPathMeasure_ae_eq hregN),
  fun h ↦ (h.comp measurable_countingPathMeasure).congr
    (countingPathMeasure_natFloor_Iic_ae_eq hregM) .rfl⟩

/-- When `M` almost surely has no mass at the origin, comparing `M` in law with
`countingPathMeasure (N · ω)` is also equivalent to comparing the counts of `M` on `(0, t]` with
`N`. -/
theorem identDistrib_measure_countingPathMeasure_iff_natFloor_Ioc
    {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω' → ℕ}
    (hregM : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω) ∧ (M ω).IsIntegerValued)
    (h0M : ∀ᵐ ω ∂P, M ω {0} = 0)
    (hregN : ∀ᵐ ω ∂Q, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IdentDistrib M (fun ω ↦ countingPathMeasure (N · ω)) P Q ↔
      IdentDistrib (fun ω t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) (fun ω t ↦ N t ω) P Q := by
  have heqM : (fun ω t ↦ ⌊(M ω (Iic t)).toNNReal⌋₊) =ᵐ[P]
      fun ω t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ := by
    filter_upwards [h0M] with ω h0
    funext t
    rw [← (M ω).measure_Ioc_bot_eq_Iic h0 t, NNReal.bot_eq_zero]
  rw [identDistrib_measure_countingPathMeasure_iff hregM hregN]
  exact ⟨fun h ↦ h.congr heqM .rfl, fun h ↦ h.congr heqM.symm .rfl⟩

end LawEquivalence

end TauCeti.Probability
