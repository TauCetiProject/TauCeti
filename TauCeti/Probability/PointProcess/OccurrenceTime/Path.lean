/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Reconstruction
public import TauCeti.Probability.RandomMeasure.Cumulative
public import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNRat.Encodable
import TauCeti.MeasureTheory.Measure.Interval
import TauCeti.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Converting between counting paths and temporal point measures

For a counting path `f : ℝ≥0 → ℕ`, `countJumpTime f n` is the infimum of nonnegative rational
times at which `f` reaches `n + 1`, with value `∞` if this threshold is never reached on `ℚ≥0`,
and `countPathMeasure f` is the associated sum of Dirac masses at the finite jump times.

Restricting the infimum in the definition to `ℚ≥0` makes `countJumpTime` and `countPathMeasure`
measurable on the entire product space `ℝ≥0 → ℕ` without restricting the domain to regular paths
or requiring measurability of a path-regularity event. Whenever `f` is either monotone or
right-continuous, `countJumpTime f n` agrees with the uncountable infimum over all `t : ℝ≥0`.
Whenever `f` is monotone, its natural values exclude finite-time explosion, so `countJumpTime f`
tends to `∞` and `countPathMeasure f` is locally finite.

When `f` is both monotone and right-continuous, `countPathMeasure f` has cumulative mass
`countPathMeasure f (Iic t) = f t` at every time (retaining any initial mass `f 0` at the origin),
interval mass `f t - f s` on `(s, t]`, and singleton mass at most one at `t > 0` if and only if
some `s < t` satisfies `f t ≤ f s + 1`. Consequently, `countPathMeasure` and `countJumpTime` are
injective and `countPathMeasure` is additive on monotone right-continuous paths. Together with the
measurable cumulative-floor maps from `Measure ℝ≥0` to `ℝ≥0 → ℕ`, this gives a measurable two-sided
conversion between locally finite integer-valued measures on `ℝ≥0` and monotone right-continuous
natural-valued paths, and identifies equality in law of random counting measures with equality in
law of their count processes when path regularity holds on one event of full measure.

## Main declarations

* `TauCeti.Probability.countJumpTime`: rational-grid threshold times of a path `f : ℝ≥0 → ℕ`.
* `TauCeti.Probability.countPathMeasure`: the integer-valued measure on `ℝ≥0` built from
  `countJumpTime f`.
* `TauCeti.Probability.natFloor_countPathMeasure_Iic`, `countPathMeasure_inj`, `countJumpTime_inj`,
  `countPathMeasure_add`: left inverse, injectivity, and additivity on regular paths.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 2 and 7.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal NNRat Topology

namespace TauCeti.Probability

/-! ### Rational-grid jump times of a counting path -/

/-- The `n`-th jump time (indexed from zero) of a counting path `f : ℝ≥0 → ℕ`, defined on the
nonnegative rationals so that the map is measurable for the product σ-algebra on `ℝ≥0 → ℕ`
without regularity assumptions on `f`. On monotone or right-continuous paths this coincides with
the infimum over all `t : ℝ≥0`. -/
noncomputable def countJumpTime (f : ℝ≥0 → ℕ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ (q : ℚ≥0) (_ : n + 1 ≤ f q), ((q : ℝ≥0) : ℝ≥0∞)

/-- Expand `countJumpTime` as an infimum over nonnegative rational observation times. -/
theorem countJumpTime_def (f : ℝ≥0 → ℕ) (n : ℕ) :
    countJumpTime f n = ⨅ (q : ℚ≥0) (_ : n + 1 ≤ f q), ((q : ℝ≥0) : ℝ≥0∞) := (rfl)

/-- A jump time is strictly below a bound exactly when some earlier nonnegative rational time
already reaches the count threshold `n + 1`. -/
theorem countJumpTime_lt_iff (f : ℝ≥0 → ℕ) (n : ℕ) (b : ℝ≥0∞) :
    countJumpTime f n < b ↔ ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < b ∧ n + 1 ≤ f q := by
  simp only [countJumpTime_def, iInf_lt_iff]
  exact ⟨fun ⟨q, hq, hb⟩ ↦ ⟨q, hb, hq⟩, fun ⟨q, hb, hq⟩ ↦ ⟨q, hq, hb⟩⟩

/-- Reaching `n + 1` at a nonnegative rational time bounds the `n`-th jump time. -/
theorem countJumpTime_le_nnrat {f : ℝ≥0 → ℕ} {n : ℕ} {q : ℚ≥0} (hq : n + 1 ≤ f q) :
    countJumpTime f n ≤ (q : ℝ≥0) :=
  iInf_le_of_le q (iInf_le_of_le hq le_rfl)

/-- Jump times are ordered in the index `n`, retaining repeated times for multiple jumps. -/
theorem monotone_countJumpTime (f : ℝ≥0 → ℕ) : Monotone (countJumpTime f) := by
  intro m n hmn
  simp only [countJumpTime_def, le_iInf_iff]
  intro q hq
  exact countJumpTime_le_nnrat ((Nat.add_le_add_right hmn 1).trans hq)

/-- Larger counting paths have earlier jump times. -/
theorem countJumpTime_anti {f g : ℝ≥0 → ℕ} (h : f ≤ g) (n : ℕ) :
    countJumpTime g n ≤ countJumpTime f n := by
  simp only [countJumpTime_def, le_iInf_iff]
  intro q hq
  exact countJumpTime_le_nnrat (hq.trans (h q))

/-- A jump time is infinite precisely when the path stays at most `n` at all nonnegative rational
times. -/
theorem countJumpTime_eq_top_iff (f : ℝ≥0 → ℕ) (n : ℕ) :
    countJumpTime f n = ∞ ↔ ∀ q : ℚ≥0, f q ≤ n := by
  rw [← not_lt_top_iff, countJumpTime_lt_iff]
  simp

/-- The identically zero path has all jump times infinite. -/
@[simp]
theorem countJumpTime_zero (n : ℕ) : countJumpTime 0 n = ∞ := by
  simp [countJumpTime_eq_top_iff]

/-- Extracting the `n`-th jump time is measurable whenever the process is measurable at
nonnegative rational times. -/
theorem measurable_countJumpTime_of_nnrat {Ω : Type*} [MeasurableSpace Ω] {N : ℝ≥0 → Ω → ℕ}
    (hN : ∀ q : ℚ≥0, Measurable (N q)) (n : ℕ) :
    Measurable fun ω ↦ countJumpTime (N · ω) n := by
  have heq (ω : Ω) : countJumpTime (N · ω) n =
      ⨅ q : ℚ≥0, if n + 1 ≤ N q ω then ((q : ℝ≥0) : ℝ≥0∞) else ⊤ := by
    rw [countJumpTime_def]
    congr 1; funext q
    by_cases hq : n + 1 ≤ N q ω
    · simp [hq]
    · simp [hq]
  simp_rw [heq]
  exact Measurable.iInf fun q ↦
    measurable_const.ite (measurableSet_le measurable_const (hN q)) measurable_const

/-- Extracting the `n`-th jump time is measurable on `ℝ≥0 → ℕ` with its product σ-algebra. -/
@[fun_prop]
theorem measurable_countJumpTime (n : ℕ) : Measurable fun f : ℝ≥0 → ℕ ↦ countJumpTime f n :=
  measurable_countJumpTime_of_nnrat (fun q ↦ measurable_pi_apply (q : ℝ≥0)) n

private theorem exists_nnrat_btwn {a b : ℝ≥0} (h : a < b) :
    ∃ r : ℚ≥0, a < (r : ℝ≥0) ∧ (r : ℝ≥0) < b := by
  obtain ⟨q, hq, haq, hqb⟩ := (NNReal.lt_iff_exists_rat_btwn a b).1 h
  let r : ℚ≥0 := ⟨q, hq⟩
  have hcoe : (r : ℝ≥0) = Real.toNNReal q :=
    NNReal.eq (by rw [Real.coe_toNNReal _ (Rat.cast_nonneg.2 hq)]; norm_cast)
  exact ⟨r, hcoe ▸ haq, hcoe ▸ hqb⟩

/-- If `f` stays at least `n + 1` throughout a nonempty open interval `(t, δ)`, then
`countJumpTime f n ≤ t`, without global monotonicity or right-continuity assumptions. -/
theorem countJumpTime_le_of_forall_Ioo {f : ℝ≥0 → ℕ} {t δ : ℝ≥0} (hδ : t < δ) {n : ℕ}
    (h : ∀ s ∈ Ioo t δ, n + 1 ≤ f s) : countJumpTime f n ≤ t := by
  refine le_of_forall_gt fun b hb ↦ ?_
  obtain ⟨u, htu, hub⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
  obtain ⟨r, htr, hrv⟩ := exists_nnrat_btwn (lt_min (ENNReal.coe_lt_coe.1 htu) hδ)
  exact (countJumpTime_le_nnrat (h r ⟨htr, hrv.trans_le (min_le_right _ _)⟩)).trans_lt
    ((ENNReal.coe_lt_coe.2 (hrv.trans_le (min_le_left _ _))).trans hub)

/-- On a monotone path, reaching `n + 1` at any real time `t` bounds `countJumpTime f n` by `t`. -/
theorem countJumpTime_le_of_le_of_monotone {f : ℝ≥0 → ℕ} (hf : Monotone f) {n : ℕ} {t : ℝ≥0}
    (ht : n + 1 ≤ f t) : countJumpTime f n ≤ t :=
  countJumpTime_le_of_forall_Ioo (lt_add_one t) fun _ hs ↦ ht.trans (hf hs.1.le)

/-- On a monotone path, `countJumpTime` agrees with the infimum over all `t : ℝ≥0`, without
assuming right-continuity. -/
theorem countJumpTime_eq_iInf_of_monotone {f : ℝ≥0 → ℕ} (hf : Monotone f) (n : ℕ) :
    countJumpTime f n = ⨅ (t : ℝ≥0) (_ : n + 1 ≤ f t), (t : ℝ≥0∞) := by
  refine le_antisymm ?_ ?_
  · exact le_iInf fun t ↦ le_iInf fun ht ↦ countJumpTime_le_of_le_of_monotone hf ht
  · exact le_iInf fun q ↦ le_iInf fun hq ↦ iInf_le_of_le (q : ℝ≥0) (iInf_le_of_le hq le_rfl)

/-- On a path that is right-continuous at `t`, reaching `n + 1` at `t` bounds `countJumpTime f n`
by `t`, without assuming monotonicity. -/
theorem countJumpTime_le_of_le_of_continuousWithinAt {f : ℝ≥0 → ℕ} {t : ℝ≥0}
    (hrc : ContinuousWithinAt f (Ioi t) t) {n : ℕ} (ht : n + 1 ≤ f t) :
    countJumpTime f n ≤ t := by
  have hev : ∀ᶠ s in 𝓝[>] t, f s = f t :=
    tendsto_pure.1 (by simpa only [ContinuousWithinAt, nhds_discrete] using hrc)
  obtain ⟨δ, hδt, hδ⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  exact countJumpTime_le_of_forall_Ioo hδt fun s hs ↦ (hδ hs).symm ▸ ht

/-- On a right-continuous path, `countJumpTime` agrees with the infimum over all `t : ℝ≥0`,
without assuming monotonicity. -/
theorem countJumpTime_eq_iInf_of_isRightContinuous {f : ℝ≥0 → ℕ} (hrc : IsRightContinuous f)
    (n : ℕ) : countJumpTime f n = ⨅ (t : ℝ≥0) (_ : n + 1 ≤ f t), (t : ℝ≥0∞) := by
  refine le_antisymm ?_ ?_
  · exact le_iInf fun t ↦ le_iInf fun ht ↦ countJumpTime_le_of_le_of_continuousWithinAt (hrc t) ht
  · exact le_iInf fun q ↦ le_iInf fun hq ↦ iInf_le_of_le (q : ℝ≥0) (iInf_le_of_le hq le_rfl)

/-- For a monotone path that is right-continuous at `t`, the `n`-th jump occurs on `[0, t]` if and
only if `n + 1 ≤ f t`. -/
theorem countJumpTime_le_coe_iff_of_continuousWithinAt {f : ℝ≥0 → ℕ} (hf : Monotone f) {t : ℝ≥0}
    (hrc : ContinuousWithinAt f (Ioi t) t) (n : ℕ) :
    countJumpTime f n ≤ t ↔ n + 1 ≤ f t := by
  refine ⟨fun h ↦ ?_, countJumpTime_le_of_le_of_monotone hf⟩
  apply ge_of_tendsto hrc
  filter_upwards [self_mem_nhdsWithin] with s hs
  obtain ⟨q, hqs, hq⟩ := (countJumpTime_lt_iff f n s).1 (h.trans_lt (ENNReal.coe_lt_coe.2 hs))
  exact hq.trans (hf (ENNReal.coe_le_coe.1 hqs.le))

/-- For a monotone right-continuous path, the `n`-th jump occurs on `[0, t]` if and only if
`n + 1 ≤ f t`. -/
@[simp]
theorem countJumpTime_le_coe_iff {f : ℝ≥0 → ℕ} (hf : Monotone f) (hrc : IsRightContinuous f)
    (n : ℕ) (t : ℝ≥0) :
    countJumpTime f n ≤ t ↔ n + 1 ≤ f t :=
  countJumpTime_le_coe_iff_of_continuousWithinAt hf (hrc t) n

/-- Every monotone natural-valued path has jump times tending to `∞`: finiteness of `f` at each
time prevents finite-time explosion even without right-continuity. -/
theorem tendsto_countJumpTime_nhds_top {f : ℝ≥0 → ℕ} (hf : Monotone f) :
    Tendsto (countJumpTime f) atTop (𝓝 ∞) := by
  refine ENNReal.tendsto_nhds_top_iff_nnreal.2 fun x ↦ ?_
  let q : ℚ≥0 := ⌈x⌉₊ + 1
  have hxq : x < (q : ℝ≥0) := (Nat.le_ceil x).trans_lt (by simp [q])
  filter_upwards [eventually_ge_atTop (f q)] with n hn
  refine (ENNReal.coe_lt_coe.2 hxq).trans_le ?_
  simp only [countJumpTime_def, le_iInf_iff]
  intro r hr
  exact ENNReal.coe_le_coe.2 (le_of_not_gt fun hqr : (r : ℝ≥0) < q ↦
    not_le_of_gt (Nat.lt_succ_of_le ((hf hqr.le).trans hn)) hr)

/-! ### The point measure reconstructed from a counting path -/

/-- The temporal counting measure associated to a path `f : ℝ≥0 → ℕ`, placing one unit mass at
each finite entry of `countJumpTime f`. -/
noncomputable def countPathMeasure (f : ℝ≥0 → ℕ) : Measure ℝ≥0 :=
  occurrenceTimeMeasure (countJumpTime f)

/-- Expand `countPathMeasure` in terms of `occurrenceTimeMeasure` and `countJumpTime`. -/
theorem countPathMeasure_def (f : ℝ≥0 → ℕ) :
    countPathMeasure f = occurrenceTimeMeasure (countJumpTime f) := (rfl)

/-- Reconstructing the temporal measure from a counting process is measurable as soon as the
process is measurable at nonnegative rational times. No measurability of any regular-path event is
required. -/
theorem measurable_countPathMeasure_of_nnrat {Ω : Type*} [MeasurableSpace Ω] {N : ℝ≥0 → Ω → ℕ}
    (hN : ∀ q : ℚ≥0, Measurable (N q)) :
    Measurable fun ω ↦ countPathMeasure (N · ω) :=
  measurable_occurrenceTimeMeasure.comp
    (measurable_pi_iff.2 (measurable_countJumpTime_of_nnrat hN))

/-- Reconstructing the temporal measure from a counting path is measurable for the product
σ-algebra on `ℝ≥0 → ℕ`. -/
@[fun_prop]
theorem measurable_countPathMeasure : Measurable countPathMeasure :=
  measurable_countPathMeasure_of_nnrat fun q ↦ measurable_pi_apply (q : ℝ≥0)

/-- The zero counting path gives the zero measure. -/
@[simp]
theorem countPathMeasure_zero : countPathMeasure 0 = 0 := by
  ext s _
  simp [countPathMeasure_def, occurrenceTimeMeasure_apply]

open Classical in
/-- Evaluating `countPathMeasure f` on any set counts finite jump times in that set, with
multiplicity. -/
theorem countPathMeasure_apply (f : ℝ≥0 → ℕ) (s : Set ℝ≥0) :
    countPathMeasure f s =
      ∑' n, if countJumpTime f n ≠ ∞ ∧ (countJumpTime f n).toNNReal ∈ s then (1 : ℝ≥0∞) else 0 :=
  occurrenceTimeMeasure_apply (countJumpTime f) s

/-- Lower Lebesgue integration against `countPathMeasure f` sums over all finite jump times. -/
@[simp]
theorem lintegral_countPathMeasure (f : ℝ≥0 → ℕ) (g : ℝ≥0 → ℝ≥0∞) :
    ∫⁻ x, g x ∂countPathMeasure f =
      ∑' n, if countJumpTime f n = ∞ then 0 else g (countJumpTime f n).toNNReal :=
  lintegral_occurrenceTimeMeasure (countJumpTime f) g

/-- The measure reconstructed from any path is integer-valued, without regularity assumptions. -/
@[simp]
theorem isIntegerValued_countPathMeasure (f : ℝ≥0 → ℕ) :
    (countPathMeasure f).IsIntegerValued :=
  isIntegerValued_occurrenceTimeMeasure (countJumpTime f)

/-- Taking occurrence times of `countPathMeasure f` recovers `countJumpTime f` for every path `f`,
without regularity assumptions. -/
@[simp]
theorem occurrenceTime_countPathMeasure (f : ℝ≥0 → ℕ) :
    (countPathMeasure f).occurrenceTime = countJumpTime f :=
  occurrenceTime_occurrenceTimeMeasure (monotone_countJumpTime f)

/-- For any monotone natural-valued path, `countPathMeasure f` is locally finite. -/
theorem isLocallyFiniteMeasure_countPathMeasure {f : ℝ≥0 → ℕ} (hf : Monotone f) :
    IsLocallyFiniteMeasure (countPathMeasure f) :=
  isLocallyFiniteMeasure_occurrenceTimeMeasure (tendsto_countJumpTime_nhds_top hf)

/-- For a monotone path that is right-continuous at `t`, the cumulative mass of
`countPathMeasure f` on `[0, t]` equals `f t`. -/
theorem countPathMeasure_Iic_of_continuousWithinAt {f : ℝ≥0 → ℕ} (hf : Monotone f) {t : ℝ≥0}
    (hrc : ContinuousWithinAt f (Ioi t) t) :
    countPathMeasure f (Iic t) = f t := by
  classical
  rw [countPathMeasure_def, occurrenceTimeMeasure_Iic]
  have heq (n : ℕ) : countJumpTime f n ≤ t ↔ n < f t := by
    rw [countJumpTime_le_coe_iff_of_continuousWithinAt hf hrc]
    exact Nat.succ_le_iff
  simp_rw [heq]
  rw [tsum_eq_sum (s := Finset.range (f t)) (fun n hn ↦ by simp_all)]
  simp [← Finset.mem_range]

/-- For a monotone right-continuous path, `countPathMeasure f` assigns mass `f t` to `[0, t]`,
including any initial mass at zero. -/
@[simp]
theorem countPathMeasure_Iic {f : ℝ≥0 → ℕ} (hf : Monotone f) (hrc : IsRightContinuous f)
    (t : ℝ≥0) :
    countPathMeasure f (Iic t) = f t :=
  countPathMeasure_Iic_of_continuousWithinAt hf (hrc t)

/-- Recovering cumulative counts from `countPathMeasure f` reproduces `f` whenever `f` is
monotone and right-continuous. -/
theorem natFloor_countPathMeasure_Iic {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) :
    (fun t ↦ ⌊(countPathMeasure f (Iic t)).toNNReal⌋₊) = f := by
  funext t
  simp [countPathMeasure_Iic hf hrc t]

/-- On monotone right-continuous paths, `countPathMeasure` is injective. -/
theorem countPathMeasure_inj {f g : ℝ≥0 → ℕ} (hf : Monotone f) (hrcf : IsRightContinuous f)
    (hg : Monotone g) (hrcg : IsRightContinuous g) :
    countPathMeasure f = countPathMeasure g ↔ f = g :=
  ⟨fun h ↦ by rw [← natFloor_countPathMeasure_Iic hf hrcf, h,
    natFloor_countPathMeasure_Iic hg hrcg], congrArg countPathMeasure⟩

/-- On monotone right-continuous paths, `countJumpTime` is injective. -/
theorem countJumpTime_inj {f g : ℝ≥0 → ℕ} (hf : Monotone f) (hrcf : IsRightContinuous f)
    (hg : Monotone g) (hrcg : IsRightContinuous g) :
    countJumpTime f = countJumpTime g ↔ f = g :=
  ⟨fun h ↦ (countPathMeasure_inj hf hrcf hg hrcg).1
    (by simp only [countPathMeasure_def, h]), congrArg countJumpTime⟩

/-- On monotone right-continuous paths, `countPathMeasure` is additive. -/
@[simp]
theorem countPathMeasure_add {f g : ℝ≥0 → ℕ} (hf : Monotone f) (hrcf : IsRightContinuous f)
    (hg : Monotone g) (hrcg : IsRightContinuous g) :
    countPathMeasure (f + g) = countPathMeasure f + countPathMeasure g := by
  have hadd : Monotone (f + g) := hf.add hg
  have hrc : IsRightContinuous (f + g) := fun t ↦ by
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    filter_upwards
      [tendsto_pure.1 (by simpa only [ContinuousWithinAt, nhds_discrete] using hrcf t),
       tendsto_pure.1 (by simpa only [ContinuousWithinAt, nhds_discrete] using hrcg t)]
      with s hfs hgs
    simp [hfs, hgs]
  refine Measure.ext_of_Iic' _ _ (fun t ↦ ?_) fun t ↦ ?_
  · rw [countPathMeasure_Iic hadd hrc t]
    exact ENNReal.natCast_ne_top _
  · simp [countPathMeasure_Iic hadd hrc t, countPathMeasure_Iic hf hrcf t,
      countPathMeasure_Iic hg hrcg t]

/-- On a monotone right-continuous path, the atom at the origin equals the initial count `f 0`. -/
@[simp]
theorem countPathMeasure_singleton_zero {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) :
    countPathMeasure f {0} = f 0 := by
  have hIic : Iic (0 : ℝ≥0) = {0} := by ext; simp
  rw [← hIic, countPathMeasure_Iic hf hrc]

/-- On a monotone right-continuous path, `countPathMeasure f` assigns mass `f t - f s` to
`(s, t]` for all `s, t : ℝ≥0`. -/
@[simp]
theorem countPathMeasure_Ioc {f : ℝ≥0 → ℕ} (hf : Monotone f) (hrc : IsRightContinuous f)
    (s t : ℝ≥0) :
    countPathMeasure f (Ioc s t) = ((f t - f s : ℕ) : ℝ≥0∞) :=
  Measure.measure_Ioc_eq_natCast_sub (countPathMeasure_Iic hf hrc s) (countPathMeasure_Iic hf hrc t)

/-- At any positive time `t > 0`, the point measure of a monotone right-continuous path has
multiplicity at most one if and only if some strictly earlier time `s < t` satisfies
`f t ≤ f s + 1`. -/
theorem countPathMeasure_singleton_le_one_iff {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) {t : ℝ≥0} (ht : 0 < t) :
    countPathMeasure f {t} ≤ 1 ↔ ∃ s < t, f t ≤ f s + 1 := by
  refine ⟨fun hle ↦ ?_, fun ⟨s, hst, hs⟩ ↦ ?_⟩
  · obtain ⟨u, hu_mono, hu_mem, hu_lim⟩ := exists_seq_strictMono_tendsto' ht
    have hu_lt (n : ℕ) : u n < t := (hu_mem n).2
    have hInter : (⋂ n : ℕ, Ioc (u n) t) = {t} := by
      ext x
      simp only [mem_iInter, mem_Ioc, mem_singleton_iff]
      refine ⟨fun hx ↦ le_antisymm (hx 0).2 ?_, fun hxt n ↦ ⟨hxt ▸ hu_lt n, hxt.le⟩⟩
      exact le_of_tendsto hu_lim (Eventually.of_forall fun n ↦ (hx n).1.le)
    have htend : Tendsto (fun n ↦ countPathMeasure f (Ioc (u n) t))
        atTop (𝓝 (countPathMeasure f {t})) := by
      rw [← hInter]
      refine tendsto_measure_iInter_atTop (fun _ ↦ measurableSet_Ioc.nullMeasurableSet)
        (fun m n hmn ↦ Ioc_subset_Ioc_left (hu_mono.monotone hmn)) ⟨0, ?_⟩
      rw [countPathMeasure_Ioc hf hrc]
      exact ENNReal.natCast_ne_top _
    have hlt2 : countPathMeasure f {t} < 2 :=
      hle.trans_lt (by norm_num)
    obtain ⟨n, hn⟩ := (htend.eventually (isOpen_Iio.mem_nhds hlt2)).exists
    have hn' : countPathMeasure f (Ioc (u n) t) < 2 := hn
    rw [countPathMeasure_Ioc hf hrc] at hn'
    have hn'' : f t - f (u n) < 2 := by exact_mod_cast hn'
    exact ⟨u n, hu_lt n, by omega⟩
  · calc
      countPathMeasure f {t} ≤ countPathMeasure f (Ioc s t) :=
        measure_mono (singleton_subset_iff.2 ⟨hst, le_rfl⟩)
      _ = ((f t - f s : ℕ) : ℝ≥0∞) := countPathMeasure_Ioc hf hrc s t
      _ ≤ 1 := by
        have : f t - f s ≤ 1 := by omega
        exact_mod_cast this

/-- A monotone right-continuous path produces a simple point measure on `ℝ≥0` if and only if
`f 0 ≤ 1` and no positive time has a left-hand jump of size two or more. -/
theorem forall_countPathMeasure_singleton_le_one_iff {f : ℝ≥0 → ℕ} (hf : Monotone f)
    (hrc : IsRightContinuous f) :
    (∀ t, countPathMeasure f {t} ≤ 1) ↔ f 0 ≤ 1 ∧ ∀ t > 0, ∃ s < t, f t ≤ f s + 1 := by
  refine ⟨fun h ↦ ⟨?_, fun t ht ↦ (countPathMeasure_singleton_le_one_iff hf hrc ht).1 (h t)⟩,
    fun ⟨h0, hpos⟩ t ↦ ?_⟩
  · have h0 := h 0
    rw [countPathMeasure_singleton_zero hf hrc] at h0
    exact_mod_cast h0
  · rcases eq_or_lt_of_le (zero_le (a := t)) with rfl | ht
    · rw [countPathMeasure_singleton_zero hf hrc]
      exact_mod_cast h0
    · exact (countPathMeasure_singleton_le_one_iff hf hrc ht).2 (hpos t ht)

/-- Any measure on `ℝ≥0` whose cumulative masses agree with a natural-valued path `f` equals
`countPathMeasure f`. Local finiteness and integrality of `μ`, as well as monotonicity and
right-continuity of `f`, follow rather than being assumed. -/
theorem eq_countPathMeasure_of_measure_Iic_eq {μ : Measure ℝ≥0} {f : ℝ≥0 → ℕ}
    (hμ : ∀ t, μ (Iic t) = f t) :
    μ = countPathMeasure f := by
  have : IsLocallyFiniteMeasure μ := μ.isLocallyFiniteMeasure_of_measure_Iic_lt_top fun t ↦ by
    rw [hμ t]; exact ENNReal.natCast_lt_top _
  have hf_eq : f = fun t ↦ ⌊(μ (Iic t)).toNNReal⌋₊ := funext fun t ↦ by simp [hμ t]
  have hf : Monotone f := hf_eq ▸ μ.monotone_natFloor_Iic
  have hrc : IsRightContinuous f := hf_eq ▸ μ.isRightContinuous_natFloor_Iic
  refine Measure.ext_of_Iic' μ (countPathMeasure f)
    (fun t ↦ by rw [hμ t]; exact ENNReal.natCast_ne_top _) fun t ↦ ?_
  rw [hμ t, countPathMeasure_Iic hf hrc t]

/-- Any measure on `ℝ≥0` whose cumulative masses agree with a natural-valued path `f` has
occurrence times equal to `countJumpTime f`. -/
theorem occurrenceTime_eq_countJumpTime_of_measure_Iic_eq {μ : Measure ℝ≥0} {f : ℝ≥0 → ℕ}
    (hμ : ∀ t, μ (Iic t) = f t) :
    μ.occurrenceTime = countJumpTime f := by
  rw [eq_countPathMeasure_of_measure_Iic_eq hμ, occurrenceTime_countPathMeasure]

/-- If the sample paths of `N` are monotone and right-continuous on one event of full measure, then
the reconstructed measure `countPathMeasure (N · ω)` has cumulative mass `N t ω` on `[0, t]`
simultaneously at all times almost surely. -/
theorem ae_countPathMeasure_Iic_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : ℝ≥0 → Ω → ℕ} (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    ∀ᵐ ω ∂P, ∀ t, countPathMeasure (N · ω) (Iic t) = N t ω :=
  hreg.mono fun _ ⟨hf, hrc⟩ t ↦ countPathMeasure_Iic hf hrc t

end TauCeti.Probability

open TauCeti.Probability

namespace MeasureTheory.Measure

/-! ### Reconstructing measures from cumulative count floors -/

variable {μ : Measure ℝ≥0}

/-- Reconstructing a temporal measure from its cumulative natural-valued counts on `[0, t]`
recovers any locally finite integer-valued measure, including any atom at zero. -/
@[simp]
theorem IsIntegerValued.countPathMeasure_natFloor_Iic [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) :
    countPathMeasure (fun t ↦ ⌊(μ (Iic t)).toNNReal⌋₊) = μ :=
  (eq_countPathMeasure_of_measure_Iic_eq fun t ↦ (hμ.natCast_natFloor_Iic t).symm).symm

/-- Jump times of the cumulative natural-valued counts on `[0, t]` agree with `μ.occurrenceTime`
for any locally finite integer-valued measure. -/
@[simp]
theorem IsIntegerValued.countJumpTime_natFloor_Iic [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) :
    countJumpTime (fun t ↦ ⌊(μ (Iic t)).toNNReal⌋₊) = μ.occurrenceTime :=
  (occurrenceTime_eq_countJumpTime_of_measure_Iic_eq
    fun t ↦ (hμ.natCast_natFloor_Iic t).symm).symm

/-- Reconstructing a temporal measure from its natural-valued counts on `(a, t]` retains the
restriction to `(a, ∞)`. -/
@[simp]
theorem IsIntegerValued.countPathMeasure_natFloor_Ioc [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) (a : ℝ≥0) :
    countPathMeasure (fun t ↦ ⌊(μ (Ioc a t)).toNNReal⌋₊) = μ.restrict (Ioi a) := by
  simpa only [μ.restrict_Ioi_apply_Iic a] using
    (hμ.restrict (A := Ioi a)).countPathMeasure_natFloor_Iic

/-- When a locally finite integer-valued measure has no mass at zero, reconstructing from the
counts on `(0, t]` recovers the entire measure. -/
theorem IsIntegerValued.countPathMeasure_natFloor_Ioc_of_singleton_zero [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) (h0 : μ {0} = 0) :
    countPathMeasure (fun t ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊) = μ := by
  rw [hμ.countPathMeasure_natFloor_Ioc 0]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hcompl : {a : ℝ≥0 | a ∉ Ioi 0} = {0} := by ext x; simp
  rwa [ae_iff, hcompl]

end MeasureTheory.Measure

namespace TauCeti.Probability

/-! ### Equivalence of count-path laws and random-measure laws -/

section LawEquivalence

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'}

private theorem identDistrib_congr {α : Type*} [MeasurableSpace α]
    {f f' : Ω → α} {g g' : Ω' → α} (h : IdentDistrib f g P Q)
    (hf : f =ᵐ[P] f') (hg : g =ᵐ[Q] g') : IdentDistrib f' g' P Q :=
  (IdentDistrib.of_ae_eq h.aemeasurable_fst hf).symm.trans
    (h.trans (IdentDistrib.of_ae_eq h.aemeasurable_snd hg))

private theorem natFloor_Iic_countPathMeasure_ae_eq {N : ℝ≥0 → Ω → ℕ}
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    (fun ω t ↦ ⌊(countPathMeasure (N · ω) (Iic t)).toNNReal⌋₊) =ᵐ[P] fun ω t ↦ N t ω := by
  filter_upwards [hreg] with ω ⟨hf, hrc⟩
  exact natFloor_countPathMeasure_Iic hf hrc

private theorem countPathMeasure_natFloor_Iic_ae_eq {M : Ω → Measure ℝ≥0}
    (hreg : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω) ∧ (M ω).IsIntegerValued) :
    (fun ω ↦ countPathMeasure (fun t ↦ ⌊(M ω (Iic t)).toNNReal⌋₊)) =ᵐ[P] M := by
  filter_upwards [hreg] with ω ⟨_, hint⟩
  exact hint.countPathMeasure_natFloor_Iic

/-- For natural-valued processes whose paths are monotone and right-continuous on one event of
full measure, equality in law of the reconstructed random measures is equivalent to equality in
law of the processes on `ℝ≥0 → ℕ`. -/
theorem identDistrib_countPathMeasure_iff {N : ℝ≥0 → Ω → ℕ} {N' : ℝ≥0 → Ω' → ℕ}
    (hreg : ∀ᵐ ω ∂P, Monotone (N · ω) ∧ IsRightContinuous (N · ω))
    (hreg' : ∀ᵐ ω ∂Q, Monotone (N' · ω) ∧ IsRightContinuous (N' · ω)) :
    IdentDistrib (fun ω ↦ countPathMeasure (N · ω)) (fun ω ↦ countPathMeasure (N' · ω)) P Q ↔
      IdentDistrib (fun ω t ↦ N t ω) (fun ω t ↦ N' t ω) P Q :=
  ⟨fun h ↦ identDistrib_congr (h.comp measurable_natFloor_measure_Iic)
    (natFloor_Iic_countPathMeasure_ae_eq hreg) (natFloor_Iic_countPathMeasure_ae_eq hreg'),
  fun h ↦ h.comp measurable_countPathMeasure⟩

/-- For almost surely locally finite integer-valued random measures on `ℝ≥0`, equality in law is
equivalent to equality in law of their natural-valued cumulative count processes on `[0, t]`. -/
theorem identDistrib_measure_iff_natFloor_Iic {M : Ω → Measure ℝ≥0} {M' : Ω' → Measure ℝ≥0}
    (hreg : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω) ∧ (M ω).IsIntegerValued)
    (hreg' : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (M' ω) ∧ (M' ω).IsIntegerValued) :
    IdentDistrib M M' P Q ↔
      IdentDistrib (fun ω t ↦ ⌊(M ω (Iic t)).toNNReal⌋₊)
        (fun ω t ↦ ⌊(M' ω (Iic t)).toNNReal⌋₊) P Q :=
  ⟨fun h ↦ h.comp measurable_natFloor_measure_Iic,
  fun h ↦ identDistrib_congr (h.comp measurable_countPathMeasure)
    (countPathMeasure_natFloor_Iic_ae_eq hreg) (countPathMeasure_natFloor_Iic_ae_eq hreg')⟩

/-- Direct law comparison between an almost surely locally finite integer-valued random measure
`M` and the measure reconstructed from an almost surely monotone right-continuous count process
`N`. -/
theorem identDistrib_measure_countPathMeasure_iff {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω' → ℕ}
    (hregM : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω) ∧ (M ω).IsIntegerValued)
    (hregN : ∀ᵐ ω ∂Q, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IdentDistrib M (fun ω ↦ countPathMeasure (N · ω)) P Q ↔
      IdentDistrib (fun ω t ↦ ⌊(M ω (Iic t)).toNNReal⌋₊) (fun ω t ↦ N t ω) P Q :=
  ⟨fun h ↦ identDistrib_congr (h.comp measurable_natFloor_measure_Iic)
    .rfl (natFloor_Iic_countPathMeasure_ae_eq hregN),
  fun h ↦ identDistrib_congr (h.comp measurable_countPathMeasure)
    (countPathMeasure_natFloor_Iic_ae_eq hregM) .rfl⟩

/-- When `M` almost surely has no mass at the origin, comparing `M` in law with
`countPathMeasure (N · ω)` is also equivalent to comparing the counts of `M` on `(0, t]` with
`N`. -/
theorem identDistrib_measure_countPathMeasure_iff_natFloor_Ioc
    {M : Ω → Measure ℝ≥0} {N : ℝ≥0 → Ω' → ℕ}
    (hregM : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω) ∧ (M ω).IsIntegerValued)
    (h0M : ∀ᵐ ω ∂P, M ω {0} = 0)
    (hregN : ∀ᵐ ω ∂Q, Monotone (N · ω) ∧ IsRightContinuous (N · ω)) :
    IdentDistrib M (fun ω ↦ countPathMeasure (N · ω)) P Q ↔
      IdentDistrib (fun ω t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊) (fun ω t ↦ N t ω) P Q := by
  have heqM : (fun ω t ↦ ⌊(M ω (Iic t)).toNNReal⌋₊) =ᵐ[P]
      fun ω t ↦ ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ := by
    filter_upwards [h0M] with ω h0
    funext t
    have hIcc : Icc (0 : ℝ≥0) t = Iic t := by ext; simp
    rw [measure_congr (Ioc_ae_eq_Icc' h0), hIcc]
  rw [identDistrib_measure_countPathMeasure_iff hregM hregN]
  exact ⟨fun h ↦ identDistrib_congr h heqM .rfl, fun h ↦ identDistrib_congr h heqM.symm .rfl⟩

end LawEquivalence

end TauCeti.Probability
