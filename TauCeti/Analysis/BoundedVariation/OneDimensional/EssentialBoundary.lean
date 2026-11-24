/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.Analysis.BoundedVariation.Hyperplane
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Perimeter on the line is bounded by the number of essential boundary points

For a null-measurable set `s ⊆ ℝ` and an open set `Ω ⊆ ℝ`, the perimeter of `s` in `Ω` is at most
the number of points of the essential boundary `∂ᵉs` lying in `Ω`:

`P(s; Ω) ≤ #(∂ᵉs ∩ Ω)`

(`TauCeti.Real.perimeter_le_encard_essentialBoundary_inter`), as an inequality in `ℝ≥0∞`. In
particular `P(s; Ω) ≤ #(frontier s ∩ Ω)`
(`TauCeti.Real.perimeter_le_encard_frontier_inter`). This is the one-dimensional case of the
converse finite-perimeter criterion: a set whose essential boundary is locally finite has locally
finite perimeter. No finiteness of the perimeter is assumed.

## Proof

The core lemma is that on an open interval `(a, b)` without essential boundary points the set is
almost everywhere empty or almost everywhere full
(`TauCeti.Real.measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero`). Let
`F y = ∫_a^y 1_s`. At a point of density zero, `|F (x + h) - F x| ≤ |s ∩ [x - |h|, x + |h|]|`
is `o(h)`, so `F' x = 0`; at a point of density one the same argument for the complement gives
`F' x = 1`. So the derivative of `F` takes only the values `0` and `1` on `(a, b)`, and by the mean
value theorem so does the slope `|s ∩ (a, b]| / (b - a)`.

For the bound, an infinite `∂ᵉs ∩ Ω` is trivial. Otherwise every `x ∈ Ω` has a ball
`B(x, ε) ⊆ Ω` meeting `∂ᵉs` at most in `x`. On each half of the ball the core lemma applies, so in
the ball `s` is almost everywhere `∅`, everything, or a half-line ending at `x`, and its perimeter
there is `0`, or at most `1` (`TauCeti.Real.perimeter_Iio_le_one`), and is `0` when
`x ∉ ∂ᵉs`. Countable subadditivity of the perimeter over the cover of `Ω` by these balls
(`TauCeti.totalVariationOn_iSup_le_tsum`) sums these bounds to `#(∂ᵉs ∩ Ω)`.

## Main results

* `TauCeti.Real.hasDerivAt_integral_indicator_of_hasDensityAt_zero` and
  `TauCeti.Real.hasDerivAt_integral_indicator_of_hasDensityAt_one`: the primitive of `1_s` is
  differentiable at points of density zero and one, with derivative the density.
* `TauCeti.Real.measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero`: on an interval without
  essential boundary points a measurable set is null or conull.
* `TauCeti.Real.perimeter_ball_le_one` and `TauCeti.Real.perimeter_ball_eq_zero`: the perimeter in a
  ball meeting `∂ᵉs` at most in its centre, or not at all.
* `TauCeti.Real.perimeter_le_encard_essentialBoundary_inter`: `P(s; Ω) ≤ #(∂ᵉs ∩ Ω)`.
* `TauCeti.Real.perimeter_le_encard_frontier_inter`: `P(s; Ω) ≤ #(frontier s ∩ Ω)`.
-/

public section

open Filter Set MeasureTheory Metric TopologicalSpace Asymptotics
open scoped Topology ENNReal Interval Set.Notation RealInnerProductSpace

namespace TauCeti.Real

variable {s : Set ℝ} {x : ℝ}

/-- Closed balls of positive radius in `ℝ` have positive finite Lebesgue measure. -/
private theorem eventually_volume_closedBall_ne_zero_ne_top (x : ℝ) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), volume (closedBall x r) ≠ 0 ∧ volume (closedBall x r) ≠ ∞ := by
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp [Real.volume_closedBall, hr, ENNReal.mul_eq_top]

/-- The indicator of a measurable set is integrable on every interval. -/
private theorem intervalIntegrable_indicator_one (hs : MeasurableSet s) (a b : ℝ) :
    IntervalIntegrable (s.indicator (1 : ℝ → ℝ)) volume a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    ((measurable_const.indicator hs).aestronglyMeasurable)
    (Eventually.of_forall fun y => by
      by_cases hy : y ∈ s <;> simp [hy])

/-- The integral of `1_s` over `(a, b]` is the measure of `s ∩ (a, b]`. -/
private theorem integral_indicator_one_eq (hs : MeasurableSet s) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, s.indicator (1 : ℝ → ℝ) t = volume.real (s ∩ Ioc a b) := by
  rw [intervalIntegral.integral_of_le hab, integral_indicator_one hs, measureReal_restrict_apply hs]

/-- The primitive of `1_s` only depends on `s` up to a null set. -/
private theorem integral_indicator_congr {t : Set ℝ} (hst : s =ᵐ[volume] t) (a y : ℝ) :
    ∫ z in a..y, s.indicator (1 : ℝ → ℝ) z = ∫ z in a..y, t.indicator (1 : ℝ → ℝ) z :=
  intervalIntegral.integral_congr_ae <| by
    filter_upwards [indicator_ae_eq_of_ae_eq_set (f := (1 : ℝ → ℝ)) hst] with z hz _
    exact hz

/-- `TauCeti.Real.hasDerivAt_integral_indicator_of_hasDensityAt_zero` for a measurable set. -/
private theorem hasDerivAt_integral_indicator_of_hasDensityAt_zero_aux (hs : MeasurableSet s)
    (a : ℝ)
    (h : HasDensityAt volume s x 0) :
    HasDerivAt (fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t) 0 x := by
  have hint := intervalIntegrable_indicator_one hs
  rw [hasDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  -- The proportion of `s` in small closed balls around `x` is below `c / 2`.
  have hev := (hasDensityAt_iff.1 h).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hc)))
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  rw [smul_zero, sub_zero, intervalIntegral.integral_interval_sub_left (hint a (x + h))
    (hint a x)]
  rcases eq_or_ne h 0 with rfl | h0
  · simp
  have hr : 0 < |h| := abs_pos.2 h0
  have hlt := hδP (y := |h|) (by simpa using hh) hr
  have hB : volume (closedBall x |h|) = ENNReal.ofReal (2 * |h|) := by
    rw [Real.volume_closedBall]
  -- So `|s ∩ B(x, |h|)| < c |h|`.
  have hm : volume (s ∩ closedBall x |h|) ≤ ENNReal.ofReal (c * |h|) := by
    rw [hB, ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul (by positivity)]
      at hlt
    refine hlt.le.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    ring
  have hsub : Ι x (x + h) ⊆ closedBall x |h| := by
    refine (uIoc_subset_uIcc.trans (uIcc_subset_Icc ?_ ?_)).trans Real.closedBall_eq_Icc.ge
    · constructor <;> linarith [abs_nonneg h]
    · constructor <;> linarith [neg_abs_le h, le_abs_self h]
  rw [intervalIntegral.norm_integral_eq_norm_integral_uIoc, integral_indicator_one hs,
    measureReal_restrict_apply hs, Real.norm_of_nonneg measureReal_nonneg, Real.norm_eq_abs]
  calc volume.real (s ∩ Ι x (x + h)) ≤ volume.real (s ∩ closedBall x |h|) :=
        measureReal_mono (inter_subset_inter_right _ hsub)
          (measure_ne_top_of_subset inter_subset_right
            (by simp [Real.volume_closedBall, ENNReal.mul_eq_top]))
    _ ≤ c * |h| := ENNReal.toReal_le_of_le_ofReal (by positivity) hm

/-- **The primitive of `1_s` at a point of density zero.** If a null-measurable set `s` has
density zero at `x`, then `y ↦ ∫_a^y 1_s` has derivative `0` at `x`. -/
theorem hasDerivAt_integral_indicator_of_hasDensityAt_zero (hs : NullMeasurableSet s) (a : ℝ)
    (h : HasDensityAt volume s x 0) :
    HasDerivAt (fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t) 0 x := by
  obtain ⟨t, -, ht, hts⟩ := hs.exists_measurable_superset_ae_eq
  simp_rw [integral_indicator_congr hts.symm a]
  exact hasDerivAt_integral_indicator_of_hasDensityAt_zero_aux ht a (h.congr_ae hts.symm)

/-- **The primitive of `1_s` at a point of density one.** If a null-measurable set `s` has
density one at `x`, then `y ↦ ∫_a^y 1_s` has derivative `1` at `x`. -/
theorem hasDerivAt_integral_indicator_of_hasDensityAt_one (hs : NullMeasurableSet s) (a : ℝ)
    (h : HasDensityAt volume s x 1) :
    HasDerivAt (fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t) 1 x := by
  obtain ⟨u, -, hu, hus⟩ := hs.exists_measurable_superset_ae_eq
  replace h := h.congr_ae hus.symm
  simp_rw [integral_indicator_congr hus.symm a]
  clear hs hus
  have h0 : HasDensityAt volume uᶜ x 0 :=
    (hasDensityAt_compl_zero_iff hu.nullMeasurableSet
      (eventually_volume_closedBall_ne_zero_ne_top x)).2 h
  have hc := hasDerivAt_integral_indicator_of_hasDensityAt_zero_aux hu.compl a h0
  -- `1_s = 1 - 1_{sᶜ}`, so the primitive of `1_s` is `y - a` minus that of `1_{sᶜ}`.
  have hfun : (fun y => ∫ t in a..y, u.indicator (1 : ℝ → ℝ) t) =
      fun y => (y - a) - ∫ t in a..y, uᶜ.indicator (1 : ℝ → ℝ) t := by
    funext y
    have hsum : ∀ t, u.indicator (1 : ℝ → ℝ) t = 1 - uᶜ.indicator 1 t := fun t => by
      by_cases ht : t ∈ u <;> simp [ht]
    simp_rw [hsum]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_indicator_one hu.compl a y)]
    simp
  rw [hfun]
  have h2 : HasDerivAt (fun y => (y - a) - ∫ t in a..y, uᶜ.indicator (1 : ℝ → ℝ) t) (1 - 0) x :=
    ((hasDerivAt_id' x).sub_const a).sub hc
  rwa [sub_zero] at h2

/-- `TauCeti.Real.measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero` for a measurable set. -/
private theorem measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero_aux (hs : MeasurableSet s)
    {a b : ℝ} (h : ∀ y ∈ Ioo a b, y ∉ essentialBoundary volume s) :
    volume (s ∩ Ioo a b) = 0 ∨ volume (Ioo a b \ s) = 0 := by
  rcases le_or_gt b a with hba | hab
  · simp [Ioo_eq_empty_of_le hba]
  classical
  let F := fun y => ∫ t in a..y, s.indicator (1 : ℝ → ℝ) t
  let g := fun y => if HasDensityAt volume s y 1 then (1 : ℝ) else 0
  have hderiv : ∀ y ∈ Ioo a b, HasDerivAt F (g y) y := by
    intro y hy
    have hy' := h y hy
    simp only [mem_essentialBoundary, mem_essentialInterior, mem_essentialExterior, not_and,
      not_not] at hy'
    by_cases h1 : HasDensityAt volume s y 1
    · simpa [g, h1] using
        hasDerivAt_integral_indicator_of_hasDensityAt_one hs.nullMeasurableSet a h1
    · simpa [g, h1] using
        hasDerivAt_integral_indicator_of_hasDensityAt_zero hs.nullMeasurableSet a (hy' h1)
  have hcont : ContinuousOn F (Icc a b) :=
    (intervalIntegral.continuous_primitive (intervalIntegrable_indicator_one hs) a).continuousOn
  obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope F g hab hcont hderiv
  have hFb : F b = volume.real (s ∩ Ioc a b) := integral_indicator_one_eq hs hab.le
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  have hfin : volume (s ∩ Ioc a b) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right (by simp)
  rw [hFb, hFa, sub_zero] at hc
  by_cases h1 : HasDensityAt volume s c 1
  · -- The slope is one, so `s` fills `(a, b]`.
    simp only [g, h1, ↓reduceIte] at hc
    have hreal : volume.real (s ∩ Ioc a b) = b - a := by
      field_simp at hc
      linarith
    right
    refine measure_mono_null (sdiff_subset_sdiff_left Ioo_subset_Ioc_self) ?_
    rw [← sdiff_self_inter, measure_sdiff inter_subset_left
      (measurableSet_Ioc.inter hs).nullMeasurableSet (by rw [inter_comm]; exact hfin),
      inter_comm, ← ofReal_measureReal hfin, hreal, Real.volume_Ioc, tsub_self]
  · -- The slope is zero, so `s` misses `(a, b]` up to a null set.
    simp only [g, h1, ↓reduceIte] at hc
    have hreal : volume.real (s ∩ Ioc a b) = 0 := by
      rcases div_eq_zero_iff.1 hc.symm with h' | h'
      · exact h'
      · exact absurd h' hba
    left
    refine measure_mono_null (inter_subset_inter_right _ Ioo_subset_Ioc_self) ?_
    rwa [measureReal_eq_zero_iff hfin] at hreal

/-- **A set without essential boundary points in an interval is null or conull there.** If no
point of `(a, b)` lies in the essential boundary of a null-measurable set `s ⊆ ℝ`, then
`s ∩ (a, b)` or `(a, b) \ s` is Lebesgue-null. -/
theorem measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero (hs : NullMeasurableSet s)
    {a b : ℝ} (h : ∀ y ∈ Ioo a b, y ∉ essentialBoundary volume s) :
    volume (s ∩ Ioo a b) = 0 ∨ volume (Ioo a b \ s) = 0 := by
  obtain ⟨u, -, hu, hus⟩ := hs.exists_measurable_superset_ae_eq
  rw [← essentialBoundary_congr_ae hus] at h
  have h1 : u ∩ Ioo a b =ᵐ[volume] s ∩ Ioo a b := eventuallyEqSet_iff.2 <| by
    filter_upwards [eventuallyEqSet_iff.1 hus] with y hy
    rw [mem_inter_iff, mem_inter_iff, hy]
  have h2 : Ioo a b \ u =ᵐ[volume] Ioo a b \ s := eventuallyEqSet_iff.2 <| by
    filter_upwards [eventuallyEqSet_iff.1 hus] with y hy
    rw [Set.mem_sdiff, Set.mem_sdiff, hy]
  rw [← measure_congr h1, ← measure_congr h2]
  exact measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero_aux hu h

/-- **A half-line ending at a point has perimeter at most one in every open set**: by
`TauCeti.perimeter_setOf_inner_lt` it is the number of times the open set contains the point. -/
theorem perimeter_Iio_le_one (x : ℝ) (Ω : Opens ℝ) : perimeter volume Ω (Iio x) ≤ 1 := by
  have h := perimeter_setOf_inner_lt (F := ℝ) (ν := 1) (by simp) x Ω
  have hlt : {y : ℝ | ⟪y, (1 : ℝ)⟫ < x} = Iio x := by ext y; simp
  have heq : {y : ℝ | ⟪y, (1 : ℝ)⟫ = x} = {x} := by ext y; simp
  rw [hlt, heq, Module.finrank_self, tsub_self, Measure.euclideanHausdorffMeasure_zero] at h
  rw [h, ← Measure.hausdorffMeasure_zero_singleton x]
  exact measure_mono inter_subset_right

/-- **A half-line starting at a point has perimeter at most one in every open set.** -/
theorem perimeter_Ioi_le_one (x : ℝ) (Ω : Opens ℝ) : perimeter volume Ω (Ioi x) ≤ 1 := by
  rw [← compl_Iic, perimeter_compl, perimeter_congr_ae (ae_restrict_of_ae Iio_ae_eq_Iic.symm)]
  exact perimeter_Iio_le_one x Ω

/-- **No essential boundary in a ball, no perimeter.** If no point of `B(x, ε)` lies in the
essential boundary of a null-measurable set `s ⊆ ℝ`, then `P(s; B(x, ε)) = 0`. -/
theorem perimeter_ball_eq_zero (hs : NullMeasurableSet s) {ε : ℝ}
    (h : ∀ y ∈ ball x ε, y ∉ essentialBoundary volume s) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s = 0 := by
  have hball : (⟨ball x ε, isOpen_ball⟩ : Opens ℝ) = ⟨Ioo (x - ε) (x + ε), isOpen_Ioo⟩ := by
    ext1; exact Real.ball_eq_Ioo x ε
  rw [Real.ball_eq_Ioo] at h
  rw [hball]
  rcases measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero hs h with h0 | h0
  · rw [perimeter_congr_ae (t := ∅), perimeter_empty]
    rw [Opens.coe_mk, ae_eq_empty, Measure.restrict_apply' measurableSet_Ioo]
    exact h0
  · rw [perimeter_congr_ae (t := univ), perimeter_univ]
    rw [Opens.coe_mk, ae_eq_univ, Measure.restrict_apply' measurableSet_Ioo, ← sdiff_eq_compl_inter]
    exact h0

/-- On a ball, `s` has the perimeter of any set `t` that agrees with it almost everywhere off the
centre. -/
private theorem perimeter_ball_congr {ε : ℝ} {t : Set ℝ}
    (ht : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ ball x ε → y ≠ x → (y ∈ s ↔ y ∈ t)) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s = perimeter volume ⟨ball x ε, isOpen_ball⟩ t := by
  have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ x := by
    simpa using (measure_eq_zero_iff_ae_notMem.1 (measure_singleton x))
  refine perimeter_congr_ae (eventuallyEqSet_iff.2 ?_)
  rw [Opens.coe_mk, ae_restrict_iff' measurableSet_ball]
  filter_upwards [ht, hne] with y hy hyx hyB
  exact hy hyB hyx

/-- **At most the centre on the essential boundary, perimeter at most one.** If no point of
`B(x, ε)` other than `x` lies in the essential boundary of a null-measurable set `s ⊆ ℝ`, then
`P(s; B(x, ε)) ≤ 1`: on the ball, `s` is almost everywhere `∅`, everything, or a half-line ending
at `x`. -/
theorem perimeter_ball_le_one (hs : NullMeasurableSet s) {ε : ℝ}
    (h : ∀ y ∈ ball x ε, y ∈ essentialBoundary volume s → y = x) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s ≤ 1 := by
  have hball : ∀ {y}, y ∈ ball x ε ↔ x - ε < y ∧ y < x + ε := by
    intro y; rw [Real.ball_eq_Ioo, mem_Ioo]
  have hL := measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero hs
    (a := x - ε) (b := x) fun y hy hyb =>
      hy.2.ne (h y (hball.2 ⟨hy.1, by linarith [hy.1, hy.2]⟩) hyb)
  have hR := measure_inter_Ioo_eq_zero_or_measure_Ioo_diff_eq_zero hs
    (a := x) (b := x + ε) fun y hy hyb =>
      hy.1.ne' (h y (hball.2 ⟨by linarith [hy.1, hy.2], hy.2⟩) hyb)
  simp only [measure_eq_zero_iff_ae_notMem, mem_inter_iff, Set.mem_sdiff, mem_Ioo, not_and,
    not_not] at hL hR
  rcases hL with hL | hL <;> rcases hR with hR | hR
  · rw [perimeter_ball_congr (t := ∅) ?_, perimeter_empty]
    · exact zero_le
    filter_upwards [hL, hR] with y hL hR hyB hyx
    simp only [mem_empty_iff_false, iff_false]
    intro hys
    rcases hyx.lt_or_gt with hlt | hgt
    · exact hL hys (hball.1 hyB).1 hlt
    · exact hR hys hgt (hball.1 hyB).2
  · rw [perimeter_ball_congr (t := Ioi x) ?_]
    · exact perimeter_Ioi_le_one x _
    filter_upwards [hL, hR] with y hL hR hyB hyx
    rcases hyx.lt_or_gt with hlt | hgt
    · exact iff_of_false (fun hys => hL hys (hball.1 hyB).1 hlt) (by simpa using hlt.le)
    · exact iff_of_true (hR ⟨hgt, (hball.1 hyB).2⟩) hgt
  · rw [perimeter_ball_congr (t := Iio x) ?_]
    · exact perimeter_Iio_le_one x _
    filter_upwards [hL, hR] with y hL hR hyB hyx
    rcases hyx.lt_or_gt with hlt | hgt
    · exact iff_of_true (hL ⟨(hball.1 hyB).1, hlt⟩) hlt
    · exact iff_of_false (fun hys => hR hys hgt (hball.1 hyB).2) (by simpa using hgt.le)
  · rw [perimeter_ball_congr (t := univ) ?_, perimeter_univ]
    · exact zero_le
    filter_upwards [hL, hR] with y hL hR hyB hyx
    simp only [mem_univ, iff_true]
    rcases hyx.lt_or_gt with hlt | hgt
    · exact hL ⟨(hball.1 hyB).1, hlt⟩
    · exact hR ⟨hgt, (hball.1 hyB).2⟩

/-- **The perimeter in a ball with at most its centre on the essential boundary.** If no point of
`B(x, ε)` other than `x` lies in `∂ᵉs`, then `P(s; B(x, ε))` is at most `1` if `x ∈ ∂ᵉs` and is
`0` otherwise. -/
theorem perimeter_ball_le_indicator (hs : NullMeasurableSet s) {ε : ℝ}
    (h : ∀ y ∈ ball x ε, y ∈ essentialBoundary volume s → y = x) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s ≤ (essentialBoundary volume s).indicator 1 x := by
  by_cases hx : x ∈ essentialBoundary volume s
  · rw [indicator_of_mem hx, Pi.one_apply]
    exact perimeter_ball_le_one hs h
  · rw [indicator_of_notMem hx, perimeter_ball_eq_zero hs fun y hy hyb => hx (h y hy hyb ▸ hyb)]

/-- **The perimeter on the line is at most the number of essential boundary points.** For a
null-measurable set `s ⊆ ℝ` and an open set `Ω`, `P(s; Ω) ≤ #(∂ᵉs ∩ Ω)` in `ℝ≥0∞`. In particular a
set whose essential boundary meets `Ω` in finitely many points has finite perimeter in `Ω`. -/
theorem perimeter_le_encard_essentialBoundary_inter (hs : NullMeasurableSet s) (Ω : Opens ℝ) :
    perimeter volume Ω s ≤ (essentialBoundary volume s ∩ Ω).encard := by
  set B := essentialBoundary volume s
  rcases (B ∩ Ω).finite_or_infinite with hfin | hinf
  swap
  · simp [Set.encard_eq_top hinf]
  -- Around each point of `Ω`, a ball inside `Ω` meeting `∂ᵉt` at most in its centre.
  have hball : ∀ x : (Ω : Set ℝ), ∃ ε > 0, ball (x : ℝ) ε ⊆ Ω ∧
      ∀ y ∈ ball (x : ℝ) ε, y ∈ B → y = x := by
    intro x
    have hcl : IsClosed ((B ∩ Ω) \ {(x : ℝ)}) := (hfin.sdiff).isClosed
    have hmem : ((B ∩ Ω) \ {(x : ℝ)})ᶜ ∩ Ω ∈ 𝓝 (x : ℝ) :=
      inter_mem (hcl.isOpen_compl.mem_nhds (by simp)) (Ω.isOpen.mem_nhds x.property)
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hmem
    refine ⟨ε, hε, fun y hy => (hεs hy).2, fun y hy hyB => ?_⟩
    have := (hεs hy).1
    simp only [mem_compl_iff, Set.mem_sdiff, mem_inter_iff, mem_singleton_iff, not_and,
      not_not] at this
    exact this ⟨hyB, (hεs hy).2⟩
  choose ε hε hεΩ hεB using hball
  let U : ↥(Ω : Set ℝ) → Opens ℝ := fun x => ⟨ball (x : ℝ) (ε x), isOpen_ball⟩
  have hU : (⨆ x, U x) = Ω := by
    refine le_antisymm (iSup_le fun x => hεΩ x) fun y hy => ?_
    exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, mem_ball_self (hε _)⟩
  calc perimeter volume Ω s = perimeter volume (⨆ x, U x) s := by rw [hU]
    _ ≤ ∑' x, perimeter volume (U x) s := by
        simp only [perimeter_def]
        exact totalVariationOn_iSup_le_tsum (locallyIntegrableOn_indicator_const
          (hs.mono Measure.restrict_le_self) (1 : ℝ))
    _ ≤ ∑' x : (Ω : Set ℝ), ((Ω : Set ℝ) ↓∩ (B ∩ Ω)).indicator 1 x := by
        refine tsum_le_tsum fun x => (perimeter_ball_le_indicator hs (hεB x)).trans (le_of_eq ?_)
        by_cases hx : (x : ℝ) ∈ B
        · rw [indicator_of_mem hx, indicator_of_mem (by exact ⟨hx, x.property⟩)]
          rfl
        · rw [indicator_of_notMem hx, indicator_of_notMem (by exact fun h => hx h.1)]
    _ = ((Ω : Set ℝ) ↓∩ (B ∩ Ω)).encard := by
        rw [← tsum_subtype]
        simp only [Pi.one_apply]
        exact ENNReal.tsum_set_one _
    _ ≤ (B ∩ Ω).encard := by
        exact_mod_cast encard_preimage_val_le_encard_right _ _

/-- **The perimeter on the line is at most the number of frontier points.** For a null-measurable
set `s ⊆ ℝ` and an open set `Ω`, `P(s; Ω) ≤ #(frontier s ∩ Ω)` in `ℝ≥0∞`. -/
theorem perimeter_le_encard_frontier_inter (hs : NullMeasurableSet s) (Ω : Opens ℝ) :
    perimeter volume Ω s ≤ (frontier s ∩ Ω).encard :=
  (perimeter_le_encard_essentialBoundary_inter hs Ω).trans <| by
    exact_mod_cast encard_le_encard (inter_subset_inter_left _ essentialBoundary_subset_frontier)

end TauCeti.Real
