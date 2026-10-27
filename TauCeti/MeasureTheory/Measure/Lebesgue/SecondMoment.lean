/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Centered intervals minimize second moments

Among Lebesgue-measurable subsets of the real line of a prescribed finite length, the
centered interval uniquely minimizes the second moment, up to null sets. Adding a constant
to the quadratic weight gives the same comparison; this is useful on orthogonal line
sections of a Euclidean set. A finite second moment forces finite volume in any
finite-dimensional real inner product space, so it needs no additional volume hypothesis.

The comparison subtracts the constant value of the weight at the interval endpoints.
The resulting weight is negative inside the interval and positive outside, so its
indicator on the interval is pointwise minimal. Equality detects membership away from
the two endpoints, which have zero Lebesgue measure.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- A finite second moment forces finite volume: the part outside the unit ball is bounded
by its moment, and the unit ball has finite volume. -/
theorem volume_ne_top_of_lintegral_norm_sq_ne_top {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hmoment : (∫⁻ x in s, ENNReal.ofReal (‖x‖ ^ 2)) ≠ ∞) :
    volume s ≠ ∞ := by
  have hmeas : Measurable (fun x : E ↦ ENNReal.ofReal (‖x‖ ^ 2)) := by fun_prop
  have htail := meas_ge_le_lintegral_div (μ := volume.restrict s) hmeas.aemeasurable
    (ε := 1) one_ne_zero ENNReal.one_ne_top
  rw [Measure.restrict_apply (measurableSet_le measurable_const hmeas), div_one,
    inter_comm] at htail
  have hsub : s ⊆ Metric.closedBall (0 : E) 1 ∪
      (s ∩ {x : E | 1 ≤ ENNReal.ofReal (‖x‖ ^ 2)}) := by
    intro x hx
    by_cases h : ‖x‖ ≤ 1
    · exact Or.inl (by simpa using h)
    · refine Or.inr ⟨hx, ?_⟩
      have hsq : 1 ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      simpa using ENNReal.ofReal_le_ofReal hsq
  exact ((measure_mono hsub).trans_lt ((measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨Metric.isBounded_closedBall.measure_lt_top,
      lt_of_le_of_lt htail (lt_top_iff_ne_top.mpr hmoment)⟩))).ne

/-- A centered interval minimizes any quadratic weight `a + t²` among sets of the same
length and finite second moment. Equality occurs precisely for the same set up to null sets. -/
private theorem integral_closedBall_add_sq_le_and_eq_iff {s : Set ℝ}
    (hs : NullMeasurableSet s volume)
    (r : ℝ) (hr : 0 ≤ r) (hmass : volume s = volume (Metric.closedBall (0 : ℝ) r))
    (a : ℝ) (hint : IntegrableOn (fun t : ℝ ↦ a + t ^ 2) s volume) :
    (∫ t in Metric.closedBall (0 : ℝ) r, a + t ^ 2) ≤ (∫ t in s, a + t ^ 2) ∧
      ((∫ t in Metric.closedBall (0 : ℝ) r, a + t ^ 2) = (∫ t in s, a + t ^ 2) ↔
        s =ᵐ[volume] Metric.closedBall (0 : ℝ) r) := by
  let I := Metric.closedBall (0 : ℝ) r
  have hI : MeasurableSet I := Metric.isClosed_closedBall.measurableSet
  have hfin : volume s ≠ ∞ := by rw [hmass]; exact Metric.isBounded_closedBall.measure_lt_top.ne
  have hfinI : volume I ≠ ∞ := Metric.isBounded_closedBall.measure_lt_top.ne
  have hi : IntegrableOn (fun t : ℝ ↦ a + t ^ 2) I volume :=
    (continuous_const.add (continuous_id.pow 2)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℝ) r)
  -- Subtract the endpoint weight: the interval is exactly its nonpositive sublevel set.
  have hsi : Integrable (s.indicator (fun t : ℝ ↦ (a + t ^ 2) - (a + r ^ 2))) volume := by
    convert (hint.sub (integrableOn_const hfin (C := a + r ^ 2))).integrable_indicator₀ hs using 1
  have hii : Integrable (I.indicator (fun t : ℝ ↦ (a + t ^ 2) - (a + r ^ 2))) volume := by
    convert (hi.sub (integrableOn_const hfinI (C := a + r ^ 2))).integrable_indicator hI using 1
  have hle : I.indicator (fun t : ℝ ↦ (a + t ^ 2) - (a + r ^ 2)) ≤
      s.indicator (fun t : ℝ ↦ (a + t ^ 2) - (a + r ^ 2)) := by
    have hsub : {t : ℝ | (a + t ^ 2) - (a + r ^ 2) ≤ 0} = I := by
      ext t
      simp only [mem_ofPred_eq, I, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      constructor <;> intro h <;> nlinarith [sq_abs t, abs_nonneg t]
    rw [← hsub]
    exact indicator_nonpos_le_indicator s _
  have heval (u : Set ℝ) (hu : NullMeasurableSet u volume)
      (hf : IntegrableOn (fun t : ℝ ↦ a + t ^ 2) u volume) (hfu : volume u ≠ ∞) :
      (∫ t, u.indicator (fun t : ℝ ↦ (a + t ^ 2) - (a + r ^ 2)) t) =
        (∫ t in u, a + t ^ 2) - volume.real u * (a + r ^ 2) := by
    rw [integral_indicator₀ hu, integral_sub hf (integrableOn_const hfu), setIntegral_const,
      smul_eq_mul]
  have hmassR : volume.real s = volume.real I := congrArg ENNReal.toReal hmass
  have hineq := integral_mono hii hsi hle
  rw [heval I hI.nullMeasurableSet hi hfinI, heval s hs hint hfin, hmassR] at hineq
  refine ⟨by linarith, ⟨fun heq ↦ ?_, fun heq ↦ setIntegral_congr_set heq.symm⟩⟩
  -- Equality of integrals forces equality of shifted indicators away from the null endpoints.
  have hweights : I.indicator (fun t : ℝ ↦ (a + t ^ 2) - (a + r ^ 2)) =ᵐ[volume]
      s.indicator (fun t : ℝ ↦ (a + t ^ 2) - (a + r ^ 2)) := by
    apply (integral_eq_iff_of_ae_le hii hsi (Filter.Eventually.of_forall hle)).mp
    rw [heval I hI.nullMeasurableSet hi hfinI, heval s hs hint hfin, hmassR, heq]
  filter_upwards [hweights, volume.ae_ne r, volume.ae_ne (-r)] with t ht htr htnr
  dsimp only [I] at ht
  have hne : (a + t ^ 2) - (a + r ^ 2) ≠ 0 := by
    intro hz
    have : t = r ∨ t = -r := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      linarith
    exact this.elim htr htnr
  apply propext
  constructor
  · intro hts
    by_contra hti
    simp only [indicator_of_mem hts, indicator_of_notMem hti] at ht
    exact hne ht.symm
  · intro hti
    by_contra hts
    simp only [indicator_of_mem hti, indicator_of_notMem hts] at ht
    exact hne ht

private theorem lintegral_eball_add_sq_le_and_eq_iff {s : Set ℝ}
    (hs : NullMeasurableSet s volume) (a : ℝ) (ha : 0 ≤ a)
    (hmoment : (∫⁻ t in s, ENNReal.ofReal (a + t ^ 2)) ≠ ∞) :
    (∫⁻ t in Metric.eball (0 : ℝ) (volume s / 2), ENNReal.ofReal (a + t ^ 2)) ≤
      (∫⁻ t in s, ENNReal.ofReal (a + t ^ 2)) ∧
      ((∫⁻ t in Metric.eball (0 : ℝ) (volume s / 2), ENNReal.ofReal (a + t ^ 2)) =
        (∫⁻ t in s, ENNReal.ofReal (a + t ^ 2)) ↔
          s =ᵐ[volume] Metric.eball (0 : ℝ) (volume s / 2)) := by
  have hfin : volume s ≠ ∞ := by
    apply volume_ne_top_of_lintegral_norm_sq_ne_top
    apply ne_top_of_le_ne_top hmoment
    apply lintegral_mono
    intro t
    apply ENNReal.ofReal_le_ofReal
    simp only [Real.norm_eq_abs, sq_abs]
    linarith
  let r := (volume s / 2).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hrad : volume s / 2 ≠ ∞ := ENNReal.div_ne_top hfin (by norm_num)
  have hball : Metric.eball (0 : ℝ) (volume s / 2) = Metric.ball (0 : ℝ) r := by
    rw [← ENNReal.ofReal_toReal hrad, Metric.eball_ofReal]
  have hae : Metric.eball (0 : ℝ) (volume s / 2) =ᵐ[volume] Metric.closedBall (0 : ℝ) r := by
    rw [hball, Real.ball_eq_Ioo, Real.closedBall_eq_Icc]
    exact Ioo_ae_eq_Icc
  have hmass : volume s = volume (Metric.closedBall (0 : ℝ) r) := by
    rw [← measure_congr hae, Real.volume_eball]
    exact (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
  have hint : IntegrableOn (fun t : ℝ ↦ a + t ^ 2) s volume :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((continuous_const.add (continuous_id.pow 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t ↦ add_nonneg ha (sq_nonneg t))).mp hmoment
  have hi : IntegrableOn (fun t : ℝ ↦ a + t ^ 2) (Metric.closedBall (0 : ℝ) r) volume :=
    (continuous_const.add (continuous_id.pow 2)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℝ) r)
  have hcmp := integral_closedBall_add_sq_le_and_eq_iff hs r hr hmass a hint
  have hnonneg (u : Set ℝ) : 0 ≤ᵐ[volume.restrict u] (fun t : ℝ ↦ a + t ^ 2) :=
    Filter.Eventually.of_forall fun t ↦ add_nonneg ha (sq_nonneg t)
  rw [setLIntegral_congr hae, ← ofReal_integral_eq_lintegral_ofReal hi (hnonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hint (hnonneg _)]
  refine ⟨ENNReal.ofReal_le_ofReal hcmp.1, ?_⟩
  rw [ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae (hnonneg _))
    (integral_nonneg_of_ae (hnonneg _)), hcmp.2]
  exact ⟨fun h ↦ h.trans hae.symm, fun h ↦ h.trans hae⟩

/-- Centering a Lebesgue-measurable subset of the real line decreases its nonnegative
quadratic moment, allowing infinite length and an infinite moment. -/
theorem lintegral_eball_add_sq_le {s : Set ℝ} (hs : NullMeasurableSet s volume)
    (a : ℝ) (ha : 0 ≤ a) :
    (∫⁻ t in Metric.eball (0 : ℝ) (volume s / 2), ENNReal.ofReal (a + t ^ 2)) ≤
      (∫⁻ t in s, ENNReal.ofReal (a + t ^ 2)) := by
  by_cases hmoment : (∫⁻ t in s, ENNReal.ofReal (a + t ^ 2)) = ∞
  · rw [hmoment]
    exact le_top
  · exact (lintegral_eball_add_sq_le_and_eq_iff hs a ha hmoment).1

/-- Equality in the centered-interval quadratic-moment comparison characterizes the centered
interval up to Lebesgue-null sets. -/
theorem lintegral_eball_add_sq_eq_iff {s : Set ℝ} (hs : NullMeasurableSet s volume)
    (a : ℝ) (ha : 0 ≤ a)
    (hmoment : (∫⁻ t in s, ENNReal.ofReal (a + t ^ 2)) ≠ ∞) :
    (∫⁻ t in Metric.eball (0 : ℝ) (volume s / 2), ENNReal.ofReal (a + t ^ 2)) =
      (∫⁻ t in s, ENNReal.ofReal (a + t ^ 2)) ↔
        s =ᵐ[volume] Metric.eball (0 : ℝ) (volume s / 2) :=
  (lintegral_eball_add_sq_le_and_eq_iff hs a ha hmoment).2

end TauCeti
