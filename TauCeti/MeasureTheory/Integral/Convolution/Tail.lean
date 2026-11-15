/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Uniform tails of half-line convolutions

A measure whose masses on closed unit intervals are uniformly bounded integrates a
nonnegative antitone function against any reflected translate with a bound given by its
integer samples. The same estimate for the tail of the function gives uniform truncation
in the translation parameter when those samples have finite sum.

Closed intervals are used in the estimate, so atoms and either endpoint cause no problem.
This estimate is useful for passing from compactly supported forcing functions to integrable
monotone forcing functions in renewal convolutions.
-/

public section

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

/-- A uniform unit-interval mass bound controls the distant part of a reflected convolution
by the tail sum of the integer samples of its antitone integrand. No measurability of the
integrand is needed for this extended nonnegative integral estimate. -/
theorem lintegral_antitone_sub_tail_le (μ : Measure ℝ≥0) {C : ℝ≥0∞}
    (hμ : ∀ a, μ (Icc a (a + 1)) ≤ C) {h : ℝ≥0 → ℝ≥0∞} (hh : Antitone h)
    (N : ℕ) (t : ℝ≥0) :
    ∫⁻ s in Iic t ∩ {s | (N : ℝ≥0) ≤ t - s}, h (t - s) ∂μ ≤
      (∑' k : ℕ, h ((k + N : ℕ) : ℝ≥0)) * C := by
  classical
  -- Reflect the unit age intervals in the observation time, clipping them at zero.
  let J (k : ℕ) := Icc (t - ((k + N : ℕ) + 1)) (t - (k + N : ℕ))
  have hJ (k : ℕ) : μ (J k) ≤ C := by
    apply le_trans (measure_mono (Icc_subset_Icc le_rfl ?_)) (hμ (t - ((k + N : ℕ) + 1)))
    simpa using (tsub_le_tsub_add_tsub (a := t) (b := (k + N : ℕ) + 1)
      (c := (k + N : ℕ)))
  rw [← lintegral_indicator (measurableSet_Iic.inter (by measurability))]
  calc
    _ ≤ ∫⁻ s, ∑' k : ℕ, (J k).indicator (fun _ => h ((k + N : ℕ) : ℝ≥0)) s ∂μ := by
      apply lintegral_mono
      intro s
      by_cases hs : s ∈ Iic t ∩ {s | (N : ℝ≥0) ≤ t - s}
      · rw [indicator_of_mem hs]
        -- The integer part of the age selects one dominating term of the series.
        let n := ⌊t - s⌋₊
        have hN : N ≤ n := Nat.le_floor hs.2
        have hn : (n : ℝ≥0) ≤ t - s := Nat.floor_le (by positivity)
        have hn' : t - s < (n : ℝ≥0) + 1 := Nat.lt_floor_add_one _
        have hsJ : s ∈ J (n - N) := by
          simp only [J, Nat.sub_add_cancel hN]
          constructor
          · apply tsub_le_iff_right.mpr
            calc
              t = (t - s) + s := (tsub_add_cancel_of_le (a := s) (b := t) hs.1).symm
              _ ≤ s + ((n : ℝ≥0) + 1) := by simpa [add_comm] using add_le_add_left hn'.le s
          · exact le_tsub_of_add_le_left (add_le_of_le_tsub_right_of_le hs.1 hn)
        calc
          h (t - s) ≤ h ((n - N + N : ℕ) : ℝ≥0) := by
            simpa only [Nat.sub_add_cancel hN] using hh hn
          _ = (J (n - N)).indicator (fun _ => h ((n - N + N : ℕ) : ℝ≥0)) s :=
            by rw [indicator_of_mem hsJ]
          _ ≤ _ := le_tsum (fun k => (J k).indicator
            (fun _ => h ((k + N : ℕ) : ℝ≥0)) s) (n - N)
      · simp [indicator_of_notMem hs]
    _ = ∑' k : ℕ, h ((k + N : ℕ) : ℝ≥0) * μ (J k) := by
      rw [lintegral_tsum (fun k => (measurable_const.indicator measurableSet_Icc).aemeasurable)]
      simp only [lintegral_indicator_const measurableSet_Icc, J]
    _ ≤ ∑' k : ℕ, h ((k + N : ℕ) : ℝ≥0) * C := tsum_le_tsum fun k => by
      gcongr
      exact hJ k
    _ = _ := ENNReal.tsum_mul_right

/-- If the integer samples of an antitone function have finite sum, truncating the function
far from zero makes all its reflected convolutions small simultaneously. -/
theorem tendsto_iSup_lintegral_antitone_sub_tail (μ : Measure ℝ≥0) {C : ℝ≥0∞}
    (hμ : ∀ a, μ (Icc a (a + 1)) ≤ C) (hC : C ≠ ∞)
    {h : ℝ≥0 → ℝ≥0∞} (hh : Antitone h) (hsum : ∑' n : ℕ, h n ≠ ∞) :
    Tendsto (fun N : ℕ => ⨆ t : ℝ≥0,
      ∫⁻ s in Iic t ∩ {s | (N : ℝ≥0) ≤ t - s}, h (t - s) ∂μ) atTop (𝓝 0) := by
  have hlim := ENNReal.Tendsto.mul_const
    (ENNReal.tendsto_sum_nat_add (fun n : ℕ => h n) hsum) (Or.inr hC)
  simp only [zero_mul] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun N => iSup_le fun t => μ.lintegral_antitone_sub_tail_le hμ hh N t)

end MeasureTheory.Measure
