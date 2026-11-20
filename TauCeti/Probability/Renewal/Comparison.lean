/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Bernoulli
import TauCeti.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Comparing renewal counts with two-point increments

At a threshold `a > 0`, replace every increment at least `a` by `a` and every smaller increment
by zero. The resulting independent increments have the two-point law with success probability
`P {ω | a ≤ T 0 ω}`. When this probability is positive, the comparison process is nonexplosive
and its count dominates the original count simultaneously at all times almost surely.
The comparison retains genuine zero-time arrivals and includes increments equal to the threshold.

The explicit binomial cdf bound for the original count follows from the two-point count law.
A nondegenerate common increment law always admits a strictly positive comparison threshold.
The comparison can be used to bound renewal-count moments.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025, §5.7, Lemma 5.11.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} (T : ℕ → Ω → ℝ≥0) (a : ℝ≥0)

/-- Replace an increment by `a` if it is at least `a`, and by zero otherwise. -/
def thresholdIncrements (n : ℕ) : Ω → ℝ≥0 :=
  (Ici a).indicator (fun _ ↦ a) ∘ T n

/-- The thresholded gap includes equality in the threshold event. -/
@[simp]
lemma thresholdIncrements_apply (n : ℕ) (ω : Ω) :
    thresholdIncrements T a n ω = if a ≤ T n ω then a else 0 := by
  classical
  simp [thresholdIncrements, indicator_apply]

/-- Thresholding only decreases the increments. -/
lemma thresholdIncrements_le (n : ℕ) (ω : Ω) : thresholdIncrements T a n ω ≤ T n ω := by
  simp only [thresholdIncrements_apply]
  split_ifs with h
  · exact h
  · exact zero_le

variable {T a} [MeasurableSpace Ω] {P : Measure Ω}

@[fun_prop]
lemma measurable_thresholdIncrements {n : ℕ} (hT : Measurable (T n)) :
    Measurable (thresholdIncrements T a n) :=
  (measurable_const.indicator measurableSet_Ici).comp hT

/-- Thresholding each coordinate preserves independence. -/
theorem _root_.ProbabilityTheory.iIndepFun.thresholdIncrements (hindep : iIndepFun T P)
    (a : ℝ≥0) : iIndepFun (TauCeti.Probability.thresholdIncrements T a) P :=
  hindep.comp (fun _ ↦ (Ici a).indicator (fun _ ↦ a))
    (fun _ ↦ measurable_const.indicator measurableSet_Ici)

/-- Identically distributed increments give the same two-point law after thresholding, with
success probability equal to the mass of the closed threshold event `a ≤ T 0`. -/
theorem hasLaw_thresholdIncrements [IsProbabilityMeasure P]
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) (a : ℝ≥0) (n : ℕ) :
    HasLaw (thresholdIncrements T a n)
      (bernoulliMeasure a 0 ⟨P.real {ω | a ≤ T 0 ω}, by simp⟩) P := by
  have h := hasLaw_indicator_bernoulliMeasure a
    ((hid n).aemeasurable_fst.nullMeasurableSet_preimage (measurableSet_Ici (a := a)))
  have hprob : P.real (T n ⁻¹' Ici a) = P.real {ω | a ≤ T 0 ω} := by
    exact congrArg ENNReal.toReal ((hid n).measure_mem_eq measurableSet_Ici)
  have hdef : thresholdIncrements T a n = (T n ⁻¹' Ici a).indicator (fun _ ↦ a) :=
    funext fun ω ↦ (Set.indicator_comp_right (s := Ici a) (g := fun _ ↦ a) (T n) (x := ω)).symm
  rw [hdef]
  simpa only [hprob] using h

/-- At a positive threshold with positive success probability, the two-point count dominates the
original count on one event for every time. The natural count's exceptional-path convention is
handled using nonexplosion of the comparison process. -/
theorem ae_renewalCountNat_le_thresholdIncrements
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (ha : 0 < a) (hq : 0 < P {ω | a ≤ T 0 ω}) :
    ∀ᵐ ω ∂P, ∀ t, renewalCountNat T t ω ≤ renewalCountNat (thresholdIncrements T a) t ω := by
  have := hindep.isProbabilityMeasure
  have hqreal : 0 < P.real {ω | a ≤ T 0 ω} :=
    ENNReal.toReal_pos hq.ne' (measure_ne_top P _)
  filter_upwards [ae_tendsto_arrival_atTop_of_bernoulliMeasure
    (hindep.thresholdIncrements a) (hasLaw_thresholdIncrements hid a) ha hqreal]
    with ω hω t
  exact renewalCountNat_anti_of_tendsto (fun n ↦ thresholdIncrements_le T a n ω) hω t

/-- The cdf of any i.i.d. renewal count is bounded below by the upper binomial tail associated
with a positive threshold. The formula includes time zero and success probability one. -/
theorem binomial_tail_le_measure_renewalCountNat_le
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (ha : 0 < a) (hq : 0 < P {ω | a ≤ T 0 ω}) (t : ℝ≥0) (n : ℕ) :
    binomial (n + 1) ⟨P.real {ω | a ≤ T 0 ω}, by
      have := hindep.isProbabilityMeasure
      simp⟩ (Ioi ⌊t / a⌋₊) ≤ P {ω | renewalCountNat T t ω ≤ n} := by
  have := hindep.isProbabilityMeasure
  have hqreal : 0 < P.real {ω | a ≤ T 0 ω} :=
    ENNReal.toReal_pos hq.ne' (measure_ne_top P _)
  rw [← measure_renewalCountNat_le_of_bernoulliMeasure
    (hindep.thresholdIncrements a) (hasLaw_thresholdIncrements hid a) ha hqreal]
  apply measure_mono_ae
  filter_upwards [ae_renewalCountNat_le_thresholdIncrements hindep hid ha hq] with ω hω hn
  exact (hω t).trans hn

/-- A nondegenerate i.i.d. renewal process admits a two-point comparison process on the same
sample space whose count dominates it simultaneously for all times. Its success probability is
strictly positive, so the binomial cdf bound applies at the selected threshold. -/
theorem exists_thresholdIncrements_domination
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) :
    ∃ a : ℝ≥0, 0 < a ∧ 0 < P {ω | a ≤ T 0 ω} ∧
      ∀ᵐ ω ∂P, ∀ t, renewalCountNat T t ω ≤ renewalCountNat (thresholdIncrements T a) t ω := by
  have := hindep.isProbabilityMeasure
  obtain ⟨a, ha, hq⟩ := P.exists_pos_measure_le_of_measure_zero_lt_one (T 0) hzero
  exact ⟨a, ha, hq, ae_renewalCountNat_le_thresholdIncrements hindep hid ha hq⟩

end TauCeti.Probability
