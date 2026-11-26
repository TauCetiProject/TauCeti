/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Weighted counts of events in a random selection

For each index, count the selected elements at which the indexed bad event occurs, then
sum the counts with nonnegative weights. A bound on the joint probability of selection
and a bad event controls this weighted count by Markov's inequality. No independence is
needed for this step, so it can be combined with a separate concentration estimate for the
size and distribution of the selection.

For the application of this estimate with equal selection probabilities, see Levent Alpöge's
`Formalism.MainNotions.J.tops_exist_of` in his formalization of the Riemann hypothesis
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace Finset

variable {Ω α ι : Type*}

open Classical in
/-- For each `i ∈ t`, count the `a ∈ s` for which the event `E i a` occurs at `x`, and
weight this count by `w i`. -/
noncomputable def weightedEventCount (s : Finset α) (t : Finset ι) (w : ι → ℝ)
    (E : ι → α → Set Ω) (x : Ω) : ℝ :=
  ∑ i ∈ t, w i * ((s.filter fun a ↦ x ∈ E i a).card : ℝ)

open Classical in
/-- The weighted event count is the sum of the weighted cardinalities of the event fibres. -/
theorem weightedEventCount_def (s : Finset α) (t : Finset ι) (w : ι → ℝ)
    (E : ι → α → Set Ω) (x : Ω) :
    s.weightedEventCount t w E x = ∑ i ∈ t, w i * ((s.filter fun a ↦ x ∈ E i a).card : ℝ) :=
  (rfl)

/-- With no candidates, the weighted event count is zero. -/
@[simp] theorem weightedEventCount_empty_left (t : Finset ι) (w : ι → ℝ)
    (E : ι → α → Set Ω) (x : Ω) : (∅ : Finset α).weightedEventCount t w E x = 0 := by
  classical
  simp [weightedEventCount_def]

/-- With no indices, the weighted event count is zero. -/
@[simp] theorem weightedEventCount_empty_right (s : Finset α) (w : ι → ℝ)
    (E : ι → α → Set Ω) (x : Ω) : s.weightedEventCount ∅ w E x = 0 := by
  classical
  simp [weightedEventCount_def]

/-- Writing the counts as sums of indicators lets them be integrated term by term. -/
theorem weightedEventCount_eq_sum_indicator (s : Finset α) (t : Finset ι) (w : ι → ℝ)
    (E : ι → α → Set Ω) (x : Ω) :
    s.weightedEventCount t w E x = ∑ i ∈ t, ∑ a ∈ s, (E i a).indicator (fun _ ↦ w i) x := by
  classical
  rw [weightedEventCount_def]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [← sum_boole (R := ℝ) (fun a ↦ x ∈ E i a) s, mul_sum]
  exact sum_congr rfl fun a _ ↦ by simp [indicator_apply, mul_ite]

/-- Nonnegative weights give a nonnegative event count. -/
theorem weightedEventCount_nonneg (s : Finset α) (t : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ t, 0 ≤ w i) (E : ι → α → Set Ω) (x : Ω) :
    0 ≤ s.weightedEventCount t w E x := by
  rw [weightedEventCount_def]
  exact sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (Nat.cast_nonneg _)

/-- Enlarging the events increases their weighted count when the weights are nonnegative. -/
theorem weightedEventCount_mono (s : Finset α) (t : Finset ι) {w : ι → ℝ}
    (hw : ∀ i ∈ t, 0 ≤ w i) {E F : ι → α → Set Ω}
    (hEF : ∀ i ∈ t, ∀ a ∈ s, E i a ⊆ F i a) (x : Ω) :
    s.weightedEventCount t w E x ≤ s.weightedEventCount t w F x := by
  classical
  simp only [weightedEventCount_def]
  refine sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left ?_ (hw i hi)
  exact_mod_cast card_le_card (monotone_filter_right s (fun a ha hx ↦ hEF i hi a ha hx))

variable [MeasurableSpace Ω]

/-- The count of finitely many weighted measurable events is measurable. -/
theorem measurable_weightedEventCount (s : Finset α) (t : Finset ι) (w : ι → ℝ)
    {E : ι → α → Set Ω} (hE : ∀ i ∈ t, ∀ a ∈ s, MeasurableSet (E i a)) :
    Measurable (s.weightedEventCount t w E) := by
  rw [funext (s.weightedEventCount_eq_sum_indicator t w E)]
  exact measurable_fun_sum _ fun i hi ↦
    measurable_fun_sum _ fun a ha ↦ measurable_const.indicator (hE i hi a ha)

/-- The count of finitely many weighted null-measurable events is integrable for a finite
measure. -/
theorem integrable_weightedEventCount (s : Finset α) (t : Finset ι) (w : ι → ℝ)
    {μ : Measure Ω} [IsFiniteMeasure μ] {E : ι → α → Set Ω}
    (hE : ∀ i ∈ t, ∀ a ∈ s, NullMeasurableSet (E i a) μ) :
    Integrable (s.weightedEventCount t w E) μ := by
  rw [funext (s.weightedEventCount_eq_sum_indicator t w E)]
  exact integrable_finsetSum _ fun i hi ↦
    integrable_finsetSum _ fun a ha ↦ (integrable_const _).indicator₀ (hE i hi a ha)

/-- The integral of the weighted count is the weighted sum of the event measures. -/
theorem integral_weightedEventCount (s : Finset α) (t : Finset ι) (w : ι → ℝ)
    {μ : Measure Ω} [IsFiniteMeasure μ] {E : ι → α → Set Ω}
    (hE : ∀ i ∈ t, ∀ a ∈ s, NullMeasurableSet (E i a) μ) :
    ∫ x, s.weightedEventCount t w E x ∂μ = ∑ i ∈ t, w i * ∑ a ∈ s, μ.real (E i a) := by
  have hi' i (hi : i ∈ t) a (ha : a ∈ s) :
      Integrable ((E i a).indicator fun _ ↦ w i) μ :=
    (integrable_const _).indicator₀ (hE i hi a ha)
  simp only [weightedEventCount_eq_sum_indicator]
  rw [integral_finsetSum t fun i hi ↦ integrable_finsetSum s (hi' i hi)]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [integral_finsetSum s (hi' i hi), mul_sum]
  exact sum_congr rfl fun a ha ↦ by
    rw [integral_indicator₀ (hE i hi a ha), setIntegral_const, smul_eq_mul, mul_comm]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- If `b` bounds the weighted sum of the outer measures of the events, there is a measurable
set of probability at least `3/4` on which the weighted count is at most `4 * b`. The events
need not be measurable or independent. -/
theorem exists_measurableSet_weightedEventCount_le (s : Finset α) (t : Finset ι)
    {w : ι → ℝ} {E : ι → α → Set Ω} {b : ℝ} (hw : ∀ i ∈ t, 0 ≤ w i)
    (hbudget : ∑ i ∈ t, w i * ∑ a ∈ s, μ.real (E i a) ≤ b) :
    ∃ H : Set Ω, MeasurableSet H ∧ (3 / 4 : ℝ) ≤ μ.real H ∧
      ∀ x ∈ H, s.weightedEventCount t w E x ≤ 4 * b := by
  let F (i : ι) (a : α) := toMeasurable μ (E i a)
  let f := s.weightedEventCount t w F
  have hF i (a : α) : MeasurableSet (F i a) := measurableSet_toMeasurable _ _
  have hFn i (_ : i ∈ t) a (_ : a ∈ s) : NullMeasurableSet (F i a) μ :=
    (hF i a).nullMeasurableSet
  have hf : 0 ≤ᵐ[μ] f := .of_forall <| s.weightedEventCount_nonneg t hw F
  have hfi : Integrable f μ := s.integrable_weightedEventCount t w hFn
  have hfm : Measurable f := s.measurable_weightedEventCount t w (fun i _ a _ ↦ hF i a)
  have hmean : ∫ x, f x ∂μ ≤ b := by
    rw [s.integral_weightedEventCount t w hFn]
    simpa only [F, measureReal_def, measure_toMeasurable] using hbudget
  have hb := (integral_nonneg_of_ae hf).trans hmean
  have hcount x (hx : x ∈ {x | f x ≤ 4 * b}) : s.weightedEventCount t w E x ≤ 4 * b :=
    (s.weightedEventCount_mono t hw (fun i _ a _ ↦ subset_toMeasurable μ (E i a)) x).trans hx
  refine ⟨{x | f x ≤ 4 * b}, measurableSet_le hfm measurable_const, ?_, hcount⟩
  have hc : μ.real {x | f x ≤ 4 * b} + μ.real {x | 4 * b < f x} = 1 := by
    simpa only [compl_ofPred, not_le, probReal_univ] using
      measureReal_add_measureReal_compl (μ := μ) (measurableSet_le hfm measurable_const)
  rcases hb.eq_or_lt with hb₀ | hb₀
  · have hz := (integral_eq_zero_iff_of_nonneg_ae hf hfi).mp
      (le_antisymm (hb₀ ▸ hmean) (integral_nonneg_of_ae hf))
    have hnull : μ.real {x | 4 * b < f x} = 0 := by
      apply (measureReal_eq_zero_iff (measure_ne_top μ _)).2
      have hae : ∀ᵐ x ∂μ, f x ≤ 4 * b := hz.mono fun x hx ↦ by simpa [← hb₀] using hx.le
      simpa only [not_le] using ae_iff.mp hae
    linarith
  · have hmul := (mul_meas_ge_le_integral_of_nonneg hf hfi (4 * b)).trans hmean
    have hle : μ.real {x | 4 * b ≤ f x} ≤ 1 / 4 := by
      apply le_of_mul_le_mul_left _ (show 0 < 4 * b by positivity)
      linarith
    have hsub : {x | 4 * b < f x} ⊆ {x | 4 * b ≤ f x} :=
      fun _ hx ↦ mem_ofPred_eq.mpr (le_of_lt (mem_ofPred_eq.mp hx))
    have hstrict := (measureReal_mono (μ := μ) hsub).trans hle
    linarith

end Finset

namespace TauCeti

open Finset

variable {Ω α ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

open Classical in
/-- Intersect the weighted bad-count event with any event of probability at least `3/4` on
which the actual size of the selection is at least half the sum of selection probabilities.
With probability at least `1/2`, both events hold, and the weighted bad count is at most
`8 * p` times the actual size times the total weight. -/
theorem half_le_measureReal_inter_weighted_bad_count_le {s : Finset α} {t : Finset ι}
    {w : ι → ℝ} {S : α → Set Ω} {B : ι → α → Set Ω} {p : ℝ≥0} {G : Set Ω}
    (hw : ∀ i ∈ t, 0 ≤ w i)
    (hbad : ∀ i ∈ t, ∀ a ∈ s, μ.real (S a ∩ B i a) ≤ (p : ℝ) * μ.real (S a))
    (hG : (3 / 4 : ℝ) ≤ μ.real G)
    (hsize : ∀ x ∈ G, (∑ a ∈ s, μ.real (S a)) ≤ 2 * ((s.filter fun a ↦ x ∈ S a).card : ℝ)) :
    (1 / 2 : ℝ) ≤ μ.real (G ∩ {x |
      s.weightedEventCount t w (fun i a ↦ S a ∩ B i a) x ≤
        4 * (p : ℝ) * (∑ a ∈ s, μ.real (S a)) * ∑ i ∈ t, w i ∧
      4 * (p : ℝ) * (∑ a ∈ s, μ.real (S a)) * ∑ i ∈ t, w i ≤
        8 * (p : ℝ) * ((s.filter fun a ↦ x ∈ S a).card : ℝ) * ∑ i ∈ t, w i}) := by
  let b := (p : ℝ) * (∑ a ∈ s, μ.real (S a)) * ∑ i ∈ t, w i
  have hbudget : ∑ i ∈ t, w i * ∑ a ∈ s, μ.real (S a ∩ B i a) ≤ b := calc
    _ ≤ ∑ i ∈ t, w i * ((p : ℝ) * ∑ a ∈ s, μ.real (S a)) := by
      refine sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left ?_ (hw i hi)
      rw [mul_sum]
      exact sum_le_sum (hbad i hi)
    _ = b := by rw [← sum_mul, mul_comm]
  obtain ⟨H, hmH, hH, hcount⟩ := s.exists_measurableSet_weightedEventCount_le t hw hbudget
  have hinter : (1 / 2 : ℝ) ≤ μ.real (G ∩ H) := by
    have hu := measureReal_mono (μ := μ) (subset_univ (G ∪ H))
    rw [probReal_univ] at hu
    linarith [measureReal_union_add_inter (μ := μ) (s := G) hmH]
  refine hinter.trans (measureReal_mono fun x hx ↦ ⟨hx.1, ?_, ?_⟩)
  · simpa only [b, mul_assoc] using hcount x hx.2
  · have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hsize x hx.1) (by positivity : 0 ≤ 4 * (p : ℝ))) (sum_nonneg hw)
    convert h using 1; ring

end TauCeti
