/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Poisson.Filtered
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.Probability.HasLaw
import TauCeti.Probability.Independence.Completion
import TauCeti.Probability.Independence.CondExp
import TauCeti.Probability.Independence.Limit
import TauCeti.Probability.Independence.Sup
import TauCeti.Probability.Process.Filtration.Natural

/-!
# Augmentation and right-continuity for filtered Poisson processes

For any homogeneous Poisson process `N` of rate `α` relative to a filtration `ℱ`, the probability
that `N` changes across `[s, u]` is `1 - exp (-α * (u - s)) ≤ α * (u - s)`. Along any sequence
`u n ≥ s` with summable gaps `u n - s`, Borel–Cantelli shows that `N (u n) = N s` eventually almost
surely, without any pathwise regularity assumption on the given version `N`.

Consequently:
* `N` remains a filtered Poisson process on `ℱ.rightCont`, on `ℱ.nullAugment P` (under
  `P.completion`), and hence on `(ℱ.ambientNullAugmentation P).rightCont` and
  `(ℱ.nullAugment P).rightCont`, with no path-continuity hypothesis;
* the entire future increment process `(N (s + v) - N s)_v` is independent of `ℱ.rightCont s`;
* both `(Filtration.natural N hmeas).ambientNullAugmentation P` and
  `(Filtration.natural N hmeas).nullAugment P` are already right-continuous.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3, Theorem 31.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition, Springer,
  1991, §2.7.A.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {α : ℝ≥0} {N : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- The probability that no increment occurs across `[s, t]` is `exp (-(α * (t - s)))`. -/
theorem measureReal_sub_eq_zero (h : IsFilteredPoissonProcess ℱ α N P) {s t : ℝ≥0}
    (hst : s ≤ t) :
    P.real {ω | N t ω - N s ω = 0} = exp (-(α * (t - s) : ℝ)) := by
  change P.real {ω | (N t - N s) ω = 0} = _
  rw [(h.hasLaw_sub hst).measureReal_eq (measurableSet_singleton (0 : ℝ)),
    Set.ofPred_eq_eq_singleton, map_measureReal_apply (by fun_prop) (measurableSet_singleton 0)]
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' {0} = {0} := by
    ext n
    simp
  rw [hpre, poissonMeasure_real_singleton, NNReal.coe_mul, NNReal.coe_sub hst]
  simp

/-- The measure of the event `{N t ≠ N s}` for `s ≤ t` is bounded by `α * (t - s)`. -/
theorem measure_eval_ne_le (h : IsFilteredPoissonProcess ℱ α N P) {s t : ℝ≥0} (hst : s ≤ t) :
    P {ω | N t ω ≠ N s ω} ≤ (α : ℝ≥0∞) * ((t - s : ℝ≥0) : ℝ≥0∞) := by
  have := h.isProbabilityMeasure
  have hset : {ω | N t ω ≠ N s ω} = {ω | N t ω - N s ω = 0}ᶜ := by
    ext ω
    simp [sub_eq_zero]
  have hmeas : MeasurableSet {ω | N t ω - N s ω = 0} :=
    ((h.measurable t).sub (h.measurable s)) (measurableSet_singleton 0)
  have hreal : P.real {ω | N t ω ≠ N s ω} ≤ (α : ℝ) * (t - s : ℝ≥0) := by
    rw [hset, probReal_compl_eq_one_sub hmeas, h.measureReal_sub_eq_zero hst, ← NNReal.coe_sub hst]
    linarith [Real.one_sub_le_exp_neg ((α : ℝ) * (t - s : ℝ≥0))]
  calc
    P {ω | N t ω ≠ N s ω} = ENNReal.ofReal (P.real {ω | N t ω ≠ N s ω}) :=
      (ofReal_measureReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal ((α : ℝ) * (t - s : ℝ≥0)) := ENNReal.ofReal_le_ofReal hreal
    _ = (α : ℝ≥0∞) * ((t - s : ℝ≥0) : ℝ≥0∞) := by
      rw [← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]

/-- Along any sequence of times `u n ≥ s` with summable gaps `u n - s`, a filtered Poisson process
eventually equals `N s` almost surely. No path regularity is assumed. -/
theorem ae_eventually_eval_eq_of_tsum_sub_ne_top (h : IsFilteredPoissonProcess ℱ α N P)
    {s : ℝ≥0} {u : ℕ → ℝ≥0} (hsu : ∀ n, s ≤ u n)
    (hsum : (∑' n, ((u n - s : ℝ≥0) : ℝ≥0∞)) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, N (u n) ω = N s ω := by
  have hle : (∑' n, P {ω | N (u n) ω ≠ N s ω}) ≤
      (α : ℝ≥0∞) * ∑' n, ((u n - s : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun n ↦ h.measure_eval_ne_le (hsu n)
  have hfin : (∑' n, P {ω | N (u n) ω ≠ N s ω}) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hsum) hle
  filter_upwards [MeasureTheory.ae_eventually_notMem hfin] with ω hω
  exact hω.mono fun _ hn ↦ not_ne_iff.mp hn

/-- At every fixed time `s`, `N (s + 2⁻ⁿ)` eventually equals `N s` almost surely. -/
theorem ae_eventually_eval_add_two_inv_pow_eq (h : IsFilteredPoissonProcess ℱ α N P) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, N (s + (2⁻¹ : ℝ≥0) ^ n) ω = N s ω := by
  refine h.ae_eventually_eval_eq_of_tsum_sub_ne_top (fun _ ↦ le_self_add) ?_
  have hgeom : (∑' n : ℕ, (((2⁻¹ : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞)) = 2 := by
    simp only [ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
    exact ENNReal.tsum_geometric_two
  simp only [add_tsub_cancel_left, hgeom]
  norm_num

/-- Every filtered Poisson process remains a filtered Poisson process on the right-continuation of
its filtration. No pathwise right-continuity hypothesis is needed. -/
theorem rightCont (h : IsFilteredPoissonProcess ℱ α N P) :
    IsFilteredPoissonProcess ℱ.rightCont α N P where
  stronglyAdapted t := (h.stronglyAdapted t).mono (ℱ.le_rightCont t)
  eval_zero_ae_eq_zero := h.eval_zero_ae_eq_zero
  hasLaw_sub := h.hasLaw_sub
  indep_sub s t hst := by
    have := h.isProbabilityMeasure
    rcases hst.eq_or_lt with rfl | hst
    · have hzero : N s - N s = fun _ ↦ (0 : ℝ) := funext fun _ ↦ sub_self _
      rw [hzero, MeasurableSpace.comap_const]
      exact indep_bot_left (ℱ.rightCont s)
    · let u : ℕ → ℝ≥0 := fun n ↦ min t (s + (2⁻¹ : ℝ≥0) ^ n)
      have hsum : (∑' n, ((u n - s : ℝ≥0) : ℝ≥0∞)) ≠ ∞ := by
        refine ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ?_
        rw [← ENNReal.tsum_geometric_two]
        refine tsum_le_tsum fun n ↦ ?_
        have hle : u n - s ≤ (2⁻¹ : ℝ≥0) ^ n :=
          (tsub_le_tsub_right (min_le_right _ _) s).trans_eq (add_tsub_cancel_left _ _)
        exact (ENNReal.coe_le_coe.mpr hle).trans_eq
          (by simp only [ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat])
      have hind (n : ℕ) : Indep (ℱ.rightCont s) (.comap (N t - N (u n)) inferInstance) P :=
        indep_of_indep_of_le_left (h.indep_sub (min_le_left t _)).symm
          (ℱ.rightCont_le_of_lt (lt_min hst (lt_add_of_pos_right s (by positivity))))
      refine (indep_comap_of_ae_tendsto (ℱ.rightCont.le s)
        (fun n ↦ ((h.measurable t).sub (h.measurable (u n))).aemeasurable)
        ((h.measurable t).sub (h.measurable s)).aemeasurable hind ?_).symm
      filter_upwards [h.ae_eventually_eval_eq_of_tsum_sub_ne_top
        (fun n ↦ le_min hst.le le_self_add) hsum] with ω hω
      exact tendsto_const_nhds.congr' (hω.mono fun _ hn ↦ by dsimp only [u, Pi.sub_apply]; rw [hn])

/-- Completing the ambient probability space and adjoining all ambient null events to the
filtration preserves the filtered Poisson property. -/
theorem nullAugment (h : IsFilteredPoissonProcess ℱ α N P) :
    IsFilteredPoissonProcess (ℱ.nullAugment P) α
      (fun t (ω : NullMeasurableSpace Ω P) ↦ N t ω) P.completion where
  stronglyAdapted t := (h.stronglyAdapted t).mono (ℱ.le_nullAugment P t)
  eval_zero_ae_eq_zero := P.ae_completion.symm ▸ h.eval_zero_ae_eq_zero
  hasLaw_sub _ _ hst := (h.hasLaw_sub hst).completion
  indep_sub s t hst := by
    have hind : Indep (.comap (N t - N s) inferInstance) (ℱ.nullAugment P s) P := by
      rw [Filtration.nullAugment_apply]
      exact (h.indep_sub hst).eventuallyMeasurableSpace_right
    change @Indep (NullMeasurableSpace Ω P) (.comap (N t - N s) inferInstance)
      (ℱ.nullAugment P s) inferInstance P.completion
    exact indep_completion_iff.mpr hind

/-- The entire future increment process `(N (s + v) - N s)_v` of a filtered Poisson process is
independent of the right-continuous past `ℱ.rightCont s`. -/
theorem indep_comap_shift_rightCont (h : IsFilteredPoissonProcess ℱ α N P) (s : ℝ≥0) :
    Indep (.comap (fun ω v ↦ N (s + v) ω - N s ω) inferInstance) (ℱ.rightCont s) P := by
  classical
  have := h.isProbabilityMeasure
  let u : ℕ → ℝ≥0 := fun n ↦ s + (2⁻¹ : ℝ≥0) ^ n
  have hmshift (t : ℝ≥0) : Measurable fun ω (v : ℝ≥0) ↦ N (t + v) ω - N t ω :=
    measurable_pi_iff.mpr fun v ↦ (h.measurable (t + v)).sub (h.measurable t)
  have hfinite (I : Finset ℝ≥0) :
      Indep (.comap (fun ω (v : I) ↦ N (s + v) ω - N s ω) inferInstance)
        (ℱ.rightCont s) P := by
    refine (indep_comap_of_ae_tendsto (X := fun n ω (v : I) ↦ N (u n + v) ω - N (u n) ω)
      (ℱ.rightCont.le s)
      (fun n ↦ (I.measurable_restrict.comp (hmshift (u n))).aemeasurable)
      (I.measurable_restrict.comp (hmshift s)).aemeasurable (fun n ↦ ?_) ?_).symm
    · refine (indep_of_indep_of_le_right
        (indep_of_indep_of_le_left (h.indep_comap_shift (u n)) ?_)
        (ℱ.rightCont_le_of_lt (lt_add_of_pos_right s (by positivity)))).symm
      rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
      exact iSup_le fun v ↦ le_iSup (fun a : ℝ≥0 ↦
        MeasurableSpace.comap (fun ω ↦ N (u n + a) ω - N (u n) ω) inferInstance) v.val
    · have hall : ∀ᵐ ω ∂P, ∀ v : I, ∀ᶠ n in atTop,
          N (s + v + (2⁻¹ : ℝ≥0) ^ n) ω = N (s + v) ω :=
        ae_all_iff.mpr fun v ↦ h.ae_eventually_eval_add_two_inv_pow_eq (s + v)
      filter_upwards [hall, h.ae_eventually_eval_add_two_inv_pow_eq s] with ω hωv hωs
      refine tendsto_pi_nhds.mpr fun v ↦ tendsto_const_nhds.congr' ?_
      filter_upwards [hωv v, hωs] with n hnv hns
      dsimp only [u]
      rw [add_right_comm s ((2⁻¹ : ℝ≥0) ^ n) v.val, hnv, hns]
      rfl
  rw [MeasurableSpace.comap_process_pi, iSup_eq_iSup_finset]
  refine indep_iSup_of_monotone (fun I ↦ ?_) (fun I ↦ ?_) (ℱ.rightCont.le s)
    (fun _ _ hIJ ↦ iSup_le_iSup_of_subset hIJ)
  · simpa only [MeasurableSpace.comap_process_pi, iSup_subtype'] using hfinite I
  · exact iSup₂_le fun v _ ↦ ((h.measurable (s + v)).sub (h.measurable s)).comap_le

/-- Every event of the raw right-continuous natural filtration of a Poisson process agrees almost
everywhere with an event of the natural filtration at the same time. -/
theorem rightCont_natural_le_nullAugment (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) (s : ℝ≥0) :
    (Filtration.natural N hmeas).rightCont s ≤ (Filtration.natural N hmeas).nullAugment P s := by
  classical
  have := h.isProbabilityMeasure
  let 𝒢 := Filtration.natural N hmeas
  let mFuture := MeasurableSpace.comap (fun ω v ↦ N (s + v) ω - N s ω) inferInstance
  let : MeasurableSpace Ω := mΩ
  have hfuture : mFuture ≤ mΩ :=
    (measurable_pi_iff.mpr fun v ↦ (hmeas (s + v)).measurable.sub (hmeas s).measurable).comap_le
  have hle : 𝒢.rightCont s ≤ 𝒢 s ⊔ mFuture :=
    (𝒢.rightCont_le_of_lt (lt_add_one s)).trans
      (Filtration.natural_le_sup_comap_shift N hmeas s (s + 1))
  intro A hA
  rw [Filtration.measurableSet_nullAugment_iff]
  have hAi : Integrable (A.indicator fun _ ↦ (1 : ℝ)) P :=
    (integrable_const 1).indicator (𝒢.rightCont.le s A hA)
  have hcond := ((h.natural hmeas).indep_comap_shift_rightCont s).symm
    |>.condExp_eq_of_le_of_stronglyMeasurable_sup (𝒢.le_rightCont s) (𝒢.rightCont.le s)
      hfuture ((stronglyMeasurable_const.indicator hA).mono hle) hAi
  have heq : P[A.indicator (fun _ ↦ (1 : ℝ)) | 𝒢 s] =ᵐ[P] A.indicator fun _ ↦ (1 : ℝ) :=
    hcond.symm.trans (EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (𝒢.rightCont.le s)
        (stronglyMeasurable_const.indicator hA) hAi))
  refine ⟨{ω | 1 / 2 < P[A.indicator (fun _ ↦ (1 : ℝ)) | 𝒢 s] ω},
    measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable, ?_⟩
  filter_upwards [heq] with ω hω
  simp only [hω]
  by_cases hωA : ω ∈ A <;> norm_num [hωA]

/-- The raw right-continuous natural filtration of a Poisson process is contained in its
original-space null augmentation. -/
theorem rightCont_natural_le_ambientNullAugmentation (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) :
    (Filtration.natural N hmeas).rightCont ≤
      (Filtration.natural N hmeas).ambientNullAugmentation P := fun s ↦ by
  rw [Filtration.ambientNullAugmentation_apply]
  exact le_inf ((Filtration.natural N hmeas).rightCont.le s)
    (h.rightCont_natural_le_nullAugment hmeas s)

/-- The original-space null augmentation of the natural filtration of a Poisson process is
right-continuous. -/
theorem isRightContinuous_ambientNullAugmentation_natural (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) :
    ((Filtration.natural N hmeas).ambientNullAugmentation P).IsRightContinuous := by
  constructor
  rw [Filtration.rightCont_ambientNullAugmentation]
  exact (Filtration.ambientNullAugmentation_mono
    (h.rightCont_natural_le_ambientNullAugmentation hmeas) P).trans_eq
    (Filtration.ambientNullAugmentation_idem _ P)

/-- The completed null augmentation of the natural filtration of a Poisson process is
right-continuous, without assuming completeness of the original probability space. -/
theorem isRightContinuous_nullAugment_natural (h : IsFilteredPoissonProcess ℱ α N P)
    (hmeas : ∀ t, StronglyMeasurable (N t)) :
    ((Filtration.natural N hmeas).nullAugment P).IsRightContinuous := by
  constructor
  intro s
  rw [Filtration.rightCont_nullAugment_apply]
  intro A hA
  rw [Filtration.measurableSet_nullAugment_iff] at hA ⊢
  obtain ⟨B, hB, hAB⟩ := hA
  obtain ⟨C, hC, hBC⟩ := (Filtration.measurableSet_nullAugment_iff _ P s B).mp
    (h.rightCont_natural_le_nullAugment hmeas s B hB)
  exact ⟨C, hC, hAB.trans hBC⟩

end TauCeti.Probability.IsFilteredPoissonProcess
