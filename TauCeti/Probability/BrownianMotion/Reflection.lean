/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.HittingTime
public import TauCeti.Probability.Distributions.FoldedNormal.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Probability.CDF
import TauCeti.MeasureTheory.Measure.Interval
import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.BrownianMotion.Version
import TauCeti.Probability.Cdf
import TauCeti.Probability.Distributions.Gaussian.Symmetry
import TauCeti.Probability.Process.HittingTime
import TauCeti.Probability.Process.HittingTime.Grid

/-!
# The reflection principle and running maximum of Brownian motion

This file establishes finite-grid and continuous-time reflection inequalities and equalities for
one-dimensional Brownian motion without completeness of the ambient measurable space or a strong
Markov framework, feeding running-maximum laws, immediate zero crossings, open/closed half-line hit
equivalence, and level-hitting distributions on native `ProbabilityTheory.IsBrownianReal`:
* `ProbabilityTheory.IsPreBrownianReal.measure_exists_gt_le`: finite-grid reflection inequality.
* `ProbabilityTheory.IsBrownianReal.measure_exists_le_ge` and `measure_exists_le_gt`:
  `P {ω | ∃ s ≤ t, a ≤ B s ω} = 2 * P {ω | a ≤ B t ω}` for `a > 0` and strict exceedance for
  `a ≥ 0`, together with their real-valued and negative-level counterparts.
* `ProbabilityTheory.IsBrownianReal.hittingAfter_Ioi_zero_ae_eq_zero` and
  `hittingAfter_Iio_zero_ae_eq_zero`: immediate positive and negative crossings after `0`.
* `ProbabilityTheory.IsBrownianReal.hasLaw_iSup_Iic_map_abs` and `hasLaw_iSup_Iic`: the running
  maximum `⨆ s : Set.Iic t, B s ω` has law `(gaussianReal 0 t).map (|·|)` for all `t : ℝ≥0`, and
  `foldedNormalMeasure 0 √t` when `t ≠ 0`.

## References
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.6, §2.8.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set TauCeti
open scoped NNReal ENNReal Topology Pointwise

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B W : ℝ≥0 → Ω → ℝ}

/-- At any positive time `t ≠ 0` or nonzero threshold `a ≠ 0`, a real pre-Brownian motion assigns
equal measure to `{ω | a ≤ B t ω}` and `{ω | a < B t ω}`. -/
theorem measure_eval_ge_eq_measure_eval_gt (hB : IsPreBrownianReal B P) {t : ℝ≥0} {a : ℝ}
    (h : t ≠ 0 ∨ a ≠ 0) : P {ω | a ≤ B t ω} = P {ω | a < B t ω} := by
  have h0 : gaussianReal 0 t {a} = 0 := by
    rcases eq_or_ne t 0 with rfl | ht
    · simp [(h.resolve_left (not_not.mpr rfl)).symm]
    · have := nullSingletonClass_gaussianReal (μ := 0) ht; exact measure_singleton a
  exact ((hB.hasLaw_eval t).measure_eq (p := (· ∈ Ici a)) measurableSet_Ici).trans
    ((measure_congr (Ioi_ae_eq_Ici' h0).symm).trans
      ((hB.hasLaw_eval t).measure_eq (p := (· ∈ Ioi a)) measurableSet_Ioi).symm)

private theorem measure_exists_gt_le_of_stronglyMeasurable (hW : IsPreBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g)
    (b : ℝ) : P {ω | ∃ i, b < W (g i) ω} ≤ 2 * P {ω | b < W (g (Fin.last n)) ω} := by
  let ℱ := Filtration.natural W hWm; have hWF := hW.isFilteredPreBrownianReal_natural hWm
  let N : Fin (n + 1) := Fin.last n
  let A (i : Fin (n + 1)) : Set Ω := {ω | (∀ j < i, W (g j) ω ≤ b) ∧ b < W (g i) ω}
  let C (i : Fin (n + 1)) : Set Ω := ((W (g N) - W (g i)) ⁻¹' Ici 0) ∩ A i
  have hA_meas (i : Fin (n + 1)) : MeasurableSet[ℱ (g i)] (A i) := by
    simp only [A, ofPred_and, ofPred_forall]
    exact (MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun (hji : j < i) ↦
      measurableSet_le ((hWF.adapted (g j)).mono (ℱ.mono (hg hji.le)) le_rfl)
        measurable_const).inter (measurableSet_lt measurable_const (hWF.adapted (g i)))
  have hA_disj : Pairwise fun i k ↦ Disjoint (A i) (A k) := fun i k hik ↦
    disjoint_left.mpr fun ω hi hk ↦ (lt_trichotomy i k).elim (fun h ↦ hi.2.not_ge (hk.1 i h))
      fun h ↦ h.elim hik fun h' ↦ hk.2.not_ge (hi.1 k h')
  have hA_union : (⋃ i, A i) = {ω | ∃ i, b < W (g i) ω} := by
    ext ω; simp only [mem_iUnion, mem_ofPred_eq, A]
    refine ⟨fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩, fun h ↦ ?_⟩; classical
    exact ⟨Fin.find _ h, fun _ hj ↦ not_lt.mp (Fin.find_min h hj), Fin.find_spec h⟩
  have hbound (i : Fin (n + 1)) : P (A i) ≤ 2 * P (C i) := calc
    P (A i) = (2 * 2⁻¹) * P (A i) := by
        rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ (2 * gaussianReal 0 (g N - g i) (Ici 0)) * P (A i) := by
        gcongr; exact (gaussianReal 0 _).inv_two_le_measure_Ici_zero
    _ = 2 * P (C i) := by
        rw [mul_assoc, (Indep_iff _ _ _).mp (hWF.indep_sub (hg (Fin.le_last i))) _ (A i)
          ⟨Ici 0, measurableSet_Ici, rfl⟩ (hA_meas i)]
        congr 2
        exact ((hW.hasLaw_sub_of_le (hg (Fin.le_last i))).measure_eq (p := (· ∈ Ici 0))
          measurableSet_Ici).symm
  rw [← hA_union, measure_iUnion hA_disj (fun i ↦ ℱ.le (g i) _ (hA_meas i)), tsum_fintype]
  calc ∑ i, P (A i) ≤ ∑ i, 2 * P (C i) := Finset.sum_le_sum fun i _ ↦ hbound i
    _ = 2 * P (⋃ i, C i) := by
        rw [← Finset.mul_sum, measure_iUnion (fun i k hik ↦ (hA_disj hik).mono inter_subset_right
          inter_subset_right) (fun i ↦ (measurableSet_Ici.preimage
            ((hWm (g N)).measurable.sub (hWm (g i)).measurable)).inter (ℱ.le (g i) _ (hA_meas i))),
          tsum_fintype]
    _ ≤ 2 * P {ω | b < W (g N) ω} := by
        gcongr; exact fun ω ⟨_, ⟨i, rfl⟩, hΔ, _, hbi⟩ ↦ lt_of_lt_of_le hbi (sub_nonneg.mp hΔ)

/-- **Discrete reflection inequality** for a real pre-Brownian motion: along any finite monotone
grid `g : Fin (n + 1) → ℝ≥0`, the probability of exceeding `b` somewhere on the grid is at most
twice the probability of exceeding `b` at the final grid time. -/
theorem measure_exists_gt_le (hB : IsPreBrownianReal B P) {n : ℕ} {g : Fin (n + 1) → ℝ≥0}
    (hg : Monotone g) (b : ℝ) :
    P {ω | ∃ i, b < B (g i) ω} ≤ 2 * P {ω | b < B (g (Fin.last n)) ω} := by
  let W (t : ℝ≥0) : Ω → ℝ := (hB.integrable_eval t).aestronglyMeasurable.mk (B t)
  have hBW (t : ℝ≥0) : B t =ᵐ[P] W t := (hB.integrable_eval t).aestronglyMeasurable.ae_eq_mk
  rw [measure_congr (t := {ω | ∃ i, b < W (g i) ω}) (eventuallyEqSet_iff.mpr
      ((ae_all_iff.mpr fun i ↦ hBW (g i)).mono fun _ hω ↦ by simp only [mem_ofPred_eq, hω])),
    measure_congr (s := {ω | b < B (g (Fin.last n)) ω}) (t := {ω | b < W (g (Fin.last n)) ω})
      ((hBW (g (.last n))).preimage (Ioi b))]
  exact (hB.congr hBW).measure_exists_gt_le_of_stronglyMeasurable
    (fun t ↦ (hB.integrable_eval t).aestronglyMeasurable.stronglyMeasurable_mk) hg b

/-- Symmetric discrete reflection inequality below a level `b`. -/
theorem measure_exists_lt_le (hB : IsPreBrownianReal B P) {n : ℕ} {g : Fin (n + 1) → ℝ≥0}
    (hg : Monotone g) (b : ℝ) :
    P {ω | ∃ i, B (g i) ω < b} ≤ 2 * P {ω | B (g (Fin.last n)) ω < b} := by
  simpa only [Pi.neg_apply, neg_lt_neg_iff] using hB.neg.measure_exists_gt_le hg (-b)

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W B : ℝ≥0 → Ω → ℝ}

private theorem measure_exists_le_gt_le_of_continuous (hW : IsPreBrownianReal W P)
    (hWc : ∀ ω, Continuous (W · ω)) (t : ℝ≥0) (b : ℝ) :
    P {ω | ∃ s ≤ t, b < W s ω} ≤ 2 * P {ω | b < W t ω} := by
  rw [setOf_exists_le_gt_eq_iUnion_dyadicTime hWc t b]
  refine le_of_tendsto' (tendsto_measure_iUnion_atTop (μ := P) (monotone_nat_of_le_succ
    fun n _ ⟨i, hi⟩ ↦ let ⟨j, hj⟩ := exists_dyadicTime_eq_of_le t i (Nat.le_succ n)
      ⟨j, hj ▸ hi⟩)) fun n ↦ ?_
  simpa only [Function.comp_apply, dyadicTime_last] using
    hW.measure_exists_gt_le (dyadicTime_monotone t n) b

private theorem measure_exists_le_ge_le_of_continuous (hW : IsPreBrownianReal W P)
    (hWm : ∀ s, StronglyMeasurable (W s)) (hWc : ∀ ω, Continuous (W · ω)) (t : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ t, a ≤ W s ω} ≤ 2 * P {ω | a ≤ W t ω} := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨u, hu_mono, hu_lt, hu_tend⟩ := exists_seq_strictMono_tendsto a
  have hF_inter : (⋂ m, {ω | ∃ s ≤ t, u m < W s ω}) = {ω | ∃ s ≤ t, a ≤ W s ω} := by
    ext ω; simp only [mem_iInter, mem_ofPred_eq]
    refine ⟨fun h ↦ ?_, fun ⟨s, hst, hs⟩ m ↦ ⟨s, hst, (hu_lt m).trans_le hs⟩⟩
    obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ t)) (hWc ω).continuousOn
    exact ⟨r, hr.2, le_of_tendsto hu_tend (.of_forall fun m ↦
      let ⟨s, hst, hs⟩ := h m; hs.le.trans (hmax ⟨bot_le, hst⟩))⟩
  have hG_inter : (⋂ m, {ω | u m < W t ω}) = {ω | a ≤ W t ω} := by
    ext ω; exact ⟨fun h ↦ le_of_tendsto hu_tend (.of_forall fun m ↦ (mem_iInter.mp h m).le),
      fun h ↦ mem_iInter.mpr fun m ↦ (hu_lt m).trans_le h⟩
  rw [← hF_inter, ← hG_inter]
  exact le_of_tendsto_of_tendsto (tendsto_measure_iInter_atTop
      (fun _ ↦ (measurableSet_exists_le_gt (fun s ↦ (hWm s).measurable) hWc t _).nullMeasurableSet)
      (fun _ _ hm _ ⟨s, hst, hs⟩ ↦ ⟨s, hst, (hu_mono.monotone hm).trans_lt hs⟩)
      ⟨0, measure_ne_top P _⟩)
    (ENNReal.Tendsto.const_mul (tendsto_measure_iInter_atTop
      (fun _ ↦ (measurableSet_lt measurable_const (hWm t).measurable).nullMeasurableSet)
      (fun _ _ hm _ hω ↦ (hu_mono.monotone hm).trans_lt hω)
      ⟨0, measure_ne_top P _⟩) (Or.inr ENNReal.ofNat_ne_top))
    (.of_forall fun _ ↦ measure_exists_le_gt_le_of_continuous hW hWc t _)

private def dyadicCrossingSet (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a δ : ℝ) (n : ℕ) (i : Fin (2 ^ n + 1)) :
    Set Ω := {ω | (∀ j < i, W (dyadicTime t n j) ω < a) ∧
      a ≤ W (dyadicTime t n i) ω ∧ W (dyadicTime t n i) ω < a + δ}

private theorem subset_dyadicCrossing_union_osc (hW0 : ∀ ω, W 0 ω = 0) (t : ℝ≥0) {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (n : ℕ) :
    {ω | a + δ ≤ W t ω} ⊆ (⋃ i, dyadicCrossingSet W t a δ n i ∩ {ω | a + δ ≤ W t ω}) ∪
      {ω | ∃ k : Fin (2 ^ n),
        δ ≤ |W (dyadicTime t n k.succ) ω - W (dyadicTime t n k.castSucc) ω|} := by
  let g := dyadicTime t n; intro ω (hω : a + δ ≤ W t ω)
  by_cases hosc : ∃ k : Fin (2 ^ n), δ ≤ |W (g k.succ) ω - W (g k.castSucc) ω|
  · exact Or.inr hosc
  · refine Or.inl (mem_iUnion.mpr ?_); classical
    have hex : ∃ j, a ≤ W (g j) ω := ⟨.last _, by simp only [g, dyadicTime_last]; linarith⟩
    obtain ⟨k, hk⟩ := Fin.eq_succ_of_ne_zero (i := Fin.find _ hex) fun h0 ↦
      ha.not_ge <| by simpa [g, h0, hW0] using Fin.find_spec hex
    refine ⟨k.succ, ⟨fun j hj ↦ not_le.mp (Fin.find_min hex (hk ▸ hj)), hk ▸ Fin.find_spec hex,
      ?_⟩, hω⟩
    have := not_le.mp (Fin.find_min hex (hk ▸ k.castSucc_lt_succ))
    have := (abs_lt.mp (not_le.mp fun hle ↦ hosc ⟨k, hle⟩)).2; linarith

private theorem measurableSet_dyadicCrossingSet (hWm : ∀ s, StronglyMeasurable (W s)) (t : ℝ≥0)
    (a δ : ℝ) (n : ℕ) (i : Fin (2 ^ n + 1)) :
    MeasurableSet[Filtration.natural W hWm (dyadicTime t n i)]
      (dyadicCrossingSet W t a δ n i) := by
  let ℱ := Filtration.natural W hWm; have hAd := (Filtration.stronglyAdapted_natural hWm).adapted
  simp only [dyadicCrossingSet, ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun (hji : j < i) ↦ measurableSet_lt
    ((hAd _).mono (ℱ.mono (dyadicTime_monotone t n hji.le)) le_rfl) measurable_const).inter
    ((measurableSet_le measurable_const (hAd _)).inter (measurableSet_lt (hAd _) measurable_const))

private theorem two_mul_measure_add_ge_le_step (hW : IsPreBrownianReal W P)
    (hWm : ∀ s, StronglyMeasurable (W s)) (hW0 : ∀ ω, W 0 ω = 0) (t : ℝ≥0) {a δ : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (n : ℕ) : 2 * P {ω | a + δ ≤ W t ω} ≤ P {ω | ∃ s ≤ t, a ≤ W s ω} +
      2 * P {ω | ∃ k : Fin (2 ^ n),
        δ ≤ |W (dyadicTime t n k.succ) ω - W (dyadicTime t n k.castSucc) ω|} := by
  let ℱ := Filtration.natural W hWm; have hWF := hW.isFilteredPreBrownianReal_natural hWm
  let g := dyadicTime t n; let N : Fin (2 ^ n + 1) := Fin.last (2 ^ n)
  let Osc : Set Ω := {ω | ∃ k : Fin (2 ^ n), δ ≤ |W (g k.succ) ω - W (g k.castSucc) ω|}
  let A := dyadicCrossingSet W t a δ n; let D i := A i ∩ {ω | a + δ ≤ W t ω}
  have hA_meas := measurableSet_dyadicCrossingSet hWm t a δ n
  have hA_disj : Pairwise fun i k ↦ Disjoint (A i) (A k) := fun i k hik ↦
    disjoint_left.mpr fun ω hi hk ↦ (lt_trichotomy i k).elim (fun h ↦ hi.2.1.not_gt (hk.1 i h))
      fun h ↦ h.elim hik fun h' ↦ hk.2.1.not_gt (hi.1 k h')
  have hbound (i : Fin (2 ^ n + 1)) : 2 * P (D i) ≤ P (A i) := by
    let E : Set Ω := (W (g N) - W (g i)) ⁻¹' Ioi 0
    have hsub : D i ⊆ E ∩ A i := fun ω ⟨hA, (hWt : a + δ ≤ W t ω)⟩ ↦
      ⟨sub_pos.mpr (hA.2.2.trans_le (by simpa only [g, N, dyadicTime_last] using hWt)), hA⟩
    calc 2 * P (D i) ≤ 2 * P (E ∩ A i) := by gcongr
      _ = (2 * gaussianReal 0 (g N - g i) (Ioi 0)) * P (A i) := by
          rw [(Indep_iff _ _ _).mp (hWF.indep_sub (dyadicTime_monotone t n (Fin.le_last i)))
            E (A i) ⟨Ioi 0, measurableSet_Ioi, rfl⟩ (hA_meas i), mul_assoc]
          congr 2
          exact (hW.hasLaw_sub_of_le (dyadicTime_monotone t n (Fin.le_last i))).measure_eq
            (p := (· ∈ Ioi 0)) measurableSet_Ioi
      _ ≤ (2 * 2⁻¹) * P (A i) := by gcongr; exact (gaussianReal 0 _).measure_Ioi_zero_le_inv_two
      _ = P (A i) := by rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  calc 2 * P {ω | a + δ ≤ W t ω} ≤ 2 * (P (⋃ i, D i) + P Osc) := by
        gcongr; exact (measure_mono (subset_dyadicCrossing_union_osc hW0 t ha hδ n)).trans
          (measure_union_le _ _)
    _ = (∑ i, 2 * P (D i)) + 2 * P Osc := by
        rw [mul_add, measure_iUnion (fun i k hik ↦ (hA_disj hik).mono inter_subset_left
          inter_subset_left) (fun i ↦ (ℱ.le (g i) _ (hA_meas i)).inter
            (measurableSet_le measurable_const (hWm t).measurable)), tsum_fintype, Finset.mul_sum]
    _ ≤ (∑ i, P (A i)) + 2 * P Osc := by gcongr with i; exact hbound i
    _ = P (⋃ i, A i) + 2 * P Osc := by
        rw [measure_iUnion hA_disj (fun i ↦ ℱ.le (g i) _ (hA_meas i)), tsum_fintype]
    _ ≤ P {ω | ∃ s ≤ t, a ≤ W s ω} + 2 * P Osc := by
        gcongr; exact iUnion_subset fun i _ h ↦ ⟨g i, dyadicTime_le t n i, h.2.1⟩

private theorem measure_exists_le_ge_of_continuous (hW : IsPreBrownianReal W P)
    (hWm : ∀ s, StronglyMeasurable (W s)) (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0)
    (t : ℝ≥0) {a : ℝ} (ha : 0 < a) : P {ω | ∃ s ≤ t, a ≤ W s ω} = 2 * P {ω | a ≤ W t ω} := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine le_antisymm (measure_exists_le_ge_le_of_continuous hW hWm hWc t a) ?_
  have hδ_bound {δ : ℝ} (hδ : 0 < δ) : 2 * P {ω | a + δ ≤ W t ω} ≤ P {ω | ∃ s ≤ t, a ≤ W s ω} := by
    have hosc := ENNReal.Tendsto.const_mul (tendsto_measure_exists_abs_sub_dyadicTime_ge P
      (fun s ↦ (hWm s).measurable.aemeasurable) (.of_forall hWc) t hδ)
      (a := 2) (Or.inr ENNReal.ofNat_ne_top)
    simpa only [mul_zero, add_zero] using ge_of_tendsto
      ((tendsto_const_nhds (x := P {ω | ∃ s ≤ t, a ≤ W s ω})).add hosc)
      (.of_forall fun n ↦ two_mul_measure_add_ge_le_step hW hWm hW0 t ha hδ n)
  obtain ⟨u, hu_anti, hu_gt, hu_tend⟩ := exists_seq_strictAnti_tendsto a
  have hGt : {ω | a < W t ω} = ⋃ m, {ω | u m ≤ W t ω} :=
    (congrArg (W t ⁻¹' ·) (iUnion_Ici_eq_Ioi_of_lt_of_tendsto hu_gt hu_tend)).symm.trans
      preimage_iUnion
  rw [hW.measure_eval_ge_eq_measure_eval_gt (.inr ha.ne'), hGt]
  refine le_of_tendsto' (ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop (μ := P)
    fun _ _ hm _ hω ↦ (hu_anti.antitone hm).trans hω) (Or.inr ENNReal.ofNat_ne_top)) fun m ↦ ?_
  simpa only [Function.comp_apply, add_sub_cancel] using hδ_bound (sub_pos.mpr (hu_gt m))

end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For any real level `a` and time `t`, the probability that a real Brownian motion strictly
exceeds `a` by time `t` is at most twice `P {ω | a < B t ω}`. -/
theorem measure_exists_le_gt_le (hB : IsBrownianReal B P) (t : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ t, a < B s ω} ≤ 2 * P {ω | a < B t ω} := by
  obtain ⟨W, _, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  exact (measure_congr (hWB.symm.ae_eq.preimage {f | ∃ s ≤ t, a < f s})).trans_le <|
    (measure_exists_le_gt_le_of_continuous hW.toIsPreBrownianReal hWc t a).trans_eq
      (congrArg (2 * ·) (measure_congr ((hWB.symm.ae_eq_eval t).preimage (Ioi a))).symm)

/-- For any real level `a` and time `t`, the probability that a real Brownian motion attains a
value at least `a` at some time `s ≤ t` is at most twice `P {ω | a ≤ B t ω}`. -/
theorem measure_exists_le_ge_le (hB : IsBrownianReal B P) (t : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ t, a ≤ B s ω} ≤ 2 * P {ω | a ≤ B t ω} := by
  obtain ⟨W, hWm, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  exact (measure_congr (hWB.symm.ae_eq.preimage {f | ∃ s ≤ t, a ≤ f s})).trans_le <|
    (measure_exists_le_ge_le_of_continuous hW.toIsPreBrownianReal hWm hWc t a).trans_eq
      (congrArg (2 * ·) (measure_congr ((hWB.symm.ae_eq_eval t).preimage (Ici a))).symm)

/-- Strict crossing below `a` by time `t` has probability at most `2 * P {ω | B t ω < a}`. -/
theorem measure_exists_le_lt_le (hB : IsBrownianReal B P) (t : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ t, B s ω < a} ≤ 2 * P {ω | B t ω < a} := by
  simpa only [Pi.neg_apply, neg_lt_neg_iff] using hB.neg.measure_exists_le_gt_le t (-a)

/-- Reaching at or below `a` by time `t` has probability at most `2 * P {ω | B t ω ≤ a}`. -/
theorem measure_exists_le_le_le (hB : IsBrownianReal B P) (t : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ t, B s ω ≤ a} ≤ 2 * P {ω | B t ω ≤ a} := by
  simpa only [Pi.neg_apply, neg_le_neg_iff] using hB.neg.measure_exists_le_ge_le t (-a)

/-- **Reflection principle for real Brownian motion**: for every positive level `a > 0` and time
`t ≥ 0` (including `t = 0`, where both sides vanish), the probability of reaching `a` by time `t`
equals twice the probability of lying at or above `a` at time `t`. -/
theorem measure_exists_le_ge (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ s ≤ t, a ≤ B s ω} = 2 * P {ω | a ≤ B t ω} := by
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  exact (measure_congr (hWB.symm.ae_eq.preimage {f | ∃ s ≤ t, a ≤ f s})).trans <|
    (measure_exists_le_ge_of_continuous hW.toIsPreBrownianReal hWm hWc hW0 t ha).trans
      (congrArg (2 * ·) (measure_congr ((hWB.symm.ae_eq_eval t).preimage (Ici a))).symm)

/-- Real-valued form of the Brownian reflection principle for `a > 0`. -/
theorem measureReal_exists_le_ge (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ s ≤ t, a ≤ B s ω} = 2 * P.real {ω | a ≤ B t ω} := by
  simp [measureReal_def, hB.measure_exists_le_ge t ha]

/-- Strict-exceedance reflection principle for every nonnegative level `a ≥ 0` and time `t ≥ 0`. -/
theorem measure_exists_le_gt (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | ∃ s ≤ t, a < B s ω} = 2 * P {ω | a < B t ω} := by
  obtain ⟨u, hu_anti, hu_gt, hu_tend⟩ := exists_seq_strictAnti_tendsto a
  have hSup : {ω | ∃ s ≤ t, a < B s ω} = ⋃ m, {ω | ∃ s ≤ t, u m ≤ B s ω} := by
    ext ω; simp only [← mem_Ioi, ← iUnion_Ici_eq_Ioi_of_lt_of_tendsto hu_gt hu_tend, mem_iUnion,
      mem_Ici, mem_ofPred_eq]
    exact (exists_congr fun _ ↦ exists_and_left.symm).trans exists_comm
  have hGt : {ω | a < B t ω} = ⋃ m, {ω | u m ≤ B t ω} :=
    (congrArg (B t ⁻¹' ·) (iUnion_Ici_eq_Ioi_of_lt_of_tendsto hu_gt hu_tend)).symm.trans
      preimage_iUnion
  rw [hSup, hGt]
  exact tendsto_nhds_unique (tendsto_measure_iUnion_atTop (μ := P) fun _ _ hm _ ⟨s, hst, hs⟩ ↦
      ⟨s, hst, (hu_anti.antitone hm).trans hs⟩)
    ((ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop (μ := P) fun _ _ hm _ hω ↦
        (hu_anti.antitone hm).trans hω) (a := 2) (Or.inr ENNReal.ofNat_ne_top)).congr fun m ↦
      (hB.measure_exists_le_ge t (ha.trans_lt (hu_gt m))).symm)

/-- Real-valued strict-exceedance reflection principle for `a ≥ 0`. -/
theorem measureReal_exists_le_gt (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | ∃ s ≤ t, a < B s ω} = 2 * P.real {ω | a < B t ω} := by
  simp [measureReal_def, hB.measure_exists_le_gt t ha]

/-- Reflection principle for reaching a negative level `a < 0` by time `t`. -/
theorem measure_exists_le_le (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : a < 0) :
    P {ω | ∃ s ≤ t, B s ω ≤ a} = 2 * P {ω | B t ω ≤ a} := by
  simpa only [Pi.neg_apply, neg_le_neg_iff] using hB.neg.measure_exists_le_ge t (neg_pos.mpr ha)

/-- Real-valued reflection principle for reaching a negative level `a < 0` by time `t`. -/
theorem measureReal_exists_le_le (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : a < 0) :
    P.real {ω | ∃ s ≤ t, B s ω ≤ a} = 2 * P.real {ω | B t ω ≤ a} := by
  simp [measureReal_def, hB.measure_exists_le_le t ha]

/-- Strict-crossing reflection principle below any nonpositive level `a ≤ 0` by time `t`. -/
theorem measure_exists_le_lt (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : a ≤ 0) :
    P {ω | ∃ s ≤ t, B s ω < a} = 2 * P {ω | B t ω < a} := by
  simpa only [Pi.neg_apply, neg_lt_neg_iff] using hB.neg.measure_exists_le_gt t (neg_nonneg.mpr ha)

/-- Real-valued strict-crossing reflection principle below any nonpositive level `a ≤ 0` by `t`. -/
theorem measureReal_exists_le_lt (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : a ≤ 0) :
    P.real {ω | ∃ s ≤ t, B s ω < a} = 2 * P.real {ω | B t ω < a} := by
  simp [measureReal_def, hB.measure_exists_le_lt t ha]

/-- **Immediate positive crossing**: a real Brownian motion enters `(0, ∞)` immediately after `0`
almost surely. -/
theorem hittingAfter_Ioi_zero_ae_eq_zero (hB : IsBrownianReal B P) :
    hittingAfter B (Ioi 0) 0 =ᵐ[P] 0 := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  refine (hWB.symm.hittingAfter_ae_eq (Ioi 0) 0).trans ?_
  have hstep (m : ℕ) : ∀ᵐ ω ∂P, ∃ s ≤ (1 / (m + 1 : ℝ≥0)), 0 < W s ω := by
    let tm : ℝ≥0 := 1 / (m + 1)
    rw [ae_iff, ← compl_ofPred, prob_compl_eq_zero_iff (measurableSet_exists_le_gt
        (fun s ↦ (hWm s).measurable) hWc tm 0), hW.measure_exists_le_gt tm le_rfl,
      (hW.hasLaw_eval tm).measure_eq (p := (0 < ·)) measurableSet_Ioi, Ioi_def,
      gaussianReal_zero_Ioi_zero (one_div_ne_zero (Nat.cast_add_one_ne_zero m)),
      ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]
  have htend : Tendsto (fun m : ℕ ↦ ((1 / (m + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)) atTop
      (𝓝 ((0 : ℝ≥0) : WithTop ℝ≥0)) := (WithTop.continuous_coe.tendsto 0).comp <|
    NNReal.tendsto_coe.mp <| by simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  filter_upwards [ae_all_iff.mpr hstep] with ω hω
  exact le_antisymm (ge_of_tendsto htend (.of_forall fun m ↦ let ⟨s, hsm, hs0⟩ := hω m
    (hittingAfter_le_of_mem (bot_le : 0 ≤ s) hs0).trans (WithTop.coe_le_coe.mpr hsm))) bot_le

/-- **Immediate negative crossing**: a real Brownian motion enters `(-∞, 0)` immediately after `0`
almost surely. -/
theorem hittingAfter_Iio_zero_ae_eq_zero (hB : IsBrownianReal B P) :
    hittingAfter B (Iio 0) 0 =ᵐ[P] 0 := by
  simpa only [hittingAfter_neg, Set.neg_preimage, Set.neg_Ioi, neg_zero] using
    hB.neg.hittingAfter_Ioi_zero_ae_eq_zero

/-- For every time `t ≥ 0` (including `t = 0`), the running maximum `⨆ s : Set.Iic t, B s ω` of a
real Brownian motion has the same law as `|B t|`, namely `(gaussianReal 0 t).map (|·|)`. -/
theorem hasLaw_iSup_Iic_map_abs (hB : IsBrownianReal B P) (t : ℝ≥0) :
    HasLaw (fun ω ↦ ⨆ s : Iic t, B s ω) ((gaussianReal 0 t).map (|·|)) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  have : Nonempty (Iic t) := ⟨⟨0, mem_Iic.mpr bot_le⟩⟩
  have : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (Icc_bot (a := t) ▸ isCompact_Icc)
  let M : Ω → ℝ := fun ω ↦ ⨆ s : Iic t, W s ω
  have hbdd (ω : Ω) : BddAbove (range fun s : Iic t ↦ W s ω) :=
    (isCompact_range ((hWc ω).comp continuous_subtypeVal)).bddAbove
  have hM_le (x : ℝ) : M ⁻¹' Iic x = {ω | ∃ s ≤ t, x < W s ω}ᶜ := by
    ext ω; simp only [M, mem_preimage, mem_Iic, mem_compl_iff, mem_ofPred_eq,
      ciSup_le_iff (hbdd ω), Subtype.forall, not_exists, not_and, not_lt]
  have hM_meas : Measurable M := measurable_of_Iic fun x ↦
    hM_le x ▸ (measurableSet_exists_le_gt (fun s ↦ (hWm s).measurable) hWc t x).compl
  have hMB_ae : M =ᵐ[P] fun ω ↦ ⨆ s : Iic t, B s ω := hWB.mono fun _ hω ↦ by simp only [M, hω]
  refine ⟨hM_meas.aemeasurable.congr hMB_ae, (Measure.map_congr hMB_ae.symm).trans ?_⟩
  have := (Measure.isProbabilityMeasure_map_iff hM_meas.aemeasurable).mpr ‹IsProbabilityMeasure P›
  have := (Measure.isProbabilityMeasure_map_iff continuous_abs.measurable.aemeasurable
    (μ := gaussianReal 0 t)).mpr inferInstance
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun x ↦ ?_)
  rcases lt_or_ge x 0 with hx | hx
  · rw [P.cdf_map M hM_meas.aemeasurable x, eq_empty_of_forall_notMem (s := M ⁻¹' Iic x) fun ω hω ↦
      (hx.trans_le ((hW0 ω).symm.trans_le (le_ciSup (hbdd ω) ⟨0, mem_Iic.mpr bot_le⟩))).not_ge hω,
      measureReal_empty, (gaussianReal 0 t).cdf_map_abs_of_neg hx]
  · rw [P.cdf_map M hM_meas.aemeasurable x, hM_le x,
      probReal_compl_eq_one_sub (measurableSet_exists_le_gt (fun s ↦ (hWm s).measurable) hWc t x),
      hW.measureReal_exists_le_gt t hx,
      (hW.hasLaw_eval t).measureReal_eq (p := (x < ·)) measurableSet_Ioi, Ioi_def,
      (gaussianReal 0 t).measureReal_Ioi_eq_one_sub_cdf x,
      (gaussianReal 0 t).cdf_map_abs_of_isNegInvariant hx]; ring

/-- At positive time `t ≠ 0`, `⨆ s : Set.Iic t, B s ω` has law `foldedNormalMeasure 0 √t`. -/
theorem hasLaw_iSup_Iic (hB : IsBrownianReal B P) {t : ℝ≥0} (ht : t ≠ 0) :
    HasLaw (fun ω ↦ ⨆ s : Iic t, B s ω) (foldedNormalMeasure 0 √(t : ℝ)) P :=
  gaussianReal_map_abs_eq_foldedNormalMeasure 0 ht ▸ hB.hasLaw_iSup_Iic_map_abs t

end ProbabilityTheory.IsBrownianReal
