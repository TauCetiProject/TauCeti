/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Gap
public import TauCeti.Probability.PointProcess.Poisson.OccurrenceTime
public import TauCeti.Probability.Distributions.Exponential.Basic
public import Mathlib.Probability.Independence.InfinitePi

import Mathlib.MeasureTheory.Function.Floor
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.MeasureTheory.MeasurableSpace.StrictMono
import TauCeti.MeasureTheory.Measure.Interval
import TauCeti.MeasureTheory.Measure.StrictMono
import TauCeti.Probability.Distributions.Exponential.PartialSum
import TauCeti.Probability.PointProcess.Poisson.Count
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.PointProcess.Poisson.Simplicity
import TauCeti.Probability.Independence.Basic

/-!
# Exponential interarrival gaps of a homogeneous Poisson random measure

For a homogeneous temporal Poisson random measure `N` of positive rate `r` on `ℝ≥0`, the
interarrival gaps `(N ω).occurrenceGap n` are mutually independent exponential random variables
of rate `r`. Equivalently, each finite prefix of finite occurrence-time representatives
`((N ω).occurrenceTime i).toNNReal` has the law of the cumulative sums of `m` independent
`nnrealExpMeasure r` variables, and the full gap sequence has the countable product law
`Measure.infinitePi`.

At rate zero, the random measure vanishes almost surely, so every extended interarrival gap is
almost surely infinite. Because almost surely constant coordinates are independent, mutual
independence of the interarrival gaps holds for every rate `r : ℝ≥0`, without a positivity side
condition.

Rather than changing variables via Lebesgue Jacobians on open simplices, the proof compares
the finite-prefix occurrence-time law and the exponential cumulative-sum law directly on the
strictly increasing positive chamber using `MeasureTheory.Measure.ext_of_Ioc_strictMono`. On
any separated half-open box `∏ᵢ (aᵢ, bᵢ]`, cumulative-count squeezing rewrites membership of
the occurrence times into independent Poisson counts on `2m` disjoint intervals, whose
product matches `TauCeti.Probability.map_sum_Iic_pi_nnrealExpMeasure_univ_pi_Ioc`.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapter 7.
* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4.
-/

public section

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

section Helpers

-- Successive differences recovering increments from nonempty prefix sums.
private def gapOfPartialSum (m : ℕ) (s : Fin m → ℝ≥0) (i : Fin m) : ℝ≥0 :=
  s i - (Fin.cons 0 s : Fin (m + 1) → ℝ≥0) i.castSucc

@[fun_prop]
private lemma measurable_gapOfPartialSum (m : ℕ) : Measurable (gapOfPartialSum m) := by
  refine measurable_pi_iff.mpr fun i => (measurable_pi_apply i).sub ?_
  cases m with
  | zero => exact i.elim0
  | succ k =>
    cases i using Fin.cases with
    | zero => simp [measurable_const]
    | succ j => simpa [Fin.castSucc_succ] using measurable_pi_apply j.castSucc

private lemma gapOfPartialSum_comp_sum_Iic (m : ℕ) :
    gapOfPartialSum m ∘ (fun (x : Fin m → ℝ≥0) (i : Fin m) => ∑ j ∈ Finset.Iic i, x j) = id := by
  funext x i
  cases m with
  | zero => exact i.elim0
  | succ k =>
    have hcons : (Fin.cons 0 (fun j : Fin (k + 1) => ∑ l ∈ Finset.Iic j, x l) :
        Fin (k + 2) → ℝ≥0) i.castSucc = Fin.partialSum x i.castSucc := by
      cases i using Fin.cases <;> simp [Fin.partialSum_succ_eq_sum_Iic]
    rw [Function.comp_apply, id_eq, gapOfPartialSum, hcons,
      ← Fin.partialSum_succ_eq_sum_Iic, Fin.partialSum_succ, add_tsub_cancel_left]

private def prevEndpoint {k : ℕ} (b : Fin (k + 1) → ℝ≥0) : Fin (k + 1) → ℝ≥0 :=
  Fin.cases 0 fun j : Fin k => b j.castSucc

private lemma prevEndpoint_le_of_separated {k : ℕ} {a b : Fin (k + 1) → ℝ≥0}
    (hsep : IsSeparatedBox a b) (i : Fin (k + 1)) : prevEndpoint b i ≤ a i := by
  cases i using Fin.cases with
  | zero => exact zero_le
  | succ j => exact hsep.le_of_lt j.castSucc_lt_succ

private lemma le_prevEndpoint_of_lt {k : ℕ} {a b : Fin (k + 1) → ℝ≥0}
    (hsep : IsSeparatedBox a b) {i i' : Fin (k + 1)} (h : i < i') :
    b i ≤ prevEndpoint b i' := by
  cases i' using Fin.cases with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ j =>
    simp only [prevEndpoint, Fin.cases_succ]
    rcases lt_or_eq_of_le (Fin.le_castSucc_iff.mpr h) with hij | rfl
    · exact (hsep.le_of_lt hij).trans (hsep.le j.castSucc)
    · exact le_rfl

private def separatedBoxIntervals {k : ℕ} (a b : Fin (k + 1) → ℝ≥0) :
    Fin (k + 1) ⊕ Fin (k + 1) → Set ℝ≥0 :=
  Sum.elim (fun i => Ioc (prevEndpoint b i) (a i)) (fun i => Ioc (a i) (b i))

private noncomputable def separatedBoxFloorCount {Ω : Type*} (N : Ω → Measure ℝ≥0)
    {k : ℕ} (a b : Fin (k + 1) → ℝ≥0) (u : Fin (k + 1) ⊕ Fin (k + 1)) (ω : Ω) : ℕ :=
  ⌊(N ω (separatedBoxIntervals a b u)).toNNReal⌋₊

private lemma pairwise_disjoint_separatedIntervals {k : ℕ} {a b : Fin (k + 1) → ℝ≥0}
    (hsep : IsSeparatedBox a b) :
    Pairwise (Disjoint on separatedBoxIntervals a b) := by
  intro u v huv
  cases u with
  | inl i =>
    cases v with
    | inl i' =>
      have hii' : i ≠ i' := fun h => huv (congrArg Sum.inl h)
      rcases lt_or_gt_of_ne hii' with hlt | hlt
      · exact Ioc_disjoint_Ioc_of_le ((hsep.le i).trans (le_prevEndpoint_of_lt hsep hlt))
      · exact (Ioc_disjoint_Ioc_of_le ((hsep.le i').trans (le_prevEndpoint_of_lt hsep hlt))).symm
    | inr i' =>
      rcases le_or_gt i i' with hle | hlt
      · have ha : a i ≤ a i' := by
          rcases lt_or_eq_of_le hle with hlt | rfl
          · exact (hsep.le i).trans
              ((le_prevEndpoint_of_lt hsep hlt).trans (prevEndpoint_le_of_separated hsep i'))
          · exact le_rfl
        exact Ioc_disjoint_Ioc_of_le ha
      · exact (Ioc_disjoint_Ioc_of_le (le_prevEndpoint_of_lt hsep hlt)).symm
  | inr i =>
    cases v with
    | inl i' =>
      rcases le_or_gt i' i with hle | hlt
      · have ha : a i' ≤ a i := by
          rcases lt_or_eq_of_le hle with hlt | rfl
          · exact (hsep.le i').trans
              ((le_prevEndpoint_of_lt hsep hlt).trans (prevEndpoint_le_of_separated hsep i))
          · exact le_rfl
        exact (Ioc_disjoint_Ioc_of_le ha).symm
      · exact Ioc_disjoint_Ioc_of_le (le_prevEndpoint_of_lt hsep hlt)
    | inr i' =>
      have hii' : i ≠ i' := fun h => huv (congrArg Sum.inr h)
      rcases lt_or_gt_of_ne hii' with hlt | hlt
      · exact Ioc_disjoint_Ioc_of_le (hsep.le_of_lt hlt)
      · exact (Ioc_disjoint_Ioc_of_le (hsep.le_of_lt hlt)).symm

-- Cumulative-count squeezing: `(μ.occurrenceTime i).toNNReal ∈ (a i, b i]` means `μ (0, a i] ≤ i`
-- and `i + 1 ≤ μ (0, b i]`. Because `b j ≤ a (j + 1)` for a separated box, monotonicity squeezes
-- `j + 1 ≤ μ (0, b j] ≤ μ (0, a (j + 1)] ≤ j + 1`, forcing `μ (0, a i] = i` for every `i`.
private lemma forall_toNNReal_occurrenceTime_mem_Ioc_iff_cumulative {k : ℕ} {μ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure μ] (hμ : μ.IsIntegerValued) (h0 : μ {0} = 0)
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    (∀ i : Fin (k + 1), (μ.occurrenceTime i).toNNReal ∈ Ioc (a i) (b i)) ↔
      (∀ i : Fin (k + 1), μ (Ioc 0 (a i)) = (i : ℕ)) ∧
      (∀ i : Fin (k + 1), ((i : ℕ) + 1 : ℝ≥0∞) ≤ μ (Ioc 0 (b i))) := by
  have hIoc_eq (t : ℝ≥0) : μ (Ioc 0 t) = μ (Iic t) := by
    rw [← bot_eq_zero]
    exact measure_Ioc_bot_eq_measure_Iic (by rwa [bot_eq_zero]) t
  constructor
  · intro hmem
    have hne (i : Fin (k + 1)) : μ.occurrenceTime i ≠ ∞ := by
      intro htop
      have := (hmem i).1
      simp [htop] at this
    have hlow (i : Fin (k + 1)) : ((i : ℕ) + 1 : ℝ≥0∞) ≤ μ (Ioc 0 (b i)) := by
      rw [hIoc_eq, ← μ.occurrenceTime_le_iff,
        ← ENNReal.coe_toNNReal (hne i), ENNReal.coe_le_coe]
      exact (hmem i).2
    have hhigh (i : Fin (k + 1)) : μ (Ioc 0 (a i)) ≤ (i : ℕ) := by
      have hlt : μ (Ioc 0 (a i)) < (i : ℕ) + 1 := by
        rw [hIoc_eq, ← not_le, ← μ.occurrenceTime_le_iff, not_le,
          ← ENNReal.coe_toNNReal (hne i), ENNReal.coe_lt_coe]
        exact (hmem i).1
      obtain ⟨m, hm⟩ := hμ.exists_eq_natCast measurableSet_Ioc measure_Ioc_lt_top
      rw [hm] at hlt ⊢
      norm_cast at hlt ⊢
      omega
    refine ⟨fun i => ?_, hlow⟩
    cases i using Fin.cases with
    | zero => simpa using hhigh 0
    | succ j =>
      have hmono : μ (Ioc 0 (b j.castSucc)) ≤ μ (Ioc 0 (a j.succ)) :=
        measure_mono (Ioc_subset_Ioc_right (hsep.le_of_lt j.castSucc_lt_succ))
      have h1 := hlow j.castSucc
      have h2 := hhigh j.succ
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h1 h2 ⊢
      exact le_antisymm h2 (h1.trans hmono)
  · rintro ⟨hai, hbi⟩ i
    have hle_b : μ.occurrenceTime i ≤ b i := by
      rw [μ.occurrenceTime_le_iff, ← hIoc_eq]
      exact hbi i
    have hne : μ.occurrenceTime i ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle_b
    have hnot_le_a : ¬ μ.occurrenceTime i ≤ a i := by
      rw [μ.occurrenceTime_le_iff, ← hIoc_eq, hai i, not_le]
      norm_cast
      omega
    exact ⟨by rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hne]; exact not_le.mp hnot_le_a,
      by rwa [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]⟩

-- Rewrites cumulative counts `μ (0, a i] = i` and `μ (0, b i] ≥ i + 1` into exact/lower-bound
-- counts on the `2(k + 1)` disjoint intervals `(prevEndpoint b i, a i]` and `(a i, b i]`.
private lemma cumulative_Ioc_iff_disjoint_Ioc {k : ℕ} {μ : Measure ℝ≥0}
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    ((∀ i : Fin (k + 1), μ (Ioc 0 (a i)) = (i : ℕ)) ∧
      (∀ i : Fin (k + 1), ((i : ℕ) + 1 : ℝ≥0∞) ≤ μ (Ioc 0 (b i)))) ↔
      (∀ i : Fin (k + 1), μ (Ioc (prevEndpoint b i) (a i)) = 0) ∧
      (∀ j : Fin k, μ (Ioc (a j.castSucc) (b j.castSucc)) = 1) ∧
      1 ≤ μ (Ioc (a (Fin.last k)) (b (Fin.last k))) := by
  constructor
  · rintro ⟨hai, hbi⟩
    have hbj (j : Fin k) : μ (Ioc 0 (b j.castSucc)) = (j : ℕ) + 1 := by
      have hmono : μ (Ioc 0 (b j.castSucc)) ≤ μ (Ioc 0 (a j.succ)) :=
        measure_mono (Ioc_subset_Ioc_right (hsep.le_of_lt j.castSucc_lt_succ))
      have h1 := hbi j.castSucc
      have h2 := hai j.succ
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h1 h2 ⊢
      exact le_antisymm (h2 ▸ hmono) h1
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · cases i using Fin.cases with
      | zero => simpa [prevEndpoint] using hai 0
      | succ j =>
        have hadd := measure_Ioc_add_measure_Ioc (μ := μ) zero_le (hsep.le_of_lt j.castSucc_lt_succ)
        have hai_succ := hai j.succ
        simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at hai_succ
        rw [hbj j, hai_succ] at hadd
        simpa [prevEndpoint] using
          (ENNReal.add_right_inj (by finiteness)).mp (hadd.trans (add_zero _).symm)
    · have hadd := measure_Ioc_add_measure_Ioc (μ := μ) zero_le (hsep.le j.castSucc)
      rw [hai j.castSucc, hbj j, Fin.val_castSucc] at hadd
      exact (ENNReal.add_right_inj (ENNReal.natCast_ne_top j)).mp hadd
    · have hadd := measure_Ioc_add_measure_Ioc (μ := μ) zero_le (hsep.le (Fin.last k))
      have hlast := hbi (Fin.last k)
      rw [← hadd, hai (Fin.last k), Fin.val_last] at hlast
      exact (ENNReal.add_le_add_iff_left (ENNReal.natCast_ne_top k)).mp hlast
  · rintro ⟨hG, hJ, hlast⟩
    have hai (i : Fin (k + 1)) : μ (Ioc 0 (a i)) = (i : ℕ) := by
      induction i using Fin.induction with
      | zero => simpa [prevEndpoint] using hG 0
      | succ j ih =>
        have hb : μ (Ioc 0 (b j.castSucc)) = (j : ℕ) + 1 := by
          rw [← measure_Ioc_add_measure_Ioc zero_le (hsep.le j.castSucc), ih, hJ j,
            Fin.val_castSucc]
        rw [← measure_Ioc_add_measure_Ioc zero_le (hsep.le_of_lt j.castSucc_lt_succ), hb]
        simpa [prevEndpoint] using hG j.succ
    refine ⟨hai, fun i => ?_⟩
    cases i using Fin.lastCases with
    | last =>
      rw [← measure_Ioc_add_measure_Ioc zero_le (hsep.le (Fin.last k)), hai (Fin.last k),
        Fin.val_last]
      gcongr
    | cast j =>
      rw [← measure_Ioc_add_measure_Ioc zero_le (hsep.le j.castSucc), hai j.castSucc, hJ j]

private lemma forall_toNNReal_occurrenceTime_mem_Ioc_iff {k : ℕ} {μ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure μ] (hμ : μ.IsIntegerValued) (h0 : μ {0} = 0)
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    (∀ i : Fin (k + 1), (μ.occurrenceTime i).toNNReal ∈ Ioc (a i) (b i)) ↔
      (∀ i : Fin (k + 1), μ (Ioc (prevEndpoint b i) (a i)) = 0) ∧
      (∀ j : Fin k, μ (Ioc (a j.castSucc) (b j.castSucc)) = 1) ∧
      1 ≤ μ (Ioc (a (Fin.last k)) (b (Fin.last k))) :=
  (forall_toNNReal_occurrenceTime_mem_Ioc_iff_cumulative hμ h0 hsep).trans
    (cumulative_Ioc_iff_disjoint_Ioc hsep)

private lemma telescoping_separated_endpoints (k : ℕ) (a b : Fin (k + 1) → ℝ≥0) :
    (∑ i : Fin (k + 1), ((a i : ℝ) - prevEndpoint b i)) +
        (∑ j : Fin k, ((b j.castSucc : ℝ) - a j.castSucc)) =
      (a (Fin.last k) : ℝ) := by
  rw [Fin.sum_univ_succ]
  simp only [prevEndpoint, Fin.cases_zero, Fin.cases_succ, NNReal.coe_zero, sub_zero]
  rw [add_assoc, ← Finset.sum_add_distrib]
  simp_rw [sub_add_sub_cancel]
  rw [Fin.sum_univ_succ_sub_castSucc (fun i => (a i : ℝ))]
  ring

-- Telescopes the product of `2(k + 1)` Poisson exponential factors into `e^{-r a_k} - e^{-r b_k}`.
private lemma prod_exp_separated_endpoints (k : ℕ) (r : ℝ) (a b : Fin (k + 1) → ℝ≥0) :
    (∏ i : Fin (k + 1), Real.exp (-(r * ((a i : ℝ) - prevEndpoint b i)))) *
      ((∏ j : Fin k, Real.exp (-(r * ((b j.castSucc : ℝ) - a j.castSucc)))) *
        (∏ j : Fin k, r * ((b j.castSucc : ℝ) - a j.castSucc)) *
        (1 - Real.exp (-(r * ((b (Fin.last k) : ℝ) - a (Fin.last k)))))) =
      (∏ j : Fin k, r * ((b j.castSucc : ℝ) - a j.castSucc)) *
        (Real.exp (-(r * (a (Fin.last k) : ℝ))) - Real.exp (-(r * (b (Fin.last k) : ℝ)))) := by
  rw [← Real.exp_sum, ← Real.exp_sum]
  have hexp_sum :
      (∑ i : Fin (k + 1), -(r * ((a i : ℝ) - prevEndpoint b i))) +
        (∑ j : Fin k, -(r * ((b j.castSucc : ℝ) - a j.castSucc))) =
      -(r * (a (Fin.last k) : ℝ)) := by
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hmul := congrArg (r * ·) (telescoping_separated_endpoints k a b)
    linarith
  have hprod_exp :
      Real.exp (∑ i : Fin (k + 1), -(r * ((a i : ℝ) - prevEndpoint b i))) *
        Real.exp (∑ j : Fin k, -(r * ((b j.castSucc : ℝ) - a j.castSucc))) =
      Real.exp (-(r * (a (Fin.last k) : ℝ))) := by
    rw [← Real.exp_add, hexp_sum]
  have hexp_last :
      Real.exp (-(r * (a (Fin.last k) : ℝ))) *
        Real.exp (-(r * ((b (Fin.last k) : ℝ) - a (Fin.last k)))) =
      Real.exp (-(r * (b (Fin.last k) : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hring (P_prod E1 E2 E_diff : ℝ) :
      E1 * (E2 * P_prod * (1 - E_diff)) = P_prod * (E1 * E2 - E1 * E2 * E_diff) := by
    ring
  rw [hring, hprod_exp, hexp_last]

private def separatedBoxCountSets (k : ℕ) : Fin (k + 1) ⊕ Fin (k + 1) → Set ℕ :=
  Sum.elim (fun _ => {0}) (fun i => if i = Fin.last k then Ici 1 else {1})

private lemma preimage_occurrenceTime_separatedBox_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) {k : ℕ}
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    ((fun ω (i : Fin (k + 1)) => ((N ω).occurrenceTime i).toNNReal) ⁻¹'
      (univ.pi fun i => Ioc (a i) (b i))) =ᵐ[P]
      (⋂ u ∈ (Finset.univ : Finset (Fin (k + 1) ⊕ Fin (k + 1))),
        separatedBoxFloorCount N a b u ⁻¹' separatedBoxCountSets k u) := by
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  have hae_zero : ∀ᵐ ω ∂P, N ω {0} = 0 := h.ae_eq_zero (by simp)
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued, hae_zero] with ω hlf hint h0
  simp only [mem_preimage, mem_univ_pi, mem_iInter, Finset.mem_univ, forall_true_left,
    forall_toNNReal_occurrenceTime_mem_Ioc_iff hint h0 hsep, Sum.forall,
    separatedBoxFloorCount, separatedBoxIntervals, separatedBoxCountSets,
    Sum.elim_inl, Sum.elim_inr]
  have hfloor (s t : ℝ≥0) : (⌊(N ω (Ioc s t)).toNNReal⌋₊ : ℝ≥0∞) = N ω (Ioc s t) :=
    hint.natCast_natFloor_toNNReal measurableSet_Ioc measure_Ioc_lt_top
  constructor
  · rintro ⟨hG, hJ, hlast⟩
    refine ⟨fun i => Nat.cast_eq_zero.mp ((hfloor _ _).trans (hG i)), fun i => ?_⟩
    cases i using Fin.lastCases with
    | last =>
      simp only [ite_true, mem_Ici]
      exact Nat.one_le_cast.mp ((hfloor _ _).symm ▸ hlast)
    | cast j =>
      simpa [Fin.castSucc_ne_last] using Nat.cast_eq_one.mp ((hfloor _ _).trans (hJ j))
  · rintro ⟨hG, hJ⟩
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · rw [← hfloor]
      exact Nat.cast_eq_zero.mpr (hG i)
    · rw [← hfloor]
      exact Nat.cast_eq_one.mpr (by simpa [Fin.castSucc_ne_last] using hJ j.castSucc)
    · have hj : 1 ≤ ⌊(N ω (Ioc (a (Fin.last k)) (b (Fin.last k)))).toNNReal⌋₊ := by
        simpa only [ite_true, mem_Ici] using hJ (Fin.last k)
      rw [← hfloor]
      exact Nat.one_le_cast.mpr hj

-- Evaluates each Poisson count probability on the `2(k + 1)` disjoint intervals via
-- `HasLaw.measureReal_eq`, then telescopes the product via `prod_exp_separated_endpoints`.
private lemma prod_poisson_separatedBox_eq_boxFormula {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) {k : ℕ}
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    (∏ u : Fin (k + 1) ⊕ Fin (k + 1),
      P.real (separatedBoxFloorCount N a b u ⁻¹' separatedBoxCountSets k u)) =
      (∏ j : Fin k, (r : ℝ) * ((b j.castSucc : ℝ) - a j.castSucc)) *
        (Real.exp (-((r : ℝ) * a (Fin.last k))) - Real.exp (-((r : ℝ) * b (Fin.last k)))) := by
  let := h.isProbabilityMeasure
  -- Stage 1: evaluate the Poisson probability of each gap (`= 0`), interior box (`= 1`),
  -- and final box (`≥ 1`).
  have hG_val (i : Fin (k + 1)) :
      P.real (separatedBoxFloorCount N a b (Sum.inl i) ⁻¹'
          separatedBoxCountSets k (Sum.inl i)) =
        Real.exp (-((r : ℝ) * ((a i : ℝ) - prevEndpoint b i))) := by
    have hlaw := h.hasLaw_nat_count_Ioc_smul_nnvolume (prevEndpoint b i) (a i)
    dsimp only [Set.preimage, separatedBoxFloorCount, separatedBoxIntervals, separatedBoxCountSets,
      Sum.elim_inl]
    rw [hlaw.measureReal_eq (p := (· ∈ ({0} : Set ℕ))) MeasurableSet.of_discrete, ofPred_mem_eq,
      poissonMeasure_real_singleton_zero, NNReal.coe_mul,
      NNReal.coe_sub (prevEndpoint_le_of_separated hsep i)]
  have hJ_cast (j : Fin k) :
      P.real (separatedBoxFloorCount N a b (Sum.inr j.castSucc) ⁻¹'
          separatedBoxCountSets k (Sum.inr j.castSucc)) =
        Real.exp (-((r : ℝ) * ((b j.castSucc : ℝ) - a j.castSucc))) *
          ((r : ℝ) * ((b j.castSucc : ℝ) - a j.castSucc)) := by
    have hlaw := h.hasLaw_nat_count_Ioc_smul_nnvolume (a j.castSucc) (b j.castSucc)
    dsimp only [Set.preimage, separatedBoxFloorCount, separatedBoxIntervals, separatedBoxCountSets,
      Sum.elim_inr]
    rw [ite_eq_right (Fin.castSucc_ne_last j),
      hlaw.measureReal_eq (p := (· ∈ ({1} : Set ℕ))) MeasurableSet.of_discrete, ofPred_mem_eq,
      poissonMeasure_real_singleton]
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, NNReal.coe_mul,
      NNReal.coe_sub (hsep.le j.castSucc)]
  have hJ_last :
      P.real (separatedBoxFloorCount N a b (Sum.inr (Fin.last k)) ⁻¹'
          separatedBoxCountSets k (Sum.inr (Fin.last k))) =
        1 - Real.exp (-((r : ℝ) * ((b (Fin.last k) : ℝ) - a (Fin.last k)))) := by
    have hlaw := h.hasLaw_nat_count_Ioc_smul_nnvolume (a (Fin.last k)) (b (Fin.last k))
    have hcompl : (Ici 1 : Set ℕ) = ({0} : Set ℕ)ᶜ := by
      ext m
      simp [Nat.one_le_iff_ne_zero]
    dsimp only [Set.preimage, separatedBoxFloorCount, separatedBoxIntervals, separatedBoxCountSets,
      Sum.elim_inr]
    rw [ite_eq_left rfl,
      hlaw.measureReal_eq (p := (· ∈ (Ici 1 : Set ℕ))) MeasurableSet.of_discrete, ofPred_mem_eq,
      hcompl, measureReal_compl MeasurableSet.of_discrete, probReal_univ,
      poissonMeasure_real_singleton_zero, NNReal.coe_mul,
      NNReal.coe_sub (hsep.le (Fin.last k))]
  -- Stage 2: split the product across gap/box terms and telescope the exponential factors.
  rw [Fintype.prod_sum_type]
  simp_rw [hG_val]
  rw [Fin.prod_univ_castSucc
      (f := fun i => P.real (separatedBoxFloorCount N a b (Sum.inr i) ⁻¹'
        separatedBoxCountSets k (Sum.inr i))),
    hJ_last]
  simp_rw [hJ_cast]
  rw [Finset.prod_mul_distrib]
  exact prod_exp_separated_endpoints k (r : ℝ) a b

-- Roadmap:
-- 1. Floored counts on the `2(k + 1)` disjoint intervals `separatedBoxIntervals a b` are mutually
--    independent (`IsPoissonRandomMeasure.iIndepFun_eval`).
-- 2. Occurrence-time membership in `∏ᵢ (aᵢ, bᵢ]` agrees a.e. with those `2(k + 1)` count events
--    (`preimage_occurrenceTime_separatedBox_ae_eq`).
-- 3. Independence turns the intersection probability into a product of Poisson probabilities that
--    telescopes to the separated-box mass formula (`prod_poisson_separatedBox_eq_boxFormula`).
private lemma poisson_occurrenceTime_apply_separatedBox {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) {k : ℕ}
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    (P.map fun ω (i : Fin (k + 1)) => ((N ω).occurrenceTime i).toNNReal)
        (univ.pi fun i => Ioc (a i) (b i)) =
      ENNReal.ofReal ((∏ j : Fin k, (r : ℝ) * ((b j.castSucc : ℝ) - a j.castSucc)) *
        (Real.exp (-((r : ℝ) * a (Fin.last k))) - Real.exp (-((r : ℝ) * b (Fin.last k))))) := by
  let := h.isProbabilityMeasure
  have hm_floor : Measurable fun x : ℝ≥0∞ => ⌊x.toNNReal⌋₊ := by fun_prop
  have hind_raw := h.iIndepFun_eval (A := separatedBoxIntervals a b)
    (fun u => by cases u <;> exact measurableSet_Ioc)
    (pairwise_disjoint_separatedIntervals hsep)
  have hindX : ProbabilityTheory.iIndepFun (separatedBoxFloorCount N a b) P :=
    hind_raw.comp (fun _ => fun x : ℝ≥0∞ => ⌊x.toNNReal⌋₊) (fun _ => hm_floor)
  have hmeas_time : Measurable fun ω (i : Fin (k + 1)) => ((N ω).occurrenceTime i).toNNReal :=
    measurable_pi_iff.mpr fun i =>
      ((Measure.measurable_occurrenceTime i).comp h.measurable).ennreal_toNNReal
  rw [Measure.map_apply hmeas_time (MeasurableSet.univ_pi fun _ => measurableSet_Ioc),
    measure_congr (preimage_occurrenceTime_separatedBox_ae_eq h hsep),
    ← ENNReal.ofReal_toReal (measure_ne_top P _)]
  congr 1
  have hprod_meas := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindX) Finset.univ
    (sets := separatedBoxCountSets k) (fun _ _ => MeasurableSet.of_discrete)
  rw [hprod_meas, ENNReal.toReal_prod]
  simp_rw [← measureReal_def]
  exact prod_poisson_separatedBox_eq_boxFormula h hsep

private lemma ae_pos_and_strictMono_toNNReal_occurrenceTime {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (m : ℕ) :
    ∀ᵐ s ∂(P.map fun ω (i : Fin m) => ((N ω).occurrenceTime i).toNNReal),
      (∀ i, 0 < s i) ∧ StrictMono s := by
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  have hmeas : Measurable fun ω (i : Fin m) => ((N ω).occurrenceTime i).toNNReal :=
    measurable_pi_iff.mpr fun i =>
      ((Measure.measurable_occurrenceTime i).comp h.measurable).ennreal_toNNReal
  rw [ae_map_iff hmeas.aemeasurable (measurableSet_setOf_pos_and_strictMono m)]
  filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
    h.ae_forall_singleton_le_one_smul_nnvolume,
    h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hlf hint hsimple hposfin
  refine ⟨fun i => ENNReal.toNNReal_pos (hposfin i).1.ne' (hposfin i).2.ne, ?_⟩
  have hmono_nat : StrictMono fun n : ℕ => ((N ω).occurrenceTime n).toNNReal :=
    strictMono_nat_of_lt_succ fun n =>
      (ENNReal.toNNReal_lt_toNNReal (hposfin n).2.ne (hposfin (n + 1)).2.ne).mpr
        (hint.occurrenceTime_lt_succ (hposfin n).2.ne (hsimple _))
  exact fun i j hij => hmono_nat hij

end Helpers

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- For a Poisson random measure on `ℝ≥0` with zero intensity, every extended interarrival gap is
infinite almost surely. -/
theorem IsPoissonRandomMeasure.ae_forall_occurrenceGap_eq_top_of_zero
    {N : Ω → Measure ℝ≥0} (h : IsPoissonRandomMeasure P N 0) :
    ∀ᵐ ω ∂P, ∀ n, (N ω).occurrenceGap n = ∞ := by
  filter_upwards [h.ae_eq_zero_of_zero] with ω hω n
  simp [hω]

section Homogeneous

variable {N : Ω → Measure ℝ≥0} {r : ℝ≥0}

/-- The first `m` finite occurrence-time representatives of a positive-rate homogeneous Poisson
random measure have the joint law of the cumulative sums of `m` independent exponential
variables of rate `r` on `ℝ≥0`. -/
theorem IsPoissonRandomMeasure.hasLaw_toNNReal_occurrenceTime_prefix
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (m : ℕ) :
    HasLaw (fun ω (i : Fin m) => ((N ω).occurrenceTime i).toNNReal)
      ((Measure.pi fun _ : Fin m => nnrealExpMeasure r).map fun x i => ∑ j ∈ Finset.Iic i, x j)
      P := by
  let := h.isProbabilityMeasure
  have hr' : 0 < (r : ℝ) := hr
  let := isProbabilityMeasure_nnrealExpMeasure hr'
  have hmeas : Measurable fun ω (i : Fin m) => ((N ω).occurrenceTime i).toNNReal :=
    measurable_pi_iff.mpr fun i =>
      ((Measure.measurable_occurrenceTime i).comp h.measurable).ennreal_toNNReal
  refine ⟨hmeas.aemeasurable, ?_⟩
  apply Measure.ext_of_Ioc_strictMono
    (ae_pos_and_strictMono_toNNReal_occurrenceTime h hr m)
    (ae_pos_and_strictMono_map_sum_Iic_pi_nnrealExpMeasure r m)
  intro a b hsep
  cases m with
  | zero =>
    have huniv : (univ.pi fun i : Fin 0 => Ioc (a i) (b i)) = univ := by
      ext x
      simp
    rw [huniv, measure_univ, measure_univ]
  | succ k =>
    rw [poisson_occurrenceTime_apply_separatedBox h hsep,
      map_sum_Iic_pi_nnrealExpMeasure_univ_pi_Ioc hr'.le hsep]

/-- The first `m` finite interarrival-gap representatives of a positive-rate homogeneous Poisson
random measure have the product exponential law on `Fin m → ℝ≥0`. -/
theorem IsPoissonRandomMeasure.hasLaw_toNNReal_occurrenceGap_prefix
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (m : ℕ) :
    HasLaw (fun ω (i : Fin m) => ((N ω).occurrenceGap i).toNNReal)
      (Measure.pi fun _ : Fin m => nnrealExpMeasure r) P := by
  have hm_sum : Measurable fun (x : Fin m → ℝ≥0) (i : Fin m) => ∑ j ∈ Finset.Iic i, x j :=
    measurable_pi_iff.mpr fun i => Finset.measurable_fun_sum _ fun j _ => measurable_pi_apply j
  have hcomp := (hasLaw_map (measurable_gapOfPartialSum m).aemeasurable).comp
    (h.hasLaw_toNNReal_occurrenceTime_prefix hr m)
  rw [Measure.map_map (measurable_gapOfPartialSum m) hm_sum,
    gapOfPartialSum_comp_sum_Iic, Measure.map_id] at hcomp
  refine hcomp.congr ?_
  filter_upwards [h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hfin
  funext i
  cases m with
  | zero => exact i.elim0
  | succ k =>
    cases i using Fin.cases with
    | zero => simp [gapOfPartialSum]
    | succ j =>
      simp only [Function.comp_apply, gapOfPartialSum, Fin.castSucc_succ, Fin.cons_succ,
        Fin.val_succ, Fin.val_castSucc]
      exact Measure.toNNReal_occurrenceGap_succ (hfin j).2.ne

/-- The first `m` real-valued interarrival-gap representatives of a positive-rate homogeneous
Poisson random measure have the product exponential law on `Fin m → ℝ`. -/
theorem IsPoissonRandomMeasure.hasLaw_toReal_occurrenceGap_prefix
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (m : ℕ) :
    HasLaw (fun ω (i : Fin m) => ((N ω).occurrenceGap i).toReal)
      (Measure.pi fun _ : Fin m => expMeasure r) P := by
  have hr' : 0 < (r : ℝ) := hr
  let := isProbabilityMeasure_nnrealExpMeasure hr'
  let := isProbabilityMeasure_expMeasure hr'
  have hmp : MeasurePreserving (fun (x : Fin m → ℝ≥0) i => (x i : ℝ))
      (Measure.pi fun _ : Fin m => nnrealExpMeasure r)
      (Measure.pi fun _ : Fin m => expMeasure r) :=
    measurePreserving_pi _ _ fun _ => ⟨by fun_prop, map_coe_nnrealExpMeasure r⟩
  exact (hmp.fun_comp_hasLaw (h.hasLaw_toNNReal_occurrenceGap_prefix hr m)).congr
    (Filter.Eventually.of_forall fun _ => funext fun _ => (ENNReal.coe_toNNReal_eq_toReal _).symm)

/-- Each finite `ℝ≥0` interarrival-gap representative of a positive-rate homogeneous Poisson
random measure has law `nnrealExpMeasure r`. -/
theorem IsPoissonRandomMeasure.hasLaw_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω => ((N ω).occurrenceGap n).toNNReal) (nnrealExpMeasure r) P := by
  have hr' : 0 < (r : ℝ) := hr
  let := isProbabilityMeasure_nnrealExpMeasure hr'
  have heval := (measurePreserving_eval (fun _ : Fin (n + 1) => nnrealExpMeasure r)
    (Fin.last n)).fun_comp_hasLaw (h.hasLaw_toNNReal_occurrenceGap_prefix hr (n + 1))
  exact heval.congr (Filter.Eventually.of_forall fun _ => by simp only [eval, Fin.val_last])

/-- Each real-valued interarrival-gap representative of a positive-rate homogeneous Poisson
random measure has the exponential law of rate `r`. -/
theorem IsPoissonRandomMeasure.hasLaw_toReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω => ((N ω).occurrenceGap n).toReal) (expMeasure r) P := by
  have hr' : 0 < (r : ℝ) := hr
  let := isProbabilityMeasure_expMeasure hr'
  have heval := (measurePreserving_eval (fun _ : Fin (n + 1) => expMeasure r)
    (Fin.last n)).fun_comp_hasLaw (h.hasLaw_toReal_occurrenceGap_prefix hr (n + 1))
  exact heval.congr (Filter.Eventually.of_forall fun _ => by simp only [eval, Fin.val_last])

/-- Each extended interarrival gap of a positive-rate homogeneous Poisson random measure has the
exponential law of rate `r` pushed forward to `ℝ≥0∞`. -/
theorem IsPoissonRandomMeasure.hasLaw_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω => (N ω).occurrenceGap n) ((expMeasure r).map ENNReal.ofReal) P := by
  refine ((hasLaw_map ENNReal.measurable_ofReal.aemeasurable).comp
    (h.hasLaw_toReal_occurrenceGap hr n)).congr ?_
  filter_upwards [h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hfin
  exact (ENNReal.ofReal_toReal (((N ω).occurrenceGap_ne_top_iff n).mpr (hfin n).2.ne)).symm

/-- The extended interarrival gaps of a homogeneous Poisson random measure on `ℝ≥0` are mutually
independent for every rate `r : ℝ≥0`, including rate zero. -/
theorem IsPoissonRandomMeasure.iIndepFun_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω => (N ω).occurrenceGap n) P := by
  let := h.isProbabilityMeasure
  rcases eq_or_lt_of_le (zero_le : 0 ≤ r) with rfl | hr
  · have hzero : IsPoissonRandomMeasure P N 0 := by simpa using h
    have hae := hzero.ae_forall_occurrenceGap_eq_top_of_zero
    exact iIndepFun_of_ae_eq_const_outside_subsingleton (s := ∅) subsingleton_empty fun n _ =>
      ⟨∞, hae.mono fun ω hω => hω n⟩
  · have hr' : 0 < (r : ℝ) := hr
    let := isProbabilityMeasure_nnrealExpMeasure hr'
    have hind_nnreal :
        ProbabilityTheory.iIndepFun (fun n ω => ((N ω).occurrenceGap n).toNNReal) P := by
      rw [iIndepFun_iff_finset]
      intro I
      let m := I.sup id + 1
      let emb : I ↪ Fin m :=
        ⟨fun i => ⟨i.1, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.2)⟩,
          fun a b hab => Subtype.ext (Fin.mk.inj hab)⟩
      have hpi := h.hasLaw_toNNReal_occurrenceGap_prefix hr m
      have hfin : ProbabilityTheory.iIndepFun
          (fun (i : Fin m) ω => ((N ω).occurrenceGap i).toNNReal) P := by
        apply (iIndepFun_iff_hasLaw_pi_pi
          (μ := fun _ : Fin m => nnrealExpMeasure r) (fun i => ?_)).mpr hpi
        exact (measurePreserving_eval (fun _ : Fin m => nnrealExpMeasure r) i).hasLaw.comp hpi
      exact hfin.precomp (g := emb) emb.injective
    have hind_coe := hind_nnreal.comp (fun _ (x : ℝ≥0) => (x : ℝ≥0∞))
      (fun _ => measurable_coe_nnreal_ennreal)
    refine hind_coe.congr fun n => ?_
    filter_upwards [h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hfin
    exact ENNReal.coe_toNNReal (((N ω).occurrenceGap_ne_top_iff n).mpr (hfin n).2.ne)

/-- The `ℝ≥0` `toNNReal` images of the interarrival gaps of a homogeneous Poisson random measure
are mutually independent for every rate `r : ℝ≥0`. For `0 < r` they coincide almost surely with
the finite gaps; at `r = 0` the gaps are almost surely infinite and `toNNReal` maps them to `0`. -/
theorem IsPoissonRandomMeasure.iIndepFun_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω => ((N ω).occurrenceGap n).toNNReal) P :=
  h.iIndepFun_occurrenceGap.comp (fun _ => ENNReal.toNNReal) (fun _ => ENNReal.measurable_toNNReal)

/-- The real-valued `toReal` images of the interarrival gaps of a homogeneous Poisson random
measure are mutually independent for every rate `r : ℝ≥0`. For `0 < r` they coincide almost surely
with the finite gaps; at `r = 0` the gaps are almost surely infinite and `toReal` maps them to
`0`. -/
theorem IsPoissonRandomMeasure.iIndepFun_toReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω => ((N ω).occurrenceGap n).toReal) P :=
  h.iIndepFun_occurrenceGap.comp (fun _ => ENNReal.toReal) (fun _ => ENNReal.measurable_toReal)

/-- The full sequence of `ℝ≥0` interarrival-gap representatives of a positive-rate homogeneous
Poisson random measure has the countable product law of `nnrealExpMeasure r`. -/
theorem IsPoissonRandomMeasure.hasLaw_toNNReal_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n => ((N ω).occurrenceGap n).toNNReal)
      (Measure.infinitePi fun _ : ℕ => nnrealExpMeasure r) P := by
  let := h.isProbabilityMeasure
  let := isProbabilityMeasure_nnrealExpMeasure (r := r) hr
  have hmeas : Measurable fun ω n => ((N ω).occurrenceGap n).toNNReal :=
    measurable_pi_iff.mpr fun n =>
      ((Measure.measurable_occurrenceGap n).comp h.measurable).ennreal_toNNReal
  exact h.iIndepFun_toNNReal_occurrenceGap.hasLaw_infinitePi
    (h.hasLaw_toNNReal_occurrenceGap hr) hmeas.aemeasurable

/-- The full sequence of real-valued interarrival-gap representatives of a positive-rate
homogeneous Poisson random measure has the countable product law of `expMeasure r`. -/
theorem IsPoissonRandomMeasure.hasLaw_toReal_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n => ((N ω).occurrenceGap n).toReal)
      (Measure.infinitePi fun _ : ℕ => expMeasure r) P := by
  let := h.isProbabilityMeasure
  let := isProbabilityMeasure_expMeasure (r := r) hr
  have hmeas : Measurable fun ω n => ((N ω).occurrenceGap n).toReal :=
    measurable_pi_iff.mpr fun n =>
      ((Measure.measurable_occurrenceGap n).comp h.measurable).ennreal_toReal
  exact h.iIndepFun_toReal_occurrenceGap.hasLaw_infinitePi
    (h.hasLaw_toReal_occurrenceGap hr) hmeas.aemeasurable

/-- The full sequence of extended interarrival gaps of a positive-rate homogeneous Poisson random
measure has the countable product law of `(expMeasure r).map ENNReal.ofReal`. -/
theorem IsPoissonRandomMeasure.hasLaw_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω n => (N ω).occurrenceGap n)
      (Measure.infinitePi fun _ : ℕ => (expMeasure r).map ENNReal.ofReal) P := by
  let := h.isProbabilityMeasure
  let := isProbabilityMeasure_expMeasure (r := r) hr
  have hmeas : Measurable fun ω n => (N ω).occurrenceGap n :=
    measurable_pi_iff.mpr fun n => (Measure.measurable_occurrenceGap n).comp h.measurable
  exact h.iIndepFun_occurrenceGap.hasLaw_infinitePi
    (h.hasLaw_occurrenceGap hr) hmeas.aemeasurable

end Homogeneous

end TauCeti.Probability
