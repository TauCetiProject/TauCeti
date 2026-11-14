/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.HittingTime
public import TauCeti.Probability.Distributions.FoldedNormal.Basic
import Mathlib.Probability.CDF
import TauCeti.Probability.BrownianMotion.Filtered
import TauCeti.Probability.BrownianMotion.Version
import TauCeti.Probability.Process.HittingTime
import TauCeti.Probability.Process.Version

/-!
# The reflection principle and running maximum of Brownian motion

For a real Brownian motion `B` and a positive level `a > 0`, the reflection principle identifies
the probability of reaching `a` by time `t` with twice the terminal tail probability:

`P {ω | ∃ s ≤ t, a ≤ B s ω} = 2 * P {ω | a ≤ B t ω}`.

This file proves the reflection principle without assuming completeness of the ambient measurable
space or pre-existing strong Markov machinery:

1. On any finite monotone time grid `g : Fin (n + 1) → ℝ≥0`, decomposing `{∃ i, b < B (g i) ω}` by
   the index of first crossing and using the independence and symmetry of the remaining increment
   `B (g (Fin.last n)) - B (g i)` gives the discrete reflection upper bound
   `ProbabilityTheory.IsPreBrownianReal.measure_exists_gt_le`.
2. Passing along nested dyadic grids on `[0, t]` and levels approaching `a` from below extends the
   upper bound to continuous time (`ProbabilityTheory.IsBrownianReal.measure_exists_le_ge_le`).
3. For `a > 0` and `t > 0`, decomposing the first dyadic crossing into `[a, a + δ)` up to the
   uniform-continuity mesh oscillation of paths on `[0, t]` gives the matching lower bound as
   `n → ∞` and `δ ↓ 0` (`ProbabilityTheory.IsBrownianReal.measure_exists_le_ge`).

Immediate corollaries include strict and negative-level reflection identities, almost-sure
immediate crossing of `0` into `(0, ∞)` and `(-∞, 0)` from time `0`, and the folded-normal law of
the running maximum `⨆ s : Set.Iic t, B s ω`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.6, §2.8.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability

private theorem one_le_two_mul_gaussianReal_Ici (v : ℝ≥0) :
    (1 : ℝ≥0∞) ≤ 2 * gaussianReal 0 v (Ici 0) := by
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Ici (0 : ℝ) = Iic 0 := by ext; simp
  have hneg : gaussianReal 0 v (Iic 0) = gaussianReal 0 v (Ici 0) := by
    have h := congrArg (· (Ici (0 : ℝ))) (gaussianReal_map_neg (μ := 0) (v := v))
    rwa [neg_zero, Measure.map_apply measurable_neg measurableSet_Ici, hpre] at h
  calc (1 : ℝ≥0∞) = gaussianReal 0 v univ := measure_univ.symm
    _ = gaussianReal 0 v (Iic 0 ∪ Ici 0) := by rw [Iic_union_Ici]
    _ ≤ gaussianReal 0 v (Iic 0) + gaussianReal 0 v (Ici 0) := measure_union_le _ _
    _ = 2 * gaussianReal 0 v (Ici 0) := by rw [hneg, two_mul]

private theorem two_mul_gaussianReal_Ioi_le_one (v : ℝ≥0) :
    2 * gaussianReal 0 v (Ioi 0) ≤ (1 : ℝ≥0∞) := by
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Ioi (0 : ℝ) = Iio 0 := by ext; simp
  have hneg : gaussianReal 0 v (Iio 0) = gaussianReal 0 v (Ioi 0) := by
    have h := congrArg (· (Ioi (0 : ℝ))) (gaussianReal_map_neg (μ := 0) (v := v))
    rwa [neg_zero, Measure.map_apply measurable_neg measurableSet_Ioi, hpre] at h
  have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) :=
    disjoint_left.mpr fun _ (hx₁ : _ < 0) (hx₂ : 0 < _) ↦ (hx₁.trans hx₂).false
  calc 2 * gaussianReal 0 v (Ioi 0)
      = gaussianReal 0 v (Iio 0) + gaussianReal 0 v (Ioi 0) := by rw [hneg, two_mul]
    _ = gaussianReal 0 v (Iio 0 ∪ Ioi 0) := (measure_union hdisj measurableSet_Ioi).symm
    _ ≤ gaussianReal 0 v univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

private theorem two_mul_gaussianReal_Ioi_eq_one {v : ℝ≥0} (hv : v ≠ 0) :
    2 * gaussianReal 0 v (Ioi 0) = (1 : ℝ≥0∞) := by
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  refine le_antisymm (two_mul_gaussianReal_Ioi_le_one v) ?_
  rw [measure_congr Ioi_ae_eq_Ici]
  exact one_le_two_mul_gaussianReal_Ici v

private theorem gaussianReal_map_abs_measureReal_Iic (v : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    ((gaussianReal 0 v).map (|·|)).real (Iic x) = 1 - 2 * (gaussianReal 0 v).real (Ioi x) := by
  have hpre : (fun y : ℝ ↦ -y) ⁻¹' Ioi x = Iio (-x) := by ext; simp
  have hneg : (gaussianReal 0 v).real (Iio (-x)) = (gaussianReal 0 v).real (Ioi x) := by
    have h := congrArg (fun μ : Measure ℝ ↦ μ.real (Ioi x))
      (gaussianReal_map_neg (μ := 0) (v := v))
    rwa [neg_zero, map_measureReal_apply measurable_neg measurableSet_Ioi, hpre] at h
  let S : Set ℝ := (|·|) ⁻¹' Iic x
  have hS : MeasurableSet S := measurableSet_Iic.preimage continuous_abs.measurable
  have hcompl : Sᶜ = Iio (-x) ∪ Ioi x := by
    ext y
    simp only [S, mem_compl_iff, mem_preimage, mem_Iic, mem_union, mem_Iio, mem_Ioi, not_le,
      lt_abs]
    exact ⟨fun h ↦ h.elim Or.inr fun h' ↦ Or.inl (lt_neg.mp h'),
      fun h ↦ h.elim (fun h' ↦ Or.inr (lt_neg.mpr h')) Or.inl⟩
  have hdisj : Disjoint (Iio (-x)) (Ioi x) :=
    disjoint_left.mpr fun y (hy₁ : y < -x) (hy₂ : x < y) ↦ by linarith
  have hc : (gaussianReal 0 v).real Sᶜ = 1 - (gaussianReal 0 v).real S :=
    probReal_compl_eq_one_sub hS
  rw [hcompl, measureReal_union hdisj measurableSet_Ioi, hneg] at hc
  rw [map_measureReal_apply continuous_abs.measurable measurableSet_Iic]
  linarith

end TauCeti.Probability

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B W : ℝ≥0 → Ω → ℝ}

private theorem measure_exists_gt_le_of_stronglyMeasurable (hW : IsPreBrownianReal W P)
    (hWm : ∀ t, StronglyMeasurable (W t)) {n : ℕ} {g : Fin (n + 1) → ℝ≥0}
    (hg : Monotone g) (b : ℝ) :
    P {ω | ∃ i, b < W (g i) ω} ≤ 2 * P {ω | b < W (g (Fin.last n)) ω} := by
  let ℱ := Filtration.natural W hWm
  have hWF := hW.isFilteredPreBrownianReal_natural hWm
  let N : Fin (n + 1) := Fin.last n
  let A (i : Fin (n + 1)) : Set Ω := {ω | (∀ j < i, W (g j) ω ≤ b) ∧ b < W (g i) ω}
  let C (i : Fin (n + 1)) : Set Ω := {ω | 0 ≤ (W (g N) - W (g i)) ω} ∩ A i
  have hA_meas (i : Fin (n + 1)) : MeasurableSet[ℱ (g i)] (A i) := by
    have hA_eq : A i = (⋂ j, ⋂ (_ : j < i), {ω | W (g j) ω ≤ b}) ∩ {ω | b < W (g i) ω} := by
      ext ω; simp [A]
    rw [hA_eq]
    refine (MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun (hji : j < i) ↦ ?_).inter
      (measurableSet_lt measurable_const (hWF.adapted (g i)))
    exact measurableSet_le ((hWF.adapted (g j)).mono (ℱ.mono (hg hji.le)) le_rfl) measurable_const
  have hA_disj : Pairwise fun i k ↦ Disjoint (A i) (A k) := fun i k hik ↦
    disjoint_left.mpr fun ω hi hk ↦ (lt_trichotomy i k).elim (fun h ↦ hi.2.not_ge (hk.1 i h))
      fun h ↦ h.elim hik fun h' ↦ hk.2.not_ge (hi.1 k h')
  have hA_union : (⋃ i, A i) = {ω | ∃ i, b < W (g i) ω} := by
    ext ω; simp only [mem_iUnion, mem_ofPred_eq, A]
    refine ⟨fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩, fun ⟨i, hi⟩ ↦ ?_⟩
    classical
    let S : Finset (Fin (n + 1)) := Finset.univ.filter fun j ↦ b < W (g j) ω
    have hSne : S.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    exact ⟨S.min' hSne, fun j hj ↦ not_lt.mp fun hjb ↦ hj.not_ge
      (Finset.min'_le S j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjb⟩)),
      (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2⟩
  have hC_meas (i : Fin (n + 1)) : MeasurableSet (C i) :=
    (measurableSet_Ici.preimage ((hWm (g N)).measurable.sub (hWm (g i)).measurable)).inter
      (ℱ.le (g i) _ (hA_meas i))
  have hC_disj : Pairwise fun i k ↦ Disjoint (C i) (C k) :=
    fun i k hik ↦ (hA_disj hik).mono inter_subset_right inter_subset_right
  have hC_sub : (⋃ i, C i) ⊆ {ω | b < W (g N) ω} := fun ω ⟨_, ⟨i, rfl⟩, hΔ, _, hbi⟩ ↦ by
    simp only [Pi.sub_apply, mem_ofPred_eq] at hΔ ⊢; linarith
  have hbound (i : Fin (n + 1)) : P (A i) ≤ 2 * P (C i) := by
    have hind := (Indep_iff _ _ _).mp (hWF.indep_sub (hg (Fin.le_last i)))
      ((W (g N) - W (g i)) ⁻¹' Ici 0) (A i) ⟨Ici 0, measurableSet_Ici, rfl⟩ (hA_meas i)
    have hlaw : P ((W (g N) - W (g i)) ⁻¹' Ici 0) = gaussianReal 0 (g N - g i) (Ici 0) :=
      (hW.hasLaw_sub_of_le (hg (Fin.le_last i))).measure_eq (p := (· ∈ Ici 0)) measurableSet_Ici
    calc P (A i) = 1 * P (A i) := (one_mul _).symm
      _ ≤ (2 * gaussianReal 0 (g N - g i) (Ici 0)) * P (A i) :=
          mul_le_mul_of_nonneg_right (one_le_two_mul_gaussianReal_Ici _) bot_le
      _ = 2 * P (C i) := by rw [mul_assoc, ← hlaw, ← hind]; rfl
  rw [← hA_union, measure_iUnion hA_disj (fun i ↦ ℱ.le (g i) _ (hA_meas i)), tsum_fintype]
  calc ∑ i, P (A i) ≤ ∑ i, 2 * P (C i) := Finset.sum_le_sum fun i _ ↦ hbound i
    _ = 2 * P (⋃ i, C i) := by rw [← Finset.mul_sum, measure_iUnion hC_disj hC_meas, tsum_fintype]
    _ ≤ 2 * P {ω | b < W (g N) ω} := mul_le_mul_of_nonneg_left (measure_mono hC_sub) bot_le

/-- **Discrete reflection inequality** for a real pre-Brownian motion: along any finite monotone
grid `g : Fin (n + 1) → ℝ≥0`, the probability of exceeding `b` somewhere on the grid is at most
twice the probability of exceeding `b` at the final grid time. -/
theorem measure_exists_gt_le (hB : IsPreBrownianReal B P) {n : ℕ} {g : Fin (n + 1) → ℝ≥0}
    (hg : Monotone g) (b : ℝ) :
    P {ω | ∃ i, b < B (g i) ω} ≤ 2 * P {ω | b < B (g (Fin.last n)) ω} := by
  let W (t : ℝ≥0) : Ω → ℝ := (hB.integrable_eval t).aestronglyMeasurable.mk (B t)
  have hBW (t : ℝ≥0) : B t =ᵐ[P] W t := (hB.integrable_eval t).aestronglyMeasurable.ae_eq_mk
  have hW : IsPreBrownianReal W P := hB.congr hBW
  have hWm (t : ℝ≥0) : StronglyMeasurable (W t) :=
    (hB.integrable_eval t).aestronglyMeasurable.stronglyMeasurable_mk
  have hgrid : ∀ᵐ ω ∂P, ∀ i : Fin (n + 1), B (g i) ω = W (g i) ω :=
    ae_all_iff.mpr fun i ↦ hBW (g i)
  have heq₁ : {ω | ∃ i, b < B (g i) ω} =ᵐ[P] {ω | ∃ i, b < W (g i) ω} := by
    filter_upwards [hgrid] with ω hω
    exact exists_congr fun i ↦ by simp only [hω i]
  have heq₂ : {ω | b < B (g (Fin.last n)) ω} =ᵐ[P] {ω | b < W (g (Fin.last n)) ω} := by
    filter_upwards [hBW (g (Fin.last n))] with ω hω
    simp only [hω]
  rw [measure_congr heq₁, measure_congr heq₂]
  exact hW.measure_exists_gt_le_of_stronglyMeasurable hWm hg b

/-- Symmetric discrete reflection inequality below a level `b`. -/
theorem measure_exists_lt_le (hB : IsPreBrownianReal B P) {n : ℕ} {g : Fin (n + 1) → ℝ≥0}
    (hg : Monotone g) (b : ℝ) :
    P {ω | ∃ i, B (g i) ω < b} ≤ 2 * P {ω | B (g (Fin.last n)) ω < b} := by
  simpa only [Pi.neg_apply, neg_lt_neg_iff] using hB.neg.measure_exists_gt_le hg (-b)

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability

private def dyadicGrid (t : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n + 1)) : ℝ≥0 :=
  (i.1 : ℝ≥0) * t / (2 ^ n : ℝ≥0)

private theorem dyadicGrid_zero (t : ℝ≥0) (n : ℕ) : dyadicGrid t n 0 = 0 := by
  simp [dyadicGrid]

private theorem dyadicGrid_last (t : ℝ≥0) (n : ℕ) :
    dyadicGrid t n (Fin.last (2 ^ n)) = t := by
  have hpos : (2 ^ n : ℝ≥0) ≠ 0 := pow_ne_zero n two_ne_zero
  simp [dyadicGrid, mul_div_cancel_left₀ t hpos]

private theorem monotone_dyadicGrid (t : ℝ≥0) (n : ℕ) : Monotone (dyadicGrid t n) := by
  intro i j hij
  have hij' : (i.1 : ℝ≥0) ≤ (j.1 : ℝ≥0) := Nat.cast_le.mpr hij
  simp only [dyadicGrid]
  gcongr

private theorem dyadicGrid_le (t : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n + 1)) :
    dyadicGrid t n i ≤ t :=
  (monotone_dyadicGrid t n (Fin.le_last i)).trans_eq (dyadicGrid_last t n)

private theorem dyadicGrid_double (t : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n + 1)) :
    dyadicGrid t (n + 1) ⟨2 * i.1, by omega⟩ = dyadicGrid t n i := by
  apply NNReal.eq
  simp only [dyadicGrid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow,
    NNReal.coe_ofNat, Nat.cast_mul, Nat.cast_ofNat, pow_succ']
  field_simp

private theorem dist_dyadicGrid_succ (t : ℝ≥0) (n : ℕ) (k : Fin (2 ^ n)) :
    dist (dyadicGrid t n k.succ) (dyadicGrid t n k.castSucc) = (t : ℝ) / 2 ^ n := by
  have hle : (dyadicGrid t n k.castSucc : ℝ) ≤ (dyadicGrid t n k.succ : ℝ) :=
    NNReal.coe_le_coe.mpr (monotone_dyadicGrid t n k.castSucc_le_succ)
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr hle)]
  simp only [dyadicGrid, Fin.val_succ, Fin.val_castSucc]
  push_cast
  ring

private theorem exists_dyadicGrid_mem_open {t s : ℝ≥0} (hst : s ≤ t) {U : Set ℝ≥0}
    (hU : IsOpen U) (hs : s ∈ U) : ∃ n : ℕ, ∃ i : Fin (2 ^ n + 1), dyadicGrid t n i ∈ U := by
  rcases eq_or_ne t 0 with rfl | ht0
  · obtain rfl : s = 0 := nonpos_iff_eq_zero.mp hst
    exact ⟨0, 0, by simpa only [dyadicGrid_zero] using hs⟩
  have htpos : (0 : ℝ) < t := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU s hs
  have htend : Tendsto (fun n : ℕ ↦ (t : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hε)).exists
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  let k : ℕ := ⌊(s : ℝ) * 2 ^ n / (t : ℝ)⌋₊
  have hk_le : k ≤ 2 ^ n := Nat.floor_le_of_le (by
    rw [div_le_iff₀ htpos]
    push_cast
    nlinarith [NNReal.coe_le_coe.mpr hst])
  let i : Fin (2 ^ n + 1) := ⟨k, Nat.lt_succ_of_le hk_le⟩
  refine ⟨n, i, hball ?_⟩
  have h1 : (k : ℝ) ≤ (s : ℝ) * 2 ^ n / (t : ℝ) := Nat.floor_le (by positivity)
  have h2 : (s : ℝ) * 2 ^ n < ((k : ℝ) + 1) * t :=
    (div_lt_iff₀ htpos).mp (Nat.lt_floor_add_one _)
  have hlo : (dyadicGrid t n i : ℝ) ≤ s := by
    simp only [dyadicGrid, i, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_pow, NNReal.coe_ofNat]
    rwa [div_le_iff₀ hpow, ← le_div_iff₀ htpos]
  have hhi : (s : ℝ) < (dyadicGrid t n i : ℝ) + (t : ℝ) / 2 ^ n := by
    simp only [dyadicGrid, i, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_pow, NNReal.coe_ofNat]
    rw [← add_div, lt_div_iff₀ hpow]
    linarith
  rw [Metric.mem_ball, NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

private theorem tendsto_measure_dyadicOsc {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsFiniteMeasure P] {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ s, StronglyMeasurable (W s))
    (hWc : ∀ ω, Continuous (W · ω)) (t : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ ↦ P {ω | ∃ k : Fin (2 ^ n),
      δ ≤ |W (dyadicGrid t n k.succ) ω - W (dyadicGrid t n k.castSucc) ω|}) atTop (𝓝 0) := by
  let Osc (n : ℕ) : Set Ω := {ω | ∃ k : Fin (2 ^ n),
    δ ≤ |W (dyadicGrid t n k.succ) ω - W (dyadicGrid t n k.castSucc) ω|}
  let Tail (m : ℕ) : Set Ω := ⋃ n ≥ m, Osc n
  have hOsc_meas (n : ℕ) : MeasurableSet (Osc n) := by
    have hstep (k : Fin (2 ^ n)) : Measurable fun ω ↦
        |W (dyadicGrid t n k.succ) ω - W (dyadicGrid t n k.castSucc) ω| :=
      continuous_abs.measurable.comp ((hWm _).measurable.sub (hWm _).measurable)
    simpa only [Osc, ofPred_exists] using
      MeasurableSet.iUnion fun k ↦ measurableSet_le measurable_const (hstep k)
  have hTail_meas (m : ℕ) : NullMeasurableSet (Tail m) P :=
    (MeasurableSet.biUnion (to_countable _) fun n _ ↦ hOsc_meas n).nullMeasurableSet
  have hTail_anti : Antitone Tail := fun m₁ m₂ hm ω hω ↦ by
    simp only [Tail, mem_iUnion] at hω ⊢
    obtain ⟨n, hn, h⟩ := hω
    exact ⟨n, hm.trans hn, h⟩
  have hTail_inter : (⋂ m, Tail m) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_iUnion, mem_empty_iff_false, iff_false, not_forall, not_exists, Tail]
    have huc := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).uniformContinuousOn_of_continuous
      (hWc ω).continuousOn
    obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
    have htend : Tendsto (fun n : ℕ ↦ (t : ℝ) / 2 ^ n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
    obtain ⟨M, hM⟩ := (htend.eventually (gt_mem_nhds hη)).exists_forall_of_atTop
    refine ⟨M, fun n hn ⟨k, hk⟩ ↦ ?_⟩
    have hd : dist (dyadicGrid t n k.succ) (dyadicGrid t n k.castSucc) < η :=
      (dist_dyadicGrid_succ t n k).trans_lt (hM n hn)
    have hlt := hmod (dyadicGrid t n k.succ) ⟨bot_le, dyadicGrid_le t n _⟩
      (dyadicGrid t n k.castSucc) ⟨bot_le, dyadicGrid_le t n _⟩ hd
    rw [Real.dist_eq] at hlt
    exact hk.not_gt hlt
  have hTail_tendsto : Tendsto (P ∘ Tail) atTop (𝓝 0) := by
    simpa only [hTail_inter, measure_empty] using
      tendsto_measure_iInter_atTop hTail_meas hTail_anti ⟨0, measure_ne_top P _⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hTail_tendsto
    (fun _ ↦ bot_le) fun m ↦ measure_mono fun ω hω ↦ ?_
  exact mem_iUnion₂.mpr ⟨m, le_rfl, hω⟩

private theorem measure_exists_le_gt_le_of_continuous {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P)
    (hWc : ∀ ω, Continuous (W · ω)) (t : ℝ≥0) (b : ℝ) :
    P {ω | ∃ s ≤ t, b < W s ω} ≤ 2 * P {ω | b < W t ω} := by
  let E (n : ℕ) : Set Ω := {ω | ∃ i : Fin (2 ^ n + 1), b < W (dyadicGrid t n i) ω}
  have hE_mono : Monotone E := by
    refine monotone_nat_of_le_succ fun n ω ⟨i, hi⟩ ↦ ?_
    exact ⟨⟨2 * i.1, by omega⟩, by rwa [dyadicGrid_double]⟩
  have hE_union : (⋃ n, E n) = {ω | ∃ s ≤ t, b < W s ω} := by
    ext ω; simp only [mem_iUnion, mem_ofPred_eq, E]
    refine ⟨fun ⟨n, i, hi⟩ ↦ ⟨dyadicGrid t n i, dyadicGrid_le t n i, hi⟩, fun ⟨s, hst, hs⟩ ↦ ?_⟩
    obtain ⟨n, i, hi⟩ := exists_dyadicGrid_mem_open hst (isOpen_lt continuous_const (hWc ω)) hs
    exact ⟨n, i, hi⟩
  rw [← hE_union]
  refine le_of_tendsto' (tendsto_measure_iUnion_atTop (μ := P) hE_mono) fun n ↦ ?_
  have h := hW.measure_exists_gt_le (monotone_dyadicGrid t n) b
  rwa [dyadicGrid_last] at h

private theorem measurableSet_exists_le_gt {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ s, StronglyMeasurable (W s)) (hWc : ∀ ω, Continuous (W · ω))
    (t : ℝ≥0) (b : ℝ) : MeasurableSet {ω | ∃ s ≤ t, b < W s ω} := by
  have heq : {ω | ∃ s ≤ t, b < W s ω} =
      ⋃ n : ℕ, ⋃ i : Fin (2 ^ n + 1), {ω | b < W (dyadicGrid t n i) ω} := by
    ext ω; simp only [mem_iUnion, mem_ofPred_eq]
    refine ⟨fun ⟨s, hst, hs⟩ ↦ ?_, fun ⟨n, i, hi⟩ ↦ ⟨dyadicGrid t n i, dyadicGrid_le t n i, hi⟩⟩
    obtain ⟨n, i, hi⟩ := exists_dyadicGrid_mem_open hst (isOpen_lt continuous_const (hWc ω)) hs
    exact ⟨n, i, hi⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun i ↦
    measurableSet_lt measurable_const (hWm _).measurable

private theorem measure_exists_le_ge_le_of_continuous {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P)
    (hWm : ∀ s, StronglyMeasurable (W s)) (hWc : ∀ ω, Continuous (W · ω)) (t : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ t, a ≤ W s ω} ≤ 2 * P {ω | a ≤ W t ω} := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let F (m : ℕ) : Set Ω := {ω | ∃ s ≤ t, a - 1 / (m + 1 : ℝ) < W s ω}
  let G (m : ℕ) : Set Ω := {ω | a - 1 / (m + 1 : ℝ) < W t ω}
  have hba : Antitone fun m : ℕ ↦ (1 : ℝ) / (m + 1) := fun m₁ m₂ hm ↦
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
  have hF_anti : Antitone F := fun m₁ m₂ hm ω ⟨s, hst, hs⟩ ↦
    ⟨s, hst, (sub_le_sub_left (hba hm) a).trans_lt hs⟩
  have hG_anti : Antitone G := fun m₁ m₂ hm ω hω ↦ (sub_le_sub_left (hba hm) a).trans_lt hω
  have htend_b : Tendsto (fun m : ℕ ↦ a - 1 / (m + 1 : ℝ)) atTop (𝓝 a) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := a)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  have hF_inter : (⋂ m, F m) = {ω | ∃ s ≤ t, a ≤ W s ω} := by
    ext ω; simp only [mem_iInter, mem_ofPred_eq, F]
    refine ⟨fun h ↦ ?_, fun ⟨s, hst, hs⟩ m ↦ ⟨s, hst, (sub_lt_self a (by positivity)).trans_le hs⟩⟩
    obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr (bot_le : (0 : ℝ≥0) ≤ t)) (hWc ω).continuousOn
    refine ⟨u, hu.2, le_of_tendsto htend_b (Eventually.of_forall fun m ↦ ?_)⟩
    obtain ⟨s, hst, hs⟩ := h m
    exact hs.le.trans (hmax ⟨bot_le, hst⟩)
  have hG_inter : (⋂ m, G m) = {ω | a ≤ W t ω} := by
    ext ω; simp only [mem_iInter, mem_ofPred_eq, G]
    exact ⟨fun h ↦ le_of_tendsto htend_b (Eventually.of_forall fun m ↦ (h m).le),
      fun h m ↦ (sub_lt_self a (by positivity)).trans_le h⟩
  have hF_lim := tendsto_measure_iInter_atTop (μ := P)
    (fun m ↦ (measurableSet_exists_le_gt hWm hWc t _).nullMeasurableSet) hF_anti
    ⟨0, measure_ne_top P _⟩
  have hG_lim : Tendsto (fun m ↦ 2 * P (G m)) atTop (𝓝 (2 * P (⋂ m, G m))) :=
    ENNReal.Tendsto.const_mul (tendsto_measure_iInter_atTop (μ := P)
      (fun m ↦ (measurableSet_lt measurable_const (hWm t).measurable).nullMeasurableSet)
      hG_anti ⟨0, measure_ne_top P _⟩) (Or.inr ENNReal.ofNat_ne_top)
  rw [← hF_inter, ← hG_inter]
  exact le_of_tendsto_of_tendsto hF_lim hG_lim (Eventually.of_forall fun m ↦
    measure_exists_le_gt_le_of_continuous hW hWc t _)

private theorem subset_dyadicCrossing_union_osc {Ω : Type*} {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (t : ℝ≥0) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (n : ℕ) :
    {ω | a + δ ≤ W t ω} ⊆
      (⋃ i : Fin (2 ^ n + 1),
        {ω | (∀ j < i, W (dyadicGrid t n j) ω < a) ∧
          a ≤ W (dyadicGrid t n i) ω ∧ W (dyadicGrid t n i) ω < a + δ} ∩
            {ω | a + δ ≤ W t ω}) ∪
        {ω | ∃ k : Fin (2 ^ n),
          δ ≤ |W (dyadicGrid t n k.succ) ω - W (dyadicGrid t n k.castSucc) ω|} := by
  let g := dyadicGrid t n
  intro ω hω
  by_cases hosc : ∃ k : Fin (2 ^ n), δ ≤ |W (g k.succ) ω - W (g k.castSucc) ω|
  · exact Or.inr hosc
  · refine Or.inl (mem_iUnion.mpr ?_)
    classical
    let N : Fin (2 ^ n + 1) := Fin.last (2 ^ n)
    let S : Finset (Fin (2 ^ n + 1)) := Finset.univ.filter fun j ↦ a ≤ W (g j) ω
    have hWN : a ≤ W (g N) ω := by
      have hWt : a + δ ≤ W t ω := hω
      simp only [g, N, dyadicGrid_last]
      linarith
    have hSne : S.Nonempty := ⟨N, Finset.mem_filter.mpr ⟨Finset.mem_univ N, hWN⟩⟩
    let i₀ := S.min' hSne
    have hi₀_ge : a ≤ W (g i₀) ω := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
    have hi₀_min (j : Fin (2 ^ n + 1)) (hj : j < i₀) : W (g j) ω < a :=
      not_le.mp fun hja ↦
        hj.not_ge (Finset.min'_le S j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hja⟩))
    have hi₀_ne : i₀ ≠ 0 := by
      intro h0
      have hw0 : W (g i₀) ω = 0 := by simp only [g, h0, dyadicGrid_zero, hW0 ω]
      linarith
    obtain ⟨k, hk_eq⟩ := Fin.eq_succ_of_ne_zero hi₀_ne
    rw [hk_eq] at hi₀_ge hi₀_min
    have hk_lt : W (g k.castSucc) ω < a := hi₀_min k.castSucc k.castSucc_lt_succ
    have hk_step : |W (g k.succ) ω - W (g k.castSucc) ω| < δ :=
      not_le.mp fun hle ↦ hosc ⟨k, hle⟩
    exact ⟨k.succ, ⟨hi₀_min, hi₀_ge, by linarith [(abs_lt.mp hk_step).2]⟩, hω⟩

private def dyadicCrossingSet {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a δ : ℝ) (n : ℕ)
    (i : Fin (2 ^ n + 1)) : Set Ω :=
  {ω | (∀ j < i, W (dyadicGrid t n j) ω < a) ∧
    a ≤ W (dyadicGrid t n i) ω ∧ W (dyadicGrid t n i) ω < a + δ}

private theorem measurableSet_dyadicCrossingSet {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ s, StronglyMeasurable (W s)) (t : ℝ≥0) (a δ : ℝ) (n : ℕ)
    (i : Fin (2 ^ n + 1)) :
    MeasurableSet[Filtration.natural W hWm (dyadicGrid t n i)]
      (dyadicCrossingSet W t a δ n i) := by
  let ℱ := Filtration.natural W hWm
  have hAd : Adapted ℱ W := (Filtration.stronglyAdapted_natural hWm).adapted
  have hA_eq : dyadicCrossingSet W t a δ n i =
      (⋂ j, ⋂ (_ : j < i), {ω | W (dyadicGrid t n j) ω < a}) ∩
        ({ω | a ≤ W (dyadicGrid t n i) ω} ∩ {ω | W (dyadicGrid t n i) ω < a + δ}) := by
    ext ω; simp [dyadicCrossingSet]
  rw [hA_eq]
  refine (MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun (hji : j < i) ↦ ?_).inter
    ((measurableSet_le measurable_const (hAd _)).inter
      (measurableSet_lt (hAd _) measurable_const))
  exact measurableSet_lt ((hAd _).mono (ℱ.mono (monotone_dyadicGrid t n hji.le)) le_rfl)
    measurable_const

private theorem two_mul_measure_add_ge_le_step {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P)
    (hWm : ∀ s, StronglyMeasurable (W s)) (hW0 : ∀ ω, W 0 ω = 0)
    (t : ℝ≥0) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (n : ℕ) :
    2 * P {ω | a + δ ≤ W t ω} ≤
      P {ω | ∃ s ≤ t, a ≤ W s ω} +
        2 * P {ω | ∃ k : Fin (2 ^ n),
          δ ≤ |W (dyadicGrid t n k.succ) ω - W (dyadicGrid t n k.castSucc) ω|} := by
  let ℱ := Filtration.natural W hWm
  have hWF := hW.isFilteredPreBrownianReal_natural hWm
  let g := dyadicGrid t n
  let N : Fin (2 ^ n + 1) := Fin.last (2 ^ n)
  let Osc : Set Ω := {ω | ∃ k : Fin (2 ^ n), δ ≤ |W (g k.succ) ω - W (g k.castSucc) ω|}
  let A := dyadicCrossingSet W t a δ n
  let D (i : Fin (2 ^ n + 1)) : Set Ω := A i ∩ {ω | a + δ ≤ W t ω}
  have hA_meas := measurableSet_dyadicCrossingSet hWm t a δ n
  have hA_disj : Pairwise fun i k ↦ Disjoint (A i) (A k) := fun i k hik ↦
    disjoint_left.mpr fun ω hi hk ↦ (lt_trichotomy i k).elim (fun h ↦ hi.2.1.not_gt (hk.1 i h))
      fun h ↦ h.elim hik fun h' ↦ hk.2.1.not_gt (hi.1 k h')
  have hD_meas (i : Fin (2 ^ n + 1)) : MeasurableSet (D i) :=
    (ℱ.le (g i) _ (hA_meas i)).inter (measurableSet_le measurable_const (hWm t).measurable)
  have hD_disj : Pairwise fun i k ↦ Disjoint (D i) (D k) :=
    fun i k hik ↦ (hA_disj hik).mono inter_subset_left inter_subset_left
  have hbound (i : Fin (2 ^ n + 1)) : 2 * P (D i) ≤ P (A i) := by
    let E : Set Ω := (W (g N) - W (g i)) ⁻¹' Ioi 0
    have hsub : D i ⊆ E ∩ A i := fun ω ⟨hA, (hWt : a + δ ≤ W t ω)⟩ ↦ ⟨by
      have hWt' : a + δ ≤ W (g N) ω := by simpa only [g, N, dyadicGrid_last] using hWt
      simp only [E, mem_preimage, mem_Ioi, Pi.sub_apply]; linarith [hA.2.2], hA⟩
    have hind := (Indep_iff _ _ _).mp (hWF.indep_sub (monotone_dyadicGrid t n (Fin.le_last i)))
      E (A i) ⟨Ioi 0, measurableSet_Ioi, rfl⟩ (hA_meas i)
    have hlaw : P E = gaussianReal 0 (g N - g i) (Ioi 0) :=
      (hW.hasLaw_sub_of_le (monotone_dyadicGrid t n (Fin.le_last i))).measure_eq
        (p := (· ∈ Ioi 0)) measurableSet_Ioi
    calc 2 * P (D i) ≤ 2 * P (E ∩ A i) := mul_le_mul_of_nonneg_left (measure_mono hsub) bot_le
      _ = (2 * gaussianReal 0 (g N - g i) (Ioi 0)) * P (A i) := by rw [hind, hlaw, mul_assoc]
      _ ≤ P (A i) := (mul_le_mul_of_nonneg_right
          (two_mul_gaussianReal_Ioi_le_one _) bot_le).trans_eq (one_mul _)
  have hA_sub : (⋃ i, A i) ⊆ {ω | ∃ s ≤ t, a ≤ W s ω} :=
    fun _ ⟨_, ⟨i, rfl⟩, _, hai, _⟩ ↦ ⟨g i, dyadicGrid_le t n i, hai⟩
  calc 2 * P {ω | a + δ ≤ W t ω}
      ≤ 2 * (P (⋃ i, D i) + P Osc) := mul_le_mul_of_nonneg_left
        ((measure_mono (subset_dyadicCrossing_union_osc hW0 t ha hδ n)).trans
          (measure_union_le _ _)) bot_le
    _ = (∑ i, 2 * P (D i)) + 2 * P Osc := by
        rw [mul_add, measure_iUnion hD_disj hD_meas, tsum_fintype, Finset.mul_sum]
    _ ≤ (∑ i, P (A i)) + 2 * P Osc := by gcongr with i; exact hbound i
    _ = P (⋃ i, A i) + 2 * P Osc := by
        rw [measure_iUnion hA_disj (fun i ↦ ℱ.le (g i) _ (hA_meas i)), tsum_fintype]
    _ ≤ P {ω | ∃ s ≤ t, a ≤ W s ω} + 2 * P Osc := add_le_add_left (measure_mono hA_sub) _

private theorem measure_exists_le_ge_of_continuous {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W P)
    (hWm : ∀ s, StronglyMeasurable (W s)) (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ s ≤ t, a ≤ W s ω} = 2 * P {ω | a ≤ W t ω} := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine le_antisymm (measure_exists_le_ge_le_of_continuous hW hWm hWc t a) ?_
  rcases eq_or_ne t 0 with rfl | ht0
  · have hemp : {ω | a ≤ W 0 ω} = ∅ := by
      ext ω; simp [hW0 ω, ha.not_ge]
    simp [hemp]
  have hδ_bound {δ : ℝ} (hδ : 0 < δ) :
      2 * P {ω | a + δ ≤ W t ω} ≤ P {ω | ∃ s ≤ t, a ≤ W s ω} := by
    have hosc := ENNReal.Tendsto.const_mul (tendsto_measure_dyadicOsc P hWm hWc t hδ)
      (a := 2) (Or.inr ENNReal.ofNat_ne_top)
    rw [mul_zero] at hosc
    have hrhs := (tendsto_const_nhds (x := P {ω | ∃ s ≤ t, a ≤ W s ω})).add hosc
    rw [add_zero] at hrhs
    exact ge_of_tendsto hrhs (Eventually.of_forall fun n ↦
      two_mul_measure_add_ge_le_step hW hWm hW0 t ha hδ n)
  let H (m : ℕ) : Set Ω := {ω | a + 1 / (m + 1 : ℝ) ≤ W t ω}
  have hH_mono : Monotone H := fun m₁ m₂ hm ω (hω : a + 1 / (m₁ + 1 : ℝ) ≤ W t ω) ↦ by
    have hle : (1 : ℝ) / (m₂ + 1) ≤ 1 / (m₁ + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    exact (add_le_add_right hle a).trans hω
  have hH_union : (⋃ m, H m) = {ω | a < W t ω} := by
    ext ω; simp only [mem_iUnion, mem_ofPred_eq, H]
    refine ⟨fun ⟨m, hm⟩ ↦ (lt_add_of_pos_right a (by positivity)).trans_le hm, fun h ↦ ?_⟩
    have htend : Tendsto (fun m : ℕ ↦ a + 1 / (m + 1 : ℝ)) atTop (𝓝 a) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := a)).add tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds h)).exists
    exact ⟨m, hm.le⟩
  have hgt_le : 2 * P {ω | a < W t ω} ≤ P {ω | ∃ s ≤ t, a ≤ W s ω} := by
    rw [← hH_union]
    exact le_of_tendsto' (ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop (μ := P) hH_mono)
      (Or.inr ENNReal.ofNat_ne_top)) fun m ↦ hδ_bound (by positivity)
  have := nullSingletonClass_gaussianReal (μ := 0) ht0
  have heq : P {ω | a ≤ W t ω} = P {ω | a < W t ω} := by
    have h₁ := (hW.hasLaw_eval t).measure_eq (p := (· ∈ Ici a)) measurableSet_Ici
    have h₂ := (hW.hasLaw_eval t).measure_eq (p := (· ∈ Ioi a)) measurableSet_Ioi
    exact h₁.trans ((measure_congr Ioi_ae_eq_Ici.symm).trans h₂.symm)
  rwa [heq]

private theorem ae_eq_setOf_exists_le_of_indist {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W B : ℝ≥0 → Ω → ℝ} (hWB : W ≡ᵐ[P] B) (t : ℝ≥0) (q : ℝ → Prop) :
    {ω | ∃ s ≤ t, q (B s ω)} =ᵐ[P] {ω | ∃ s ≤ t, q (W s ω)} := by
  filter_upwards [hWB] with ω hω
  exact exists_congr fun s ↦ and_congr_right fun _ ↦ by rw [hω s]

private theorem ae_eq_setOf_eval_of_indist {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {W B : ℝ≥0 → Ω → ℝ} (hWB : W ≡ᵐ[P] B) (t : ℝ≥0) (q : ℝ → Prop) :
    {ω | q (B t ω)} =ᵐ[P] {ω | q (W t ω)} := by
  filter_upwards [hWB.ae_eq_eval t] with ω hω
  simp only [hω]

end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For any real level `a` and time `t`, the probability that a real Brownian motion strictly
exceeds `a` by time `t` is at most twice `P {ω | a < B t ω}`. -/
theorem measure_exists_le_gt_le (hB : IsBrownianReal B P) (t : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ t, a < B s ω} ≤ 2 * P {ω | a < B t ω} := by
  obtain ⟨W, _, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  rw [measure_congr (ae_eq_setOf_exists_le_of_indist hWB t (a < ·)),
    measure_congr (ae_eq_setOf_eval_of_indist hWB t (a < ·))]
  exact measure_exists_le_gt_le_of_continuous hW.toIsPreBrownianReal hWc t a

/-- For any real level `a` and time `t`, the probability that a real Brownian motion reaches `a`
by time `t` is at most twice `P {ω | a ≤ B t ω}`. -/
theorem measure_exists_le_ge_le (hB : IsBrownianReal B P) (t : ℝ≥0) (a : ℝ) :
    P {ω | ∃ s ≤ t, a ≤ B s ω} ≤ 2 * P {ω | a ≤ B t ω} := by
  obtain ⟨W, hWm, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  rw [measure_congr (ae_eq_setOf_exists_le_of_indist hWB t (a ≤ ·)),
    measure_congr (ae_eq_setOf_eval_of_indist hWB t (a ≤ ·))]
  exact measure_exists_le_ge_le_of_continuous hW.toIsPreBrownianReal hWm hWc t a

/-- **Reflection principle for real Brownian motion**: for every positive level `a > 0` and time
`t ≥ 0` (including `t = 0`, where both sides vanish), the probability of reaching `a` by time `t`
equals twice the probability of lying at or above `a` at time `t`. -/
theorem measure_exists_le_ge (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ s ≤ t, a ≤ B s ω} = 2 * P {ω | a ≤ B t ω} := by
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  rw [measure_congr (ae_eq_setOf_exists_le_of_indist hWB t (a ≤ ·)),
    measure_congr (ae_eq_setOf_eval_of_indist hWB t (a ≤ ·))]
  exact measure_exists_le_ge_of_continuous hW.toIsPreBrownianReal hWm hWc hW0 t ha

/-- Real-valued form of the Brownian reflection principle for `a > 0`. -/
theorem measureReal_exists_le_ge (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ s ≤ t, a ≤ B s ω} = 2 * P.real {ω | a ≤ B t ω} := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [measureReal_def, hB.measure_exists_le_ge t ha,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← measureReal_def]

/-- Strict-exceedance reflection principle for every nonnegative level `a ≥ 0` and time `t ≥ 0`. -/
theorem measure_exists_le_gt (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    P {ω | ∃ s ≤ t, a < B s ω} = 2 * P {ω | a < B t ω} := by
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  rw [measure_congr (ae_eq_setOf_exists_le_of_indist hWB t (a < ·)),
    measure_congr (ae_eq_setOf_eval_of_indist hWB t (a < ·))]
  let F (m : ℕ) : Set Ω := {ω | ∃ s ≤ t, a + 1 / (m + 1 : ℝ) ≤ W s ω}
  let G (m : ℕ) : Set Ω := {ω | a + 1 / (m + 1 : ℝ) ≤ W t ω}
  have hF_mono : Monotone F := fun m₁ m₂ hm ω ⟨s, hst, hs⟩ ↦ by
    have hle : (1 : ℝ) / (m₂ + 1) ≤ 1 / (m₁ + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    exact ⟨s, hst, (add_le_add_right hle a).trans hs⟩
  have hG_mono : Monotone G := fun m₁ m₂ hm ω (hω : a + 1 / (m₁ + 1 : ℝ) ≤ W t ω) ↦ by
    have hle : (1 : ℝ) / (m₂ + 1) ≤ 1 / (m₁ + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)
    exact (add_le_add_right hle a).trans hω
  have htend : Tendsto (fun m : ℕ ↦ a + 1 / (m + 1 : ℝ)) atTop (𝓝 a) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := a)).add tendsto_one_div_add_atTop_nhds_zero_nat
  have hF_union : (⋃ m, F m) = {ω | ∃ s ≤ t, a < W s ω} := by
    ext ω; simp only [mem_iUnion, mem_ofPred_eq, F]
    refine ⟨fun ⟨m, s, hst, hs⟩ ↦ ⟨s, hst, (lt_add_of_pos_right a (by positivity)).trans_le hs⟩,
      fun ⟨s, hst, hs⟩ ↦ ?_⟩
    obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds hs)).exists
    exact ⟨m, s, hst, hm.le⟩
  have hG_union : (⋃ m, G m) = {ω | a < W t ω} := by
    ext ω; simp only [mem_iUnion, mem_ofPred_eq, G]
    refine ⟨fun ⟨m, hm⟩ ↦ (lt_add_of_pos_right a (by positivity)).trans_le hm, fun hs ↦ ?_⟩
    obtain ⟨m, hm⟩ := (htend.eventually (gt_mem_nhds hs)).exists
    exact ⟨m, hm.le⟩
  rw [← hF_union, ← hG_union]
  refine tendsto_nhds_unique (tendsto_measure_iUnion_atTop (μ := P) hF_mono) ?_
  have hlim := ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop (μ := P) hG_mono)
    (a := 2) (Or.inr ENNReal.ofNat_ne_top)
  refine hlim.congr fun m ↦ ?_
  exact (measure_exists_le_ge_of_continuous hW.toIsPreBrownianReal hWm hWc hW0 t
    (add_pos_of_nonneg_of_pos ha (by positivity))).symm

/-- Reflection principle for reaching a negative level `a < 0` by time `t`. -/
theorem measure_exists_le_le (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : a < 0) :
    P {ω | ∃ s ≤ t, B s ω ≤ a} = 2 * P {ω | B t ω ≤ a} := by
  simpa only [Pi.neg_apply, neg_le_neg_iff] using hB.neg.measure_exists_le_ge t (neg_pos.mpr ha)

/-- Strict-crossing reflection principle below any nonpositive level `a ≤ 0` by time `t`. -/
theorem measure_exists_le_lt (hB : IsBrownianReal B P) (t : ℝ≥0) {a : ℝ} (ha : a ≤ 0) :
    P {ω | ∃ s ≤ t, B s ω < a} = 2 * P {ω | B t ω < a} := by
  simpa only [Pi.neg_apply, neg_lt_neg_iff] using
    hB.neg.measure_exists_le_gt t (neg_nonneg.mpr ha)

/-- **Immediate positive crossing of Brownian motion**: a real Brownian motion enters `(0, ∞)`
immediately after time `0` almost surely. -/
theorem hittingAfter_Ioi_zero_ae_eq_zero (hB : IsBrownianReal B P) :
    hittingAfter B (Ioi 0) 0 =ᵐ[P] 0 := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, _, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  refine (hWB.symm.hittingAfter_ae_eq (Ioi 0) 0).trans ?_
  have hstep (m : ℕ) : ∀ᵐ ω ∂P, ∃ s ≤ (1 / (m + 1 : ℝ≥0)), 0 < W s ω := by
    let tm : ℝ≥0 := 1 / (m + 1)
    have htm : tm ≠ 0 := one_div_ne_zero (Nat.cast_add_one_ne_zero m)
    have hm_meas : MeasurableSet {ω | ∃ s ≤ tm, 0 < W s ω} :=
      measurableSet_exists_le_gt hWm hWc tm 0
    rw [ae_iff, ← compl_ofPred, prob_compl_eq_zero_iff hm_meas,
      hW.measure_exists_le_gt tm le_rfl,
      (hW.hasLaw_eval tm).measure_eq (p := (0 < ·)) measurableSet_Ioi]
    exact two_mul_gaussianReal_Ioi_eq_one htm
  have htend_nn : Tendsto (fun m : ℕ ↦ (1 / (m + 1 : ℝ≥0) : ℝ≥0)) atTop (𝓝 0) := by
    rw [← NNReal.tendsto_coe]
    simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_zero] using tendsto_one_div_add_atTop_nhds_zero_nat
  have htend : Tendsto (fun m : ℕ ↦ ((1 / (m + 1 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)) atTop
      (𝓝 ((0 : ℝ≥0) : WithTop ℝ≥0)) :=
    (WithTop.continuous_coe.tendsto 0).comp htend_nn
  filter_upwards [ae_all_iff.mpr hstep] with ω hω
  refine le_antisymm (ge_of_tendsto htend (Eventually.of_forall fun m ↦ ?_)) bot_le
  obtain ⟨s, hsm, hs0⟩ := hω m
  exact (hittingAfter_le_of_mem (bot_le : (0 : ℝ≥0) ≤ s) hs0).trans (WithTop.coe_le_coe.mpr hsm)

/-- **Immediate negative crossing of Brownian motion**: a real Brownian motion enters `(-∞, 0)`
immediately after time `0` almost surely. -/
theorem hittingAfter_Iio_zero_ae_eq_zero (hB : IsBrownianReal B P) :
    hittingAfter B (Iio 0) 0 =ᵐ[P] 0 := by
  refine Filter.EventuallyEq.trans ?_ hB.neg.hittingAfter_Ioi_zero_ae_eq_zero
  classical
  refine Eventually.of_forall fun ω ↦ ?_
  rw [hittingAfter_def, hittingAfter_def]
  simp only [Pi.neg_apply, mem_Iio, mem_Ioi, Right.neg_pos_iff]

/-- For every time `t ≥ 0` (including `t = 0`), the running maximum `⨆ s : Set.Iic t, B s ω` of a
real Brownian motion has the same law as `|B t|`, namely `(gaussianReal 0 t).map (|·|)`. -/
theorem hasLaw_iSup_Iic_eq_map_abs (hB : IsBrownianReal B P) (t : ℝ≥0) :
    HasLaw (fun ω ↦ ⨆ s : Iic t, B s ω) ((gaussianReal 0 t).map (|·|)) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨W, hWm, hWc, hW0, hW, hWB⟩ := hB.exists_stronglyMeasurable_continuous_indist
  have : Nonempty (Iic t) := ⟨⟨0, mem_Iic.mpr bot_le⟩⟩
  have hIic : Iic t = Icc 0 t := by ext s; simp
  have : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (hIic ▸ isCompact_Icc)
  let M : Ω → ℝ := fun ω ↦ ⨆ s : Iic t, W s ω
  have hbdd (ω : Ω) : BddAbove (range fun s : Iic t ↦ W s ω) :=
    (isCompact_range ((hWc ω).comp continuous_subtype_val)).bddAbove
  have hM_le (x : ℝ) : M ⁻¹' Iic x = {ω | ∃ s ≤ t, x < W s ω}ᶜ := by
    ext ω
    simp only [M, mem_preimage, mem_Iic, mem_compl_iff, mem_ofPred_eq, ciSup_le_iff (hbdd ω),
      Subtype.forall, not_exists, not_and, not_lt]
  have hM_meas : Measurable M := measurable_of_Iic fun x ↦ by
    rw [hM_le x]; exact (measurableSet_exists_le_gt hWm hWc t x).compl
  have hMB_ae : M =ᵐ[P] fun ω ↦ ⨆ s : Iic t, B s ω := by
    filter_upwards [hWB] with ω hω; simp only [M, hω]
  refine ⟨hM_meas.aemeasurable.congr hMB_ae, (Measure.map_congr hMB_ae.symm).trans ?_⟩
  have : IsProbabilityMeasure (P.map M) :=
    (Measure.isProbabilityMeasure_map_iff hM_meas.aemeasurable).mpr ‹_›
  have : IsProbabilityMeasure ((gaussianReal 0 t).map (|·|)) :=
    (Measure.isProbabilityMeasure_map_iff continuous_abs.measurable.aemeasurable).mpr inferInstance
  refine Measure.eq_of_cdf _ _ (StieltjesFunction.ext fun x ↦ ?_)
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply hM_meas measurableSet_Iic]
  rcases lt_or_ge x 0 with hx | hx
  · have h₁ : M ⁻¹' Iic x = ∅ := eq_empty_of_forall_notMem fun ω hω ↦
      (hx.trans_le ((hW0 ω).symm.trans_le (le_ciSup (hbdd ω) ⟨0, mem_Iic.mpr bot_le⟩))).not_ge hω
    have h₂ : (|·|) ⁻¹' Iic x = (∅ : Set ℝ) :=
      eq_empty_of_forall_notMem fun y hy ↦ (hx.trans_le (abs_nonneg y)).not_ge hy
    rw [map_measureReal_apply continuous_abs.measurable measurableSet_Iic, h₁, h₂,
      measureReal_empty, measureReal_empty]
  · rw [hM_le x, probReal_compl_eq_one_sub (measurableSet_exists_le_gt hWm hWc t x),
      measureReal_def, hW.measure_exists_le_gt t hx,
      (hW.hasLaw_eval t).measure_eq (p := (x < ·)) measurableSet_Ioi,
      ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← measureReal_def,
      gaussianReal_map_abs_measureReal_Iic t hx]
    rfl

/-- At positive time `t ≠ 0`, the running maximum `⨆ s : Set.Iic t, B s ω` of a real Brownian
motion has the folded normal law `foldedNormalMeasure 0 √t`. -/
theorem hasLaw_iSup_Iic (hB : IsBrownianReal B P) {t : ℝ≥0} (ht : t ≠ 0) :
    HasLaw (fun ω ↦ ⨆ s : Iic t, B s ω) (foldedNormalMeasure 0 √(t : ℝ)) P :=
  gaussianReal_map_abs_eq_foldedNormalMeasure 0 ht ▸ hB.hasLaw_iSup_Iic_eq_map_abs t

end ProbabilityTheory.IsBrownianReal
