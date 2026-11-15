/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Probability.Martingale.Local.Arithmetic
public import TauCeti.Probability.Martingale.Local.Bounded
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.Stopping

/-!
# Continuous local martingales of finite variation are constant

Under a finite measure, any almost-surely continuous native local martingale on `ℝ≥0` whose sample
paths have bounded variation on every compact interval `[0, T]` is indistinguishable from its
initial value. Neither right continuity nor completeness of the filtration is required, and no
integrability or measurability assumption is imposed on the initial value.

The proof proceeds in three stages:

1. For a bounded centered real martingale `W`, stopping at the first dyadic grid point where the
   discrete variation on `[0, T]` exceeds `M` produces a countable-range stopping time `σ` whose
   stopped squared increments sum to at most `(M + 2 C) · max_i |Δ_i W|`. Uniform continuity on
   `[0, T]` and dominated convergence send `∫ (W^σ_T)² dP` to zero as the dyadic mesh vanishes;
   Fatou's lemma and exhaustion in `M` force `W_T = 0` almost everywhere.
2. Bounded native localization (`exists_isLocalizingSequence_bounded_martingale`) extends the real
   result to arbitrary continuous real local martingales of locally bounded variation.
3. Hahn–Banach separation (`MeasureTheory.ae_eq_zero_of_forall_dual_of_isSeparable`) lifts the
   vanishing theorem to continuous local martingales in any real Banach space `E`.

Specializations cover `LocallyBoundedVariationOn`, almost-surely zero initial values, true
martingales, and real local martingales with almost-surely monotone or antitone paths.

## References

* Daniel Revuz and Marc Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Proposition 1.2.
* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.Locally

section DyadicHelpers

private def dyadicPt (T : ℝ≥0) (k j : ℕ) : ℝ≥0 :=
  ((min j (2 ^ k) : ℕ) : ℝ≥0) / (2 ^ k : ℝ≥0) * T

private theorem dyadicPt_mono (T : ℝ≥0) (k : ℕ) : Monotone (dyadicPt T k) := by
  intro i j hij
  dsimp only [dyadicPt]
  gcongr

private theorem dyadicPt_zero (T : ℝ≥0) (k : ℕ) : dyadicPt T k 0 = 0 := by
  simp [dyadicPt]

private theorem dyadicPt_end (T : ℝ≥0) (k : ℕ) : dyadicPt T k (2 ^ k) = T := by
  have hpos : (2 ^ k : ℝ≥0) ≠ 0 := pow_ne_zero k two_ne_zero
  simp [dyadicPt, hpos]

private theorem dyadicPt_mem_Icc (T : ℝ≥0) (k j : ℕ) : dyadicPt T k j ∈ Icc 0 T := by
  refine ⟨bot_le, ?_⟩
  have hpos : (2 ^ k : ℝ≥0) ≠ 0 := pow_ne_zero k two_ne_zero
  have hle : ((min j (2 ^ k) : ℕ) : ℝ≥0) ≤ (2 ^ k : ℝ≥0) := by
    exact_mod_cast min_le_right j (2 ^ k)
  have hdiv : ((min j (2 ^ k) : ℕ) : ℝ≥0) / (2 ^ k : ℝ≥0) ≤ 1 :=
    (div_le_one₀ (pos_iff_ne_zero.2 hpos)).2 hle
  simpa only [dyadicPt, one_mul] using mul_le_mul_of_nonneg_right hdiv bot_le

private theorem dist_dyadicPt_succ_le (T : ℝ≥0) (k i : ℕ) :
    dist (dyadicPt T k (i + 1)) (dyadicPt T k i) ≤ (T : ℝ) / (2 : ℝ) ^ k := by
  have hle : dyadicPt T k i ≤ dyadicPt T k (i + 1) := dyadicPt_mono T k i.le_succ
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hle))]
  have hstep : ((min (i + 1) (2 ^ k) : ℕ) : ℝ) - ((min i (2 ^ k) : ℕ) : ℝ) ≤ 1 := by
    have hnat : min (i + 1) (2 ^ k) ≤ min i (2 ^ k) + 1 := by omega
    have hcast : ((min (i + 1) (2 ^ k) : ℕ) : ℝ) ≤ ((min i (2 ^ k) : ℕ) : ℝ) + 1 := by
      exact_mod_cast hnat
    linarith
  have hexp : (dyadicPt T k (i + 1) : ℝ) - (dyadicPt T k i : ℝ) =
      (((min (i + 1) (2 ^ k) : ℕ) : ℝ) - ((min i (2 ^ k) : ℕ) : ℝ)) *
        ((T : ℝ) / (2 : ℝ) ^ k) := by
    simp only [dyadicPt, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat,
      NNReal.coe_natCast]
    ring
  rw [hexp]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hstep (by positivity : 0 ≤ (T : ℝ) / (2 : ℝ) ^ k)

private def gridOsc {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) : ℝ≥0 :=
  (Finset.range (2 ^ k)).sup fun i ↦ ‖W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω‖₊

private theorem abs_sub_le_gridOsc {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k i : ℕ}
    (hi : i ∈ Finset.range (2 ^ k)) (ω : Ω) :
    |W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω| ≤ (gridOsc W T k ω : ℝ) := by
  simpa only [gridOsc, Real.norm_eq_abs, coe_nnNorm] using
    NNReal.coe_le_coe.2 (Finset.le_sup
      (f := fun j ↦ ‖W (dyadicPt T k (j + 1)) ω - W (dyadicPt T k j) ω‖₊) hi)

private theorem stronglyMeasurable_gridOsc {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, StronglyMeasurable (W t)) (T : ℝ≥0) (k : ℕ) :
    StronglyMeasurable fun ω ↦ (gridOsc W T k ω : ℝ) := by
  suffices ∀ s : Finset ℕ, StronglyMeasurable fun ω ↦
      ((s.sup fun i ↦ ‖W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω‖₊ : ℝ≥0) : ℝ) from
    this (Finset.range (2 ^ k))
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => simpa using stronglyMeasurable_const
  | insert a s _ ih =>
    have ha_meas : StronglyMeasurable fun ω ↦
        (‖W (dyadicPt T k (a + 1)) ω - W (dyadicPt T k a) ω‖₊ : ℝ) :=
      ((hW _).sub (hW _)).norm
    convert ha_meas.sup ih using 1
    ext ω
    simp [Finset.sup_insert]

private def gridVar {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k j : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range j, |W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω|

private theorem gridVar_mono {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    Monotone fun j ↦ gridVar W T k j ω := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) fun _ _ _ ↦ abs_nonneg _

open scoped Classical in
private def gridStop {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k M : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  (Finset.range (2 ^ k + 1)).inf fun j ↦
    if (M : ℝ) < gridVar W T k j ω then (dyadicPt T k j : WithTop ℝ≥0) else ⊤

open scoped Classical in
private theorem isStoppingTime_gridStop {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} (hW : StronglyAdapted ℱ W) (T : ℝ≥0) (k M : ℕ) :
    IsStoppingTime ℱ (gridStop W T k M) := by
  have hterm (j : ℕ) : IsStoppingTime ℱ (fun ω ↦
      if (M : ℝ) < gridVar W T k j ω then (dyadicPt T k j : WithTop ℝ≥0) else ⊤) := by
    intro t
    by_cases hjt : dyadicPt T k j ≤ t
    · have hmeas : StronglyMeasurable[ℱ (dyadicPt T k j)] (gridVar W T k j) := by
        let : MeasurableSpace Ω := ℱ (dyadicPt T k j)
        have hsum := Finset.stronglyMeasurable_sum (Finset.range j) fun i hi ↦ by
          have hij : i + 1 ≤ j := Nat.succ_le_of_lt (Finset.mem_range.1 hi)
          exact (((hW _).mono (ℱ.mono (dyadicPt_mono T k hij))).sub
            ((hW _).mono (ℱ.mono (dyadicPt_mono T k (i.le_succ.trans hij))))).norm
        convert hsum using 1
        ext ω
        simp [gridVar, Finset.sum_apply, Real.norm_eq_abs]
      have heq : {ω | (if (M : ℝ) < gridVar W T k j ω
          then (dyadicPt T k j : WithTop ℝ≥0) else ⊤) ≤ (t : WithTop ℝ≥0)} =
          {ω | (M : ℝ) < gridVar W T k j ω} := by
        ext ω
        simp only [mem_ofPred_eq]
        split_ifs with h
        · exact iff_of_true (WithTop.coe_le_coe.2 hjt) h
        · exact iff_of_false (not_le_of_gt (WithTop.coe_lt_top t)) h
      rw [heq]
      exact ℱ.mono hjt _ (measurableSet_lt measurable_const hmeas.measurable)
    · have heq : {ω | (if (M : ℝ) < gridVar W T k j ω
          then (dyadicPt T k j : WithTop ℝ≥0) else ⊤) ≤ (t : WithTop ℝ≥0)} = ∅ := by
        refine eq_empty_of_forall_notMem fun x hω ↦ ?_
        simp only [mem_ofPred_eq] at hω
        split_ifs at hω
        · exact hjt (WithTop.coe_le_coe.1 hω)
        · exact not_le_of_gt (WithTop.coe_lt_top t) hω
      rw [heq]
      exact @MeasurableSet.empty _ (ℱ t)
  exact (Finset.range (2 ^ k + 1)).isStoppingTime_inf fun j _ ↦ hterm j

open scoped Classical in
private theorem gridStop_eq_of_exists {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k M : ℕ} {ω : Ω}
    (hex : ∃ i, i < 2 ^ k + 1 ∧ (M : ℝ) < gridVar W T k i ω) :
    gridStop W T k M ω = dyadicPt T k (Nat.find hex) := by
  have hj₀spec := Nat.find_spec hex
  apply le_antisymm
  · refine (Finset.inf_le (Finset.mem_range.2 hj₀spec.1)).trans_eq ?_
    split_ifs with h
    · rfl
    · exact absurd hj₀spec.2 h
  · refine Finset.le_inf fun i hi ↦ ?_
    split_ifs with hi'
    · exact WithTop.coe_le_coe.2 (dyadicPt_mono T k
        (Nat.find_min' hex ⟨Finset.mem_range.1 hi, hi'⟩))
    · exact le_top

open scoped Classical in
private theorem gridStop_eq_top_of_gridVar_le {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k M : ℕ}
    {ω : Ω} (h : gridVar W T k (2 ^ k) ω ≤ M) : gridStop W T k M ω = ⊤ := by
  refine le_antisymm le_top (Finset.le_inf fun j hj ↦ ?_)
  have hjle : j ≤ 2 ^ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hle : gridVar W T k j ω ≤ M := (gridVar_mono W T k ω hjle).trans h
  split_ifs with hlt
  · exact absurd hlt (not_lt.2 hle)
  · exact le_rfl

open scoped Classical in
private theorem countable_range_gridStop {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (k M : ℕ) :
    (range (gridStop W T k M)).Countable := by
  let S : Finset (WithTop ℝ≥0) :=
    insert ⊤ ((Finset.range (2 ^ k + 1)).image fun j ↦ (dyadicPt T k j : WithTop ℝ≥0))
  refine S.countable_toSet.mono ?_
  rintro _ ⟨ω, rfl⟩
  by_cases hex : ∃ i, i < 2 ^ k + 1 ∧ (M : ℝ) < gridVar W T k i ω
  · rw [gridStop_eq_of_exists hex]
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.find_spec hex).1)))
  · have hle : gridVar W T k (2 ^ k) ω ≤ M :=
      not_lt.1 fun h ↦ hex ⟨2 ^ k, Nat.lt_succ_self _, h⟩
    rw [gridStop_eq_top_of_gridVar_le hle]
    exact Finset.mem_coe.2 (Finset.mem_insert_self _ _)

private theorem abs_sub_le_two_mul {x y C : ℝ} (hx : |x| ≤ C) (hy : |y| ≤ C) :
    |x - y| ≤ 2 * C := by
  rw [abs_le] at hx hy ⊢
  constructor <;> linarith

private theorem stopped_grid_sub_eq {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k j₀ i : ℕ}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} (hstop : τ ω = dyadicPt T k j₀) :
    stoppedProcess W τ (dyadicPt T k (i + 1)) ω - stoppedProcess W τ (dyadicPt T k i) ω =
      if i < j₀ then W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω else 0 := by
  split_ifs with hi
  · rw [stoppedProcess_eq_of_le (hstop ▸ WithTop.coe_le_coe.2
        (dyadicPt_mono T k (Nat.succ_le_of_lt hi))),
      stoppedProcess_eq_of_le (hstop ▸ WithTop.coe_le_coe.2 (dyadicPt_mono T k hi.le))]
  · have hji : j₀ ≤ i := not_lt.1 hi
    rw [stoppedProcess_eq_of_ge (hstop ▸ WithTop.coe_le_coe.2
        (dyadicPt_mono T k (hji.trans i.le_succ))),
      stoppedProcess_eq_of_ge (hstop ▸ WithTop.coe_le_coe.2 (dyadicPt_mono T k hji)), sub_self]

open scoped Classical in
private theorem stopped_grid_inc_le_and_sum_le {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k M : ℕ}
    {C : ℝ} {ω : Ω} (hb : ∀ t, |W t ω| ≤ C) :
    let Z := stoppedProcess W (gridStop W T k M)
    (∀ i ∈ Finset.range (2 ^ k),
      |Z (dyadicPt T k (i + 1)) ω - Z (dyadicPt T k i) ω| ≤ (gridOsc W T k ω : ℝ)) ∧
    ∑ i ∈ Finset.range (2 ^ k), |Z (dyadicPt T k (i + 1)) ω - Z (dyadicPt T k i) ω| ≤
      M + 2 * C := by
  intro Z
  by_cases hex : ∃ i, i < 2 ^ k + 1 ∧ (M : ℝ) < gridVar W T k i ω
  · let j₀ := Nat.find hex
    have hj₀pos : 0 < j₀ := by
      by_contra h0
      have hlt0 : (M : ℝ) < gridVar W T k 0 ω := (Nat.eq_zero_of_not_pos h0) ▸ (Nat.find_spec hex).2
      have : (M : ℝ) < 0 := by simpa [gridVar] using hlt0
      linarith [Nat.cast_nonneg (α := ℝ) M]
    have hinc (i : ℕ) := stopped_grid_sub_eq (W := W) (i := i) (gridStop_eq_of_exists hex)
    refine ⟨fun i hi ↦ by rw [hinc i]; split_ifs; exacts [abs_sub_le_gridOsc hi ω, by simp], ?_⟩
    have hprev : gridVar W T k (j₀ - 1) ω ≤ M :=
      not_lt.1 fun h ↦ Nat.find_min hex (Nat.sub_lt hj₀pos zero_lt_one)
        ⟨(Nat.sub_lt hj₀pos zero_lt_one).trans (Nat.find_spec hex).1, h⟩
    calc ∑ i ∈ Finset.range (2 ^ k), |Z (dyadicPt T k (i + 1)) ω - Z (dyadicPt T k i) ω|
        = ∑ i ∈ (Finset.range (2 ^ k)).filter (· < j₀),
            |W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω| := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [hinc i]; split_ifs <;> simp
      _ ≤ ∑ i ∈ Finset.range j₀, |W (dyadicPt T k (i + 1)) ω - W (dyadicPt T k i) ω| :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi ↦ Finset.mem_range.2 (Finset.mem_filter.1 hi).2) fun _ _ _ ↦ abs_nonneg _
      _ = gridVar W T k (j₀ - 1) ω + |W (dyadicPt T k j₀) ω - W (dyadicPt T k (j₀ - 1)) ω| := by
          conv_lhs => rw [← Nat.sub_add_cancel hj₀pos]
          rw [Finset.sum_range_succ, Nat.sub_add_cancel hj₀pos]
          rfl
      _ ≤ M + 2 * C := add_le_add hprev (abs_sub_le_two_mul (hb _) (hb _))
  · have hle : gridVar W T k (2 ^ k) ω ≤ M := not_lt.1 fun h ↦ hex ⟨2 ^ k, Nat.lt_succ_self _, h⟩
    have hZeq (t : ℝ≥0) : Z t ω = W t ω :=
      stoppedProcess_eq_of_le ((gridStop_eq_top_of_gridVar_le hle) ▸ le_top)
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · rw [hZeq, hZeq]
      exact abs_sub_le_gridOsc hi ω
    · simp_rw [hZeq]
      exact hle.trans (by linarith [(abs_nonneg (W 0 ω)).trans (hb 0)])

open scoped Classical in
private theorem stopped_grid_sq_sum_le {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {k M : ℕ}
    {C : ℝ} {ω : Ω} (hC0 : 0 ≤ C) (hb : ∀ t, |W t ω| ≤ C) :
    let Z := stoppedProcess W (gridStop W T k M)
    ∑ i ∈ Finset.range (2 ^ k), (Z (dyadicPt T k (i + 1)) ω - Z (dyadicPt T k i) ω) ^ 2 ≤
      (M + 2 * C) * (gridOsc W T k ω : ℝ) ∧
      (M + 2 * C) * (gridOsc W T k ω : ℝ) ≤ 2 * C * (M + 2 * C) := by
  intro Z
  have hosc_le : (gridOsc W T k ω : ℝ) ≤ 2 * C := by
    let B : ℝ≥0 := ⟨2 * C, by positivity⟩
    have hBle : gridOsc W T k ω ≤ B := Finset.sup_le fun i _ ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs]
      exact abs_sub_le_two_mul (hb _) (hb _)
    exact NNReal.coe_le_coe.2 hBle
  have hstep := stopped_grid_inc_le_and_sum_le (T := T) (k := k) (M := M) hb
  have : 0 ≤ (M : ℝ) + 2 * C := by positivity
  refine ⟨?_, by nlinarith⟩
  calc ∑ i ∈ Finset.range (2 ^ k), (Z (dyadicPt T k (i + 1)) ω - Z (dyadicPt T k i) ω) ^ 2
      ≤ ∑ i ∈ Finset.range (2 ^ k),
          (gridOsc W T k ω : ℝ) * |Z (dyadicPt T k (i + 1)) ω - Z (dyadicPt T k i) ω| := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        rw [← sq_abs]
        simpa only [sq] using mul_le_mul_of_nonneg_right (hstep.1 i hi) (abs_nonneg _)
    _ = (gridOsc W T k ω : ℝ) * ∑ i ∈ Finset.range (2 ^ k),
          |Z (dyadicPt T k (i + 1)) ω - Z (dyadicPt T k i) ω| := (Finset.mul_sum ..).symm
    _ ≤ (gridOsc W T k ω : ℝ) * (M + 2 * C) :=
        mul_le_mul_of_nonneg_left hstep.2 (NNReal.coe_nonneg _)
    _ = (M + 2 * C) * (gridOsc W T k ω : ℝ) := mul_comm _ _

private theorem tendsto_gridOsc {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hf : Continuous (W · ω)) :
    Tendsto (fun k : ℕ ↦ (gridOsc W T k ω : ℝ)) atTop (𝓝 0) := by
  have huc : UniformContinuousOn (W · ω) (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  have hmesh : Tendsto (fun k : ℕ ↦ (T : ℝ) / (2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hmesh δ hδ
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
  let B : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
  have hle : (gridOsc W T k ω : ℝ) ≤ (B : ℝ) := NNReal.coe_le_coe.2 <| Finset.sup_le fun i _ ↦ by
    rw [← NNReal.coe_le_coe, coe_nnNorm, Real.norm_eq_abs, ← Real.dist_eq]
    have hd : dist (dyadicPt T k (i + 1)) (dyadicPt T k i) < δ :=
      (dist_dyadicPt_succ_le T k i).trans_lt (by
        simpa [Real.dist_eq, abs_of_nonneg (by positivity : 0 ≤ (T : ℝ) / (2 : ℝ) ^ k)] using
          hN k hk)
    exact (hmod _ (dyadicPt_mem_Icc T k (i + 1)) _ (dyadicPt_mem_Icc T k i) hd).le
  exact lt_of_le_of_lt hle (half_lt_self hε)

end DyadicHelpers

section RealEngine

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ}

private theorem tendsto_integral_stopped_gridStop_sq {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W ℱ P) (hW0 : ∀ ω, W 0 ω = 0) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, |W t ω| ≤ C) (hc : ∀ᵐ ω ∂P, Continuous (W · ω)) (T : ℝ≥0) (M : ℕ) :
    Tendsto (fun k : ℕ ↦ ∫ ω, (stoppedProcess W (gridStop W T k M) T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let g (k : ℕ) (ω : Ω) := ((M : ℝ) + 2 * C) * (gridOsc W T k ω : ℝ)
  have hg_meas (k : ℕ) : AEStronglyMeasurable (g k) P :=
    (stronglyMeasurable_const.mul
      (stronglyMeasurable_gridOsc (fun t ↦ (hW.stronglyAdapted t).mono (ℱ.le t))
        T k)).aestronglyMeasurable
  have hg_bound (k : ℕ) : ∀ᵐ ω ∂P, ‖g k ω‖ ≤ 2 * C * (M + 2 * C) := by
    filter_upwards [hb] with ω hω
    have hnn : 0 ≤ g k ω := mul_nonneg (by positivity) (NNReal.coe_nonneg _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnn] using
      (stopped_grid_sq_sum_le (T := T) (k := k) (M := M) hC hω).2
  have hg_lim : Tendsto (fun k ↦ ∫ ω, g k ω ∂P) atTop (𝓝 0) := by
    have hdom := tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * C * (M + 2 * C)) hg_meas
      (integrable_const _) hg_bound (f := fun _ ↦ (0 : ℝ))
      (hc.mono fun ω hω ↦ by
        simpa only [mul_zero] using (tendsto_gridOsc (T := T) hω).const_mul ((M : ℝ) + 2 * C))
    simpa only [integral_const, smul_zero] using hdom
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _)
    (Eventually.of_forall fun k ↦ ?_) hg_lim
  let Z := stoppedProcess W (gridStop W T k M)
  have hZ : Martingale Z ℱ P := hW.stoppedProcess_of_countable_range
    (isStoppingTime_gridStop hW.stronglyAdapted T k M) (countable_range_gridStop W T k M)
  have hZbdd (t : ℝ≥0) : MemLp (Z t) 2 P :=
    memLp_of_bounded (a := -C) (b := C)
      (hb.mono fun ω hω ↦ stoppedProcess_mem (s := Icc (-C) C) (fun u _ ↦ abs_le.1 (hω u)) t)
      ((hZ.stronglyAdapted t).mono (ℱ.le t)).aestronglyMeasurable 2
  have hZ0 : ∫ ω, Z (dyadicPt T k 0) ω ^ 2 ∂P = 0 := by
    have h0eq : ∀ ω, Z (dyadicPt T k 0) ω = 0 := fun ω ↦ by
      rw [dyadicPt_zero]
      exact (congr_fun (stoppedProcess_bot W (gridStop W T k M)) ω).trans (hW0 ω)
    simp [h0eq]
  have htele := hZ.sum_integral_sq_sub (n := 2 ^ k)
    ((dyadicPt_mono T k).monotoneOn _) (by simpa only [dyadicPt_end] using hZbdd T)
  have hint (i : ℕ) :
      Integrable (fun ω ↦ (Z (dyadicPt T k (i + 1)) ω - Z (dyadicPt T k i) ω) ^ 2) P :=
    ((hZbdd _).sub (hZbdd _)).integrable_sq
  rw [dyadicPt_end, hZ0, sub_zero] at htele
  rw [← htele, ← integral_finsetSum (Finset.range (2 ^ k)) fun i _ ↦ hint i]
  exact integral_mono_ae
    (integrable_finsetSum (Finset.range (2 ^ k)) fun i _ ↦ hint i)
    ((integrable_const (2 * C * (M + 2 * C))).mono' (hg_meas k) (hg_bound k))
    (hb.mono fun ω hω ↦ (stopped_grid_sq_sum_le hC hω).1)

private theorem ae_eq_zero_of_bounded_centered_real_martingale {W : ℝ≥0 → Ω → ℝ}
    (hW : Martingale W ℱ P) (hW0 : ∀ ω, W 0 ω = 0) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂P, ∀ t, |W t ω| ≤ C) (hc : ∀ᵐ ω ∂P, Continuous (W · ω))
    (T : ℝ≥0) (hbv : ∀ᵐ ω ∂P, BoundedVariationOn (W · ω) (Icc 0 T)) :
    W T =ᵐ[P] 0 := by
  have hfatou (M : ℕ) : ∀ᵐ ω ∂P,
      liminf (fun k ↦ ENNReal.ofReal ((stoppedProcess W (gridStop W T k M) T ω) ^ 2)) atTop =
        0 := by
    have hZ (k : ℕ) : Martingale (stoppedProcess W (gridStop W T k M)) ℱ P :=
      hW.stoppedProcess_of_countable_range
        (isStoppingTime_gridStop hW.stronglyAdapted T k M) (countable_range_gridStop W T k M)
    have hmeas (k : ℕ) : AEMeasurable
        (fun ω ↦ ENNReal.ofReal ((stoppedProcess W (gridStop W T k M) T ω) ^ 2)) P :=
      (ENNReal.measurable_ofReal.comp
        ((((hZ k).stronglyAdapted T).mono (ℱ.le T)).pow 2).measurable).aemeasurable
    have hlint (k : ℕ) :
        (∫⁻ ω, ENNReal.ofReal ((stoppedProcess W (gridStop W T k M) T ω) ^ 2) ∂P) =
          ENNReal.ofReal (∫ ω, (stoppedProcess W (gridStop W T k M) T ω) ^ 2 ∂P) := by
      have hZbdd : MemLp (stoppedProcess W (gridStop W T k M) T) 2 P :=
        memLp_of_bounded (a := -C) (b := C)
          (hb.mono fun ω hω ↦ stoppedProcess_mem (s := Icc (-C) C) (fun u _ ↦ abs_le.1 (hω u)) T)
          (((hZ k).stronglyAdapted T).mono (ℱ.le T)).aestronglyMeasurable 2
      exact (ofReal_integral_eq_lintegral_ofReal hZbdd.integrable_sq
        (ae_of_all _ fun _ ↦ sq_nonneg _)).symm
    have hlim0 : liminf (fun k ↦
        ∫⁻ ω, ENNReal.ofReal ((stoppedProcess W (gridStop W T k M) T ω) ^ 2) ∂P) atTop = 0 := by
      simp_rw [hlint]
      exact ((ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_integral_stopped_gridStop_sq hW hW0 hC hb hc T M)).liminf_eq.trans (by simp)
    have hle := (lintegral_liminf_le' hmeas).trans (le_of_eq hlim0)
    exact (lintegral_eq_zero_iff' (AEMeasurable.liminf hmeas)).1 (nonpos_iff_eq_zero.1 hle)
  filter_upwards [hbv, ae_all_iff.2 hfatou] with ω hbvω hfω
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hbvω
  have htop (k : ℕ) : gridStop W T k M ω = ⊤ := by
    apply gridStop_eq_top_of_gridVar_le
    have hsum := eVariationOn.sum_le (f := (W · ω)) (s := Icc 0 T) (n := 2 ^ k)
      (dyadicPt_mono T k) (dyadicPt_mem_Icc T k)
    have hofReal : ENNReal.ofReal (gridVar W T k (2 ^ k) ω) ≤ M := by
      refine (le_trans ?_ hsum).trans hM.le
      rw [gridVar, ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _]
      exact Finset.sum_le_sum fun i _ ↦ by simp [edist_dist, Real.dist_eq]
    simpa using (ENNReal.ofReal_le_iff_le_toReal (ENNReal.natCast_ne_top M)).1 hofReal
  have hconst : (fun k ↦ ENNReal.ofReal ((stoppedProcess W (gridStop W T k M) T ω) ^ 2)) =
      fun _ ↦ ENNReal.ofReal (W T ω ^ 2) := by
    ext k
    rw [stoppedProcess_eq_of_le (htop k ▸ le_top)]
  have hsq0 : ENNReal.ofReal (W T ω ^ 2) = 0 := by
    simpa only [hconst, liminf_const] using hfω M
  exact sq_eq_zero_iff.1 ((ENNReal.ofReal_eq_zero.1 hsq0).antisymm (sq_nonneg _))

private theorem continuous_stoppedProcess_indicator {E : Type*} [NormedAddCommGroup E]
    {M : ℝ≥0 → Ω → E} {ω : Ω} (hc : Continuous (M · ω)) (τ : Ω → WithTop ℝ≥0) :
    Continuous (stoppedProcess (fun t ↦ {ω' | 0 < τ ω'}.indicator (M t)) τ · ω) := by
  have heq : (fun t ↦ stoppedProcess (fun s ↦ {ω' | 0 < τ ω'}.indicator (M s)) τ t ω) =
      if 0 < τ ω then (fun t ↦ stoppedProcess M τ t ω) else fun _ ↦ 0 := by
    ext t
    rw [stoppedProcess_indicator_comm]
    by_cases hpos : 0 < τ ω <;> simp [hpos]
  rw [heq]
  split_ifs
  · exact hc.stoppedProcess
  · exact continuous_const

private theorem boundedVariationOn_stoppedProcess_indicator_sub {M : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {ω : Ω}
    (hbv : BoundedVariationOn (M · ω) (Icc 0 T)) (τ : Ω → WithTop ℝ≥0) :
    let Z := stoppedProcess (fun t ↦ {ω' | 0 < τ ω'}.indicator (M t)) τ
    BoundedVariationOn (fun t ↦ Z t ω - Z 0 ω) (Icc 0 T) := by
  intro Z
  apply (LipschitzWith.id.sub (LipschitzWith.const (Z 0 ω))).comp_boundedVariationOn (g := (Z · ω))
  have heq : (Z · ω) = if 0 < τ ω then (fun t ↦ stoppedProcess M τ t ω) else fun _ ↦ 0 := by
    ext t
    dsimp only [Z]
    rw [stoppedProcess_indicator_comm]
    by_cases hpos : 0 < τ ω <;> simp [hpos]
  rw [heq]
  split_ifs
  · exact hbv.stoppedProcess_Icc
  · simp [BoundedVariationOn, eVariationOn]

private theorem indist_const_real_localMartingale {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ T : ℝ≥0, ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T)) :
    M ≡ᵐ[P] fun _ ↦ M 0 := by
  obtain ⟨ρ, hρ, hmart, hbound⟩ := exists_isLocalizingSequence_bounded_martingale hM hc
  let Z (n : ℕ) := stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (M t)) (ρ n)
  have hZconst (n : ℕ) : (fun t ω ↦ Z n t ω - Z n 0 ω) ≡ᵐ[P] 0 := by
    let W (t : ℝ≥0) (ω : Ω) := Z n t ω - Z n 0 ω
    have hW : Martingale W ℱ P :=
      (hmart n).sub (martingale_const_fun ℱ P ((hmart n).stronglyMeasurable 0)
        ((hmart n).integrable 0))
    have hcW : ∀ᵐ ω ∂P, Continuous (W · ω) :=
      hc.mono fun ω hω ↦ (continuous_stoppedProcess_indicator hω (ρ n)).sub continuous_const
    refine Indistinguishable.of_ae_eq_eval hcW (ae_of_all _ fun _ ↦ continuous_const)
      fun T ↦ ae_eq_zero_of_bounded_centered_real_martingale hW (fun _ ↦ sub_self _)
        (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
        (hbound.mono fun ω hω t ↦ by simpa only [W, Real.norm_eq_abs] using (hω n t).1)
        hcW T ((hbv T).mono fun ω hω ↦ boundedVariationOn_stoppedProcess_indicator_sub hω (ρ n))
  filter_upwards [hρ.tendsto_top, ae_all_iff.2 hZconst] with ω htop hZω t
  obtain ⟨n, hn⟩ := (htop.eventually (eventually_gt_nhds (WithTop.coe_lt_top t))).exists
  have hpos : 0 < ρ n ω := lt_of_le_of_lt (WithTop.coe_le_coe.2 bot_le) hn
  have hZt : Z n t ω = M t ω := by
    dsimp only [Z]
    rw [stoppedProcess_eq_of_le hn.le]
    simp [hpos]
  have hZ0 : Z n 0 ω = M 0 ω := by
    have h0le : ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ ρ n ω := bot_le
    dsimp only [Z]
    rw [stoppedProcess_eq_of_le h0le]
    simp [hpos]
  have hdiff : Z n t ω - Z n 0 ω = 0 := hZω n t
  linarith

end RealEngine

section BanachSpace

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → E}

/-- Under a finite measure, any almost-surely continuous Banach-valued native local martingale on
`ℝ≥0` whose paths have bounded variation on every compact interval `[0, T]` is indistinguishable
from its initial value. Neither completeness nor right continuity of `ℱ`, nor integrability of
`M 0`, is assumed. -/
theorem indist_const_of_boundedVariationOn
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ T : ℝ≥0, ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T)) :
    M ≡ᵐ[P] fun _ ↦ M 0 := by
  obtain ⟨Y, hY, hYM⟩ := hM.exists_stronglyAdapted_ae_eq fun _ h ↦ h.stronglyAdapted
  refine Indistinguishable.of_ae_eq_eval hc (ae_of_all _ fun _ ↦ continuous_const) fun t ↦ ?_
  have hdiff : M t - M 0 =ᵐ[P] 0 := by
    have hsep : TopologicalSpace.IsSeparable (range (Y t - Y 0)) :=
      ((hY t).sub ((hY 0).mono (ℱ.mono bot_le))).isSeparable_range
    refine ae_eq_zero_of_forall_dual_of_isSeparable ℝ hsep (fun L ↦ ?_) ?_
    · have hLM := indist_const_real_localMartingale (L.comp_locally_martingale hM)
        (hc.mono fun ω hω ↦ L.continuous.comp hω)
        (fun T ↦ (hbv T).mono fun ω hω ↦ L.lipschitzWith.comp_boundedVariationOn hω)
      filter_upwards [hLM.ae_eq_eval t] with ω hω
      simpa [map_sub, sub_eq_zero] using hω
    · filter_upwards [hYM] with ω hω
      exact ⟨ω, by simp [hω t, hω 0]⟩
  filter_upwards [hdiff] with ω hω
  exact sub_eq_zero.1 hω

/-- A Banach-valued almost-surely continuous native local martingale with almost-surely locally
bounded variation paths on `Set.univ` is indistinguishable from its initial value. -/
theorem indist_const_of_locallyBoundedVariationOn
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (M · ω) univ) :
    M ≡ᵐ[P] fun _ ↦ M 0 :=
  hM.indist_const_of_boundedVariationOn hc fun T ↦ hbv.mono fun _ h ↦ by
    simpa only [univ_inter] using h 0 T (mem_univ _) (mem_univ _)

/-- A Banach-valued almost-surely continuous native local martingale of locally bounded variation
starting at zero almost surely is indistinguishable from zero. -/
theorem indist_zero_of_locallyBoundedVariationOn
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (M · ω) univ)
    (h0 : M 0 =ᵐ[P] 0) :
    M ≡ᵐ[P] 0 := by
  filter_upwards [hM.indist_const_of_locallyBoundedVariationOn hc hbv, h0] with ω hω h0ω t
  simpa [h0ω] using hω t

end BanachSpace

section RealMonotone

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}

/-- An almost-surely continuous real native local martingale with almost-surely monotone paths is
indistinguishable from its initial value. -/
theorem indist_const_of_ae_monotone
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hmono : ∀ᵐ ω ∂P, Monotone (M · ω)) :
    M ≡ᵐ[P] fun _ ↦ M 0 :=
  hM.indist_const_of_locallyBoundedVariationOn hc
    (hmono.mono fun _ h ↦ (h.monotoneOn univ).locallyBoundedVariationOn)

/-- An almost-surely continuous real native local martingale with almost-surely antitone paths is
indistinguishable from its initial value. -/
theorem indist_const_of_ae_antitone
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hanti : ∀ᵐ ω ∂P, Antitone (M · ω)) :
    M ≡ᵐ[P] fun _ ↦ M 0 := by
  have h := hM.martingale_neg.indist_const_of_ae_monotone
    (hc.mono fun _ h ↦ h.neg) (hanti.mono fun _ h ↦ h.neg)
  filter_upwards [h] with ω hω t
  exact neg_inj.1 (hω t)

end RealMonotone

end ProbabilityTheory.Locally

namespace MeasureTheory.Martingale

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → E}

/-- Under a finite measure, any almost-surely continuous Banach-valued martingale on `ℝ≥0` whose
paths have bounded variation on every compact interval `[0, T]` is indistinguishable from its
initial value. -/
theorem indist_const_of_boundedVariationOn (hM : Martingale M ℱ P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ T : ℝ≥0, ∀ᵐ ω ∂P, BoundedVariationOn (M · ω) (Icc 0 T)) :
    M ≡ᵐ[P] fun _ ↦ M 0 :=
  (Locally.of_prop hM).indist_const_of_boundedVariationOn hc hbv

/-- A Banach-valued almost-surely continuous martingale of locally bounded variation starting at
zero almost surely is indistinguishable from zero. -/
theorem indist_zero_of_locallyBoundedVariationOn (hM : Martingale M ℱ P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hbv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (M · ω) univ)
    (h0 : M 0 =ᵐ[P] 0) :
    M ≡ᵐ[P] 0 :=
  (Locally.of_prop hM).indist_zero_of_locallyBoundedVariationOn hc hbv h0

end MeasureTheory.Martingale
