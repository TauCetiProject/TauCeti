/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Gap
public import TauCeti.Probability.PointProcess.Poisson.OccurrenceTime
public import TauCeti.Probability.PointProcess.Poisson.Count
public import TauCeti.Probability.Distributions.Exponential.Basic
public import Mathlib.Probability.Independence.InfinitePi

import Mathlib.MeasureTheory.Function.Floor
import TauCeti.MeasureTheory.Measure.StrictMono
import TauCeti.MeasureTheory.Constructions.Pi
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

At rate zero, the random measure vanishes almost surely, so every occurrence time and every
extended interarrival gap is almost surely infinite. Because almost surely constant coordinates
are independent, mutual independence of the interarrival gaps holds for every rate `r : ℝ≥0`,
without a positivity side condition.

Rather than changing variables via Lebesgue Jacobians on open simplices, the proof compares
the finite-prefix occurrence-time law and the exponential cumulative-sum law directly on the
strictly increasing positive chamber using `MeasureTheory.Measure.ext_of_Ioc_strictMono`. On
any separated half-open box `∏ᵢ (aᵢ, bᵢ]`, cumulative-count squeezing rewrites membership of
the occurrence times into independent Poisson counts on `2m` disjoint intervals, whose
product matches the iterated exponential integral of the shifted box.

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

private def partialSum (m : ℕ) (x : Fin m → ℝ≥0) (i : Fin m) : ℝ≥0 :=
  ∑ j : Fin m, if j ≤ i then x j else 0

private lemma partialSum_eq_sum_Iic (m : ℕ) (x : Fin m → ℝ≥0) (i : Fin m) :
    partialSum m x i = ∑ j ∈ Finset.Iic i, x j := by
  rw [partialSum, ← Finset.sum_filter]
  congr 1
  ext j
  simp

@[fun_prop]
private lemma measurable_partialSum (m : ℕ) : Measurable (partialSum m) := by
  refine measurable_pi_iff.mpr fun i => Finset.measurable_fun_sum _ fun j _ => ?_
  by_cases hji : j ≤ i <;> simp [hji, measurable_pi_apply]

private lemma partialSum_cons_zero {k : ℕ} (x₀ : ℝ≥0) (y : Fin k → ℝ≥0) :
    partialSum (k + 1) (Fin.cons x₀ y) 0 = x₀ := by
  rw [partialSum, Fin.sum_univ_succ]
  simp [not_le_of_gt (Fin.succ_pos _)]

private lemma partialSum_cons_succ {k : ℕ} (x₀ : ℝ≥0) (y : Fin k → ℝ≥0) (i : Fin k) :
    partialSum (k + 1) (Fin.cons x₀ y) i.succ = x₀ + partialSum k y i := by
  rw [partialSum, Fin.sum_univ_succ]
  simp [partialSum]

private def gapOfPartialSum (m : ℕ) (s : Fin m → ℝ≥0) (i : Fin m) : ℝ≥0 :=
  if h : 0 < (i : ℕ) then s i - s ⟨(i : ℕ) - 1, by omega⟩ else s i

@[fun_prop]
private lemma measurable_gapOfPartialSum (m : ℕ) : Measurable (gapOfPartialSum m) := by
  refine measurable_pi_iff.mpr fun i => ?_
  dsimp only [gapOfPartialSum]
  split_ifs with h
  · exact (measurable_pi_apply i).sub (measurable_pi_apply _)
  · exact measurable_pi_apply i

private lemma gapOfPartialSum_comp_partialSum (m : ℕ) :
    gapOfPartialSum m ∘ partialSum m = id := by
  funext x i
  simp only [Function.comp_apply, id_eq, gapOfPartialSum, partialSum_eq_sum_Iic]
  split_ifs with h
  · let i' : Fin m := ⟨(i : ℕ) - 1, by omega⟩
    have hIic : Finset.Iic i = insert i (Finset.Iic i') := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff, i']
      omega
    have hnotMem : i ∉ Finset.Iic i' := by
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, i']
      omega
    rw [hIic, Finset.sum_insert hnotMem, add_tsub_cancel_right]
  · have hIic : Finset.Iic i = {i} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    rw [hIic, Finset.sum_singleton]

private lemma ae_pos_nnrealExpMeasure {r : ℝ} : ∀ᵐ x ∂nnrealExpMeasure r, 0 < x := by
  rw [nnrealExpMeasure_def, ae_map_iff (by fun_prop) measurableSet_Ioi]
  filter_upwards [ae_pos_expMeasure r] with x hx
  exact Real.toNNReal_pos.mpr hx

private lemma map_coe_nnrealExpMeasure {r : ℝ} :
    (nnrealExpMeasure r).map ((↑) : ℝ≥0 → ℝ) = expMeasure r := by
  rw [nnrealExpMeasure_def, Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    (expMeasure r).map (((↑) : ℝ≥0 → ℝ) ∘ Real.toNNReal) = (expMeasure r).map id := by
      apply Measure.map_congr
      filter_upwards [ae_pos_expMeasure r] with x hx
      exact Real.coe_toNNReal x hx.le
    _ = expMeasure r := Measure.map_id

private lemma toNNReal_preimage_Ioc (u v : ℝ≥0) :
    Real.toNNReal ⁻¹' Ioc u v = Ioc (u : ℝ) (v : ℝ) := by
  ext x
  simp only [mem_preimage, mem_Ioc]
  exact ⟨fun ⟨hu, hv⟩ => ⟨Real.lt_toNNReal_iff_coe_lt.mp hu, Real.toNNReal_le_iff_le_coe.mp hv⟩,
    fun ⟨hu, hv⟩ => ⟨Real.lt_toNNReal_iff_coe_lt.mpr hu, Real.toNNReal_le_iff_le_coe.mpr hv⟩⟩

private lemma add_mem_Ioc_iff_sub {x₀ u v z : ℝ≥0} (hx : x₀ ≤ u) (huv : u ≤ v) :
    x₀ + z ∈ Ioc u v ↔ z ∈ Ioc (u - x₀) (v - x₀) := by
  have hxv : x₀ ≤ v := hx.trans huv
  simp only [mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe, NNReal.coe_add,
    NNReal.coe_sub hx, NNReal.coe_sub hxv]
  constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith

private lemma isSeparatedBox_shift {k : ℕ} {a b : Fin (k + 2) → ℝ≥0}
    (hsep : IsSeparatedBox a b) {x₀ : ℝ≥0} :
    IsSeparatedBox (fun i : Fin (k + 1) => a i.succ - x₀)
      (fun i : Fin (k + 1) => b i.succ - x₀) :=
  IsSeparatedBox.mk (fun i => tsub_le_tsub_right (hsep.le i.succ) x₀) fun _ _ hij =>
    tsub_le_tsub_right (hsep.le_of_lt (Fin.succ_lt_succ_iff.mpr hij)) x₀

private noncomputable def boxFormula {k : ℕ} (r : ℝ) (a b : Fin (k + 1) → ℝ≥0) : ℝ :=
  (∏ j : Fin k, r * ((b j.castSucc : ℝ) - a j.castSucc)) *
    (Real.exp (-(r * a (Fin.last k))) - Real.exp (-(r * b (Fin.last k))))

private lemma boxFormula_nonneg {k : ℕ} {r : ℝ} (hr : 0 ≤ r) {a b : Fin (k + 1) → ℝ≥0}
    (hsep : IsSeparatedBox a b) : 0 ≤ boxFormula r a b := by
  refine mul_nonneg (Finset.prod_nonneg fun j _ => ?_) (sub_nonneg.mpr ?_)
  · exact mul_nonneg hr (sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hsep.le j.castSucc)))
  · apply Real.exp_le_exp.mpr
    have hab : (a (Fin.last k) : ℝ) ≤ b (Fin.last k) := NNReal.coe_le_coe.mpr (hsep.le _)
    nlinarith

private lemma setLIntegral_exp_mul_nnrealExpMeasure {r : ℝ} (hr : 0 < r) (u v : ℝ≥0) :
    ∫⁻ x in Ioc u v, ENNReal.ofReal (Real.exp (r * (x : ℝ))) ∂nnrealExpMeasure r =
      ENNReal.ofReal (r * ((v : ℝ) - u)) := by
  have hm : Measurable fun x : ℝ≥0 => ENNReal.ofReal (Real.exp (r * (x : ℝ))) := by fun_prop
  have hm_real : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (r * x)) := by fun_prop
  have hm_pdf : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  rw [nnrealExpMeasure_def, ← lintegral_indicator measurableSet_Ioc,
    lintegral_map (hm.indicator measurableSet_Ioc) (by fun_prop)]
  have hind : (fun x : ℝ => ((Ioc u v).indicator
      (fun y : ℝ≥0 => ENNReal.ofReal (Real.exp (r * (y : ℝ)))) (Real.toNNReal x))) =
      (Ioc (u : ℝ) (v : ℝ)).indicator (fun x : ℝ => ENNReal.ofReal (Real.exp (r * x))) := by
    funext x
    by_cases hx : Real.toNNReal x ∈ Ioc u v
    · have hx' : x ∈ Ioc (u : ℝ) (v : ℝ) := by rwa [← toNNReal_preimage_Ioc]
      have hxnonneg : 0 ≤ x := u.2.trans hx'.1.le
      simp [hx, hx', Real.coe_toNNReal x hxnonneg]
    · have hx' : x ∉ Ioc (u : ℝ) (v : ℝ) := by rwa [← toNNReal_preimage_Ioc]
      simp [hx, hx']
  rw [hind, expMeasure_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul₀ hm_pdf.aemeasurable
      (hm_real.indicator measurableSet_Ioc).aemeasurable]
  have hmul_ind (x : ℝ) :
      (exponentialPDF r *
        (Ioc (u : ℝ) (v : ℝ)).indicator (fun y => ENNReal.ofReal (Real.exp (r * y)))) x =
      (Ioc (u : ℝ) (v : ℝ)).indicator (fun _ => ENNReal.ofReal r) x := by
    rw [Pi.mul_apply]
    by_cases hx : x ∈ Ioc (u : ℝ) (v : ℝ)
    · have hxnonneg : 0 ≤ x := u.2.trans hx.1.le
      rw [indicator_of_mem hx, indicator_of_mem hx, exponentialPDF_eq, ite_eq_left hxnonneg,
        ← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.exp_nonneg _))]
      congr 1
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    · simp [hx]
  rw [lintegral_congr hmul_ind, lintegral_indicator measurableSet_Ioc, setLIntegral_const,
    Real.volume_Ioc, ← ENNReal.ofReal_mul hr.le]

private lemma map_partialSum_pi_apply_separatedBox (k : ℕ) {r : ℝ} (hr : 0 < r)
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    ((Measure.pi fun _ : Fin (k + 1) => nnrealExpMeasure r).map (partialSum (k + 1)))
        (univ.pi fun i => Ioc (a i) (b i)) =
      ENNReal.ofReal (boxFormula r a b) := by
  induction k with
  | zero =>
    have _ : IsProbabilityMeasure (nnrealExpMeasure r) := isProbabilityMeasure_nnrealExpMeasure hr
    have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
    rw [Measure.map_apply (measurable_partialSum 1)
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
    have hpre : partialSum 1 ⁻¹' (univ.pi fun i => Ioc (a i) (b i)) =
        (fun x : Fin 1 → ℝ≥0 => x 0) ⁻¹' Ioc (a 0) (b 0) := by
      ext x
      simp only [mem_preimage, mem_univ_pi, Fin.forall_fin_one, partialSum, Fin.sum_univ_one,
        le_rfl, ↓reduceIte]
    rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioc,
      (measurePreserving_eval (fun _ : Fin 1 => nnrealExpMeasure r) 0).map_eq,
      nnrealExpMeasure_def, Measure.map_apply (by fun_prop) measurableSet_Ioc,
      toNNReal_preimage_Ioc]
    have hunion : Ioc (a 0 : ℝ) (b 0 : ℝ) ∪ Ioi (b 0 : ℝ) = Ioi (a 0 : ℝ) :=
      Ioc_union_Ioi_eq_Ioi (NNReal.coe_le_coe.mpr (hsep.le 0))
    have hdisj : Disjoint (Ioc (a 0 : ℝ) (b 0 : ℝ)) (Ioi (b 0 : ℝ)) := Ioc_disjoint_Ioi le_rfl
    rw [← ENNReal.ofReal_toReal (measure_ne_top (expMeasure r) _)]
    congr 1
    have hreal : (expMeasure r).real (Ioi (a 0 : ℝ)) =
        (expMeasure r).real (Ioc (a 0 : ℝ) (b 0 : ℝ)) + (expMeasure r).real (Ioi (b 0 : ℝ)) := by
      rw [← hunion, measureReal_union hdisj measurableSet_Ioi]
    have ha0 : (0 : ℝ) ≤ a 0 := (a 0).2
    have hb0 : (0 : ℝ) ≤ b 0 := (b 0).2
    rw [measureReal_Ioi_expMeasure hr, measureReal_Ioi_expMeasure hr,
      ite_eq_left ha0, ite_eq_left hb0] at hreal
    simp only [boxFormula, Finset.univ_eq_empty, Finset.prod_empty, one_mul, Fin.last_zero,
      ← measureReal_def]
    linarith
  | succ k ih =>
    have _ : IsProbabilityMeasure (nnrealExpMeasure r) := isProbabilityMeasure_nnrealExpMeasure hr
    let ν_tail := Measure.pi fun _ : Fin (k + 1) => nnrealExpMeasure r
    let B := univ.pi fun i : Fin (k + 2) => Ioc (a i) (b i)
    have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
    rw [Measure.map_apply (measurable_partialSum (k + 2)) hB]
    have hcons : MeasurePreserving
        (fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2)
        ((nnrealExpMeasure r).prod ν_tail)
        (Measure.pi fun _ : Fin (k + 2) => nnrealExpMeasure r) := by
      have hcons_eq : (fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2) =
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) => ℝ≥0) 0).symm := by
        funext p
        exact (MeasurableEquiv.piFinSuccAbove_zero_symm_apply_eq_cons p.1 p.2).symm
      rw [hcons_eq]
      exact (measurePreserving_piFinSuccAbove
        (fun _ : Fin (k + 2) => nnrealExpMeasure r) 0).symm _
    rw [← hcons.measure_preimage ((measurable_partialSum (k + 2)) hB).nullMeasurableSet,
      Measure.prod_apply (hcons.measurable ((measurable_partialSum (k + 2)) hB))]
    let C_tail : ℝ :=
      (∏ j : Fin k, r * ((b j.castSucc.succ : ℝ) - a j.castSucc.succ)) *
        (Real.exp (-(r * a (Fin.last (k + 1)))) - Real.exp (-(r * b (Fin.last (k + 1)))))
    have hC_nonneg : 0 ≤ C_tail := by
      have hsep' : IsSeparatedBox (fun i : Fin (k + 1) => a i.succ)
          (fun i : Fin (k + 1) => b i.succ) :=
        IsSeparatedBox.mk (fun i => hsep.le i.succ)
          (fun _ _ hij => hsep.le_of_lt (Fin.succ_lt_succ_iff.mpr hij))
      exact boxFormula_nonneg hr.le hsep'
    have hslice (x₀ : ℝ≥0) :
        ν_tail (Prod.mk x₀ ⁻¹' ((fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2) ⁻¹'
          (partialSum (k + 2) ⁻¹' B))) =
          (Ioc (a 0) (b 0)).indicator
            (fun x => ENNReal.ofReal C_tail * ENNReal.ofReal (Real.exp (r * (x : ℝ)))) x₀ := by
      by_cases hx₀ : x₀ ∈ Ioc (a 0) (b 0)
      · have hset : Prod.mk x₀ ⁻¹' ((fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2) ⁻¹'
            (partialSum (k + 2) ⁻¹' B)) =
            partialSum (k + 1) ⁻¹'
              (univ.pi fun i : Fin (k + 1) => Ioc (a i.succ - x₀) (b i.succ - x₀)) := by
          ext y
          simp only [B, mem_preimage, mem_univ_pi]
          rw [Fin.forall_fin_succ (n := k + 1)]
          simp only [partialSum_cons_zero, partialSum_cons_succ, hx₀, true_and]
          exact forall_congr' fun i =>
            add_mem_Ioc_iff_sub (hx₀.2.trans (hsep.le_of_lt (Fin.succ_pos i))) (hsep.le i.succ)
        rw [hset, indicator_of_mem hx₀,
          ← Measure.map_apply (measurable_partialSum (k + 1))
            (MeasurableSet.univ_pi fun _ => measurableSet_Ioc),
          ih (isSeparatedBox_shift hsep),
          ← ENNReal.ofReal_mul hC_nonneg]
        congr 1
        have ha_ge (i : Fin (k + 1)) : x₀ ≤ a i.succ :=
          hx₀.2.trans (hsep.le_of_lt (Fin.succ_pos i))
        have hb_ge (i : Fin (k + 1)) : x₀ ≤ b i.succ := (ha_ge i).trans (hsep.le i.succ)
        have hprod : (∏ j : Fin k, r *
            (((b j.castSucc.succ - x₀ : ℝ≥0) : ℝ) - (a j.castSucc.succ - x₀ : ℝ≥0))) =
            ∏ j : Fin k, r * ((b j.castSucc.succ : ℝ) - a j.castSucc.succ) := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [NNReal.coe_sub (hb_ge _), NNReal.coe_sub (ha_ge _)]
          ring
        have hexp_a : Real.exp (-(r * ((a (Fin.last k).succ - x₀ : ℝ≥0) : ℝ))) =
            Real.exp (-(r * a (Fin.last (k + 1)))) * Real.exp (r * x₀) := by
          rw [NNReal.coe_sub (ha_ge (Fin.last k)), Fin.succ_last, ← Real.exp_add]
          congr 1
          ring
        have hexp_b : Real.exp (-(r * ((b (Fin.last k).succ - x₀ : ℝ≥0) : ℝ))) =
            Real.exp (-(r * b (Fin.last (k + 1)))) * Real.exp (r * x₀) := by
          rw [NNReal.coe_sub (hb_ge (Fin.last k)), Fin.succ_last, ← Real.exp_add]
          congr 1
          ring
        simp only [boxFormula, hprod, hexp_a, hexp_b, C_tail]
        ring
      · have hempty : Prod.mk x₀ ⁻¹' ((fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2) ⁻¹'
            (partialSum (k + 2) ⁻¹' B)) = ∅ := by
          ext y
          simp only [B, mem_preimage, mem_univ_pi, mem_empty_iff_false, iff_false]
          intro hy
          exact hx₀ (by simpa [partialSum_cons_zero] using hy 0)
        rw [hempty, measure_empty, indicator_of_notMem hx₀]
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Ioc,
      lintegral_const_mul _ (by fun_prop),
      setLIntegral_exp_mul_nnrealExpMeasure hr (a 0) (b 0),
      ← ENNReal.ofReal_mul hC_nonneg]
    congr 1
    simp only [boxFormula, C_tail, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.succ_castSucc]
    ring

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

private lemma pairwise_disjoint_separatedIntervals {k : ℕ} {a b : Fin (k + 1) → ℝ≥0}
    (hsep : IsSeparatedBox a b) :
    Pairwise (Disjoint on (Sum.elim (fun i : Fin (k + 1) => Ioc (prevEndpoint b i) (a i))
      (fun i : Fin (k + 1) => Ioc (a i) (b i)))) := by
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

private lemma measure_Ioc_zero_eq_Iic {μ : Measure ℝ≥0} (h0 : μ {0} = 0) (t : ℝ≥0) :
    μ (Ioc 0 t) = μ (Iic t) := by
  have heq : Ioc 0 t = Iic t \ {0} := by
    ext x
    simp [pos_iff_ne_zero, and_comm]
  rw [heq, measure_sdiff_null h0]

private lemma measure_Ioc_zero_add {μ : Measure ℝ≥0} {s t : ℝ≥0} (hst : s ≤ t) :
    μ (Ioc 0 s) + μ (Ioc s t) = μ (Ioc 0 t) := by
  rw [← measure_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
    Ioc_union_Ioc_eq_Ioc zero_le hst]

private lemma forall_toNNReal_occurrenceTime_mem_Ioc_iff {k : ℕ} {μ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure μ] (hμ : μ.IsIntegerValued) (h0 : μ {0} = 0)
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    (∀ i : Fin (k + 1), (μ.occurrenceTime i).toNNReal ∈ Ioc (a i) (b i)) ↔
      (∀ i : Fin (k + 1), μ (Ioc (prevEndpoint b i) (a i)) = 0) ∧
      (∀ j : Fin k, μ (Ioc (a j.castSucc) (b j.castSucc)) = 1) ∧
      1 ≤ μ (Ioc (a (Fin.last k)) (b (Fin.last k))) := by
  have hfin_Ioc (t : ℝ≥0) : μ (Ioc 0 t) ≠ ∞ :=
    ((measure_mono Ioc_subset_Iic_self).trans_lt measure_Iic_lt_top).ne
  constructor
  · intro hmem
    have hne (i : Fin (k + 1)) : μ.occurrenceTime i ≠ ∞ := by
      intro htop
      have := (hmem i).1
      simp [htop] at this
    have hlow (i : Fin (k + 1)) : ((i : ℕ) + 1 : ℝ≥0∞) ≤ μ (Ioc 0 (b i)) := by
      rw [measure_Ioc_zero_eq_Iic h0, ← μ.occurrenceTime_le_iff]
      rw [← ENNReal.coe_toNNReal (hne i), ENNReal.coe_le_coe]
      exact (hmem i).2
    have hhigh (i : Fin (k + 1)) : μ (Ioc 0 (a i)) ≤ (i : ℕ) := by
      have hlt : μ (Ioc 0 (a i)) < (i : ℕ) + 1 := by
        rw [measure_Ioc_zero_eq_Iic h0, ← not_le, ← μ.occurrenceTime_le_iff, not_le,
          ← ENNReal.coe_toNNReal (hne i), ENNReal.coe_lt_coe]
        exact (hmem i).1
      obtain ⟨m, hm⟩ := hμ.exists_eq_natCast measurableSet_Ioc (hfin_Ioc (a i)).lt_top
      rw [hm] at hlt ⊢
      norm_cast at hlt ⊢
      omega
    have hbj (j : Fin k) : μ (Ioc 0 (b j.castSucc)) = (j : ℕ) + 1 ∧
        μ (Ioc 0 (a j.succ)) = (j : ℕ) + 1 := by
      have hmono : μ (Ioc 0 (b j.castSucc)) ≤ μ (Ioc 0 (a j.succ)) :=
        measure_mono (Ioc_subset_Ioc_right (hsep.le_of_lt j.castSucc_lt_succ))
      have h1 := hlow j.castSucc
      have h2 := hhigh j.succ
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] at h1 h2
      exact ⟨le_antisymm (hmono.trans h2) h1, le_antisymm h2 (h1.trans hmono)⟩
    have hai (i : Fin (k + 1)) : μ (Ioc 0 (a i)) = (i : ℕ) := by
      cases i using Fin.cases with
      | zero => simpa using hhigh 0
      | succ j => simpa using (hbj j).2
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · cases i using Fin.cases with
      | zero => simpa [prevEndpoint] using hai 0
      | succ j =>
        have hadd := measure_Ioc_zero_add (μ := μ) (hsep.le_of_lt j.castSucc_lt_succ)
        rw [(hbj j).1, (hbj j).2] at hadd
        simpa [prevEndpoint] using
          (ENNReal.add_right_inj (by finiteness)).mp (hadd.trans (add_zero _).symm)
    · have hadd := measure_Ioc_zero_add (μ := μ) (hsep.le j.castSucc)
      rw [hai j.castSucc, (hbj j).1] at hadd
      exact (ENNReal.add_right_inj (ENNReal.natCast_ne_top j)).mp hadd
    · have hadd := measure_Ioc_zero_add (μ := μ) (hsep.le (Fin.last k))
      have hlast := hlow (Fin.last k)
      rw [← hadd, hai (Fin.last k), Fin.val_last] at hlast
      exact (ENNReal.add_le_add_iff_left (ENNReal.natCast_ne_top k)).mp hlast
  · rintro ⟨hG, hJ, hlast⟩
    have hai (i : Fin (k + 1)) : μ (Ioc 0 (a i)) = (i : ℕ) := by
      induction i using Fin.induction with
      | zero => simpa [prevEndpoint] using hG 0
      | succ j ih =>
        have hb : μ (Ioc 0 (b j.castSucc)) = (j : ℕ) + 1 := by
          rw [← measure_Ioc_zero_add (hsep.le j.castSucc), ih, hJ j, Fin.val_castSucc]
        rw [← measure_Ioc_zero_add (hsep.le_of_lt j.castSucc_lt_succ), hb]
        simpa [prevEndpoint] using hG j.succ
    have hbi (i : Fin (k + 1)) : ((i : ℕ) + 1 : ℝ≥0∞) ≤ μ (Ioc 0 (b i)) := by
      cases i using Fin.lastCases with
      | last =>
        rw [← measure_Ioc_zero_add (hsep.le (Fin.last k)), hai (Fin.last k), Fin.val_last]
        gcongr
      | cast j =>
        rw [← measure_Ioc_zero_add (hsep.le j.castSucc), hai j.castSucc, hJ j]
    intro i
    have hle_b : μ.occurrenceTime i ≤ b i := by
      rw [μ.occurrenceTime_le_iff, ← measure_Ioc_zero_eq_Iic h0]
      exact hbi i
    have hne : μ.occurrenceTime i ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle_b
    have hnot_le_a : ¬ μ.occurrenceTime i ≤ a i := by
      rw [μ.occurrenceTime_le_iff, ← measure_Ioc_zero_eq_Iic h0, hai i, not_le]
      norm_cast
      omega
    refine ⟨?_, ?_⟩
    · rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hne]
      exact not_le.mp hnot_le_a
    · rwa [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]

private lemma telescoping_separated_endpoints (k : ℕ) (a b : Fin (k + 1) → ℝ≥0) :
    (∑ i : Fin (k + 1), ((a i : ℝ) - prevEndpoint b i)) +
        (∑ j : Fin k, ((b j.castSucc : ℝ) - a j.castSucc)) =
      (a (Fin.last k) : ℝ) := by
  induction k with
  | zero => simp [prevEndpoint]
  | succ k ih =>
    let a' : Fin (k + 1) → ℝ≥0 := fun i => a i.castSucc
    let b' : Fin (k + 1) → ℝ≥0 := fun i => b i.castSucc
    have hprev (i : Fin (k + 1)) : prevEndpoint b i.castSucc = prevEndpoint b' i := by
      cases i using Fin.cases <;> rfl
    have hlast_prev : prevEndpoint b (Fin.last (k + 1)) = b (Fin.last k).castSucc := by
      rw [← Fin.succ_last k]
      rfl
    have h1 := Fin.sum_univ_castSucc (n := k + 1) (f := fun i => (a i : ℝ) - prevEndpoint b i)
    have h2 := Fin.sum_univ_castSucc (n := k) (f := fun j => (b j.castSucc : ℝ) - a j.castSucc)
    have ih' := ih a' b'
    rw [h1, h2, hlast_prev]
    simp_rw [hprev]
    dsimp only [a', b'] at ih'
    linarith

private lemma poisson_occurrenceTime_apply_separatedBox {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) {k : ℕ}
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    (P.map fun ω (i : Fin (k + 1)) => ((N ω).occurrenceTime i).toNNReal)
        (univ.pi fun i => Ioc (a i) (b i)) =
      ENNReal.ofReal (boxFormula (r : ℝ) a b) := by
  let := h.isProbabilityMeasure
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  let A : Fin (k + 1) ⊕ Fin (k + 1) → Set ℝ≥0 :=
    Sum.elim (fun i => Ioc (prevEndpoint b i) (a i)) (fun i => Ioc (a i) (b i))
  have hm_floor : Measurable fun x : ℝ≥0∞ => ⌊x.toNNReal⌋₊ := by fun_prop
  have hind_raw := h.iIndepFun_eval (A := A) (fun u => by cases u <;> exact measurableSet_Ioc)
    (pairwise_disjoint_separatedIntervals hsep)
  have hind_comp := hind_raw.comp (fun _ => fun x : ℝ≥0∞ => ⌊x.toNNReal⌋₊) (fun _ => hm_floor)
  let X (u : Fin (k + 1) ⊕ Fin (k + 1)) (ω : Ω) : ℕ := ⌊(N ω (A u)).toNNReal⌋₊
  have hindX : ProbabilityTheory.iIndepFun X P :=
    hind_comp.congr fun _ => Filter.Eventually.of_forall fun _ => rfl
  let S : Fin (k + 1) ⊕ Fin (k + 1) → Set ℕ :=
    Sum.elim (fun _ => {0}) (fun i => if i = Fin.last k then Ici 1 else {1})
  have hae_zero : ∀ᵐ ω ∂P, N ω {0} = 0 := by
    have hlaw0 : HasLaw (fun ω => N ω {0}) (Measure.dirac 0) P := by
      simpa [poissonMeasure_zero] using h.hasLaw (measurableSet_singleton 0) (by simp)
    exact hlaw0.ae_eq_of_dirac
  have hmeas_time : Measurable fun ω (i : Fin (k + 1)) => ((N ω).occurrenceTime i).toNNReal :=
    measurable_pi_iff.mpr fun i =>
      ((Measure.measurable_occurrenceTime i).comp h.measurable).ennreal_toNNReal
  rw [Measure.map_apply hmeas_time (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
  have hevent : ((fun ω (i : Fin (k + 1)) => ((N ω).occurrenceTime i).toNNReal) ⁻¹'
      (univ.pi fun i => Ioc (a i) (b i))) =ᵐ[P]
      (⋂ u ∈ (Finset.univ : Finset (Fin (k + 1) ⊕ Fin (k + 1))), X u ⁻¹' S u) := by
    filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued, hae_zero] with ω hlf hint h0
    simp only [mem_preimage, mem_univ_pi, mem_iInter, Finset.mem_univ, forall_true_left,
      forall_toNNReal_occurrenceTime_mem_Ioc_iff hint h0 hsep, Sum.forall, A, S, X]
    have hnat (s t : ℝ≥0) : ∃ m : ℕ, N ω (Ioc s t) = m :=
      hint.exists_eq_natCast measurableSet_Ioc
        ((measure_mono Ioc_subset_Iic_self).trans_lt measure_Iic_lt_top)
    have hfloor_eq_zero (s t : ℝ≥0) :
        N ω (Ioc s t) = 0 ↔ ⌊(N ω (Ioc s t)).toNNReal⌋₊ = 0 := by
      obtain ⟨m, hm⟩ := hnat s t
      rw [hm]
      simp
    have hfloor_eq_one (s t : ℝ≥0) :
        N ω (Ioc s t) = 1 ↔ ⌊(N ω (Ioc s t)).toNNReal⌋₊ = 1 := by
      obtain ⟨m, hm⟩ := hnat s t
      rw [hm]
      simp
    have hfloor_ge_one (s t : ℝ≥0) :
        1 ≤ N ω (Ioc s t) ↔ 1 ≤ ⌊(N ω (Ioc s t)).toNNReal⌋₊ := by
      obtain ⟨m, hm⟩ := hnat s t
      rw [hm]
      simp
    constructor
    · rintro ⟨hG, hJ, hlast⟩
      refine ⟨fun i => (hfloor_eq_zero _ _).mp (hG i), fun i => ?_⟩
      cases i using Fin.lastCases with
      | last => simpa using (hfloor_ge_one _ _).mp hlast
      | cast j => simpa [Fin.castSucc_ne_last] using (hfloor_eq_one _ _).mp (hJ j)
    · rintro ⟨hG, hJ⟩
      refine ⟨fun i => (hfloor_eq_zero _ _).mpr (hG i), fun j => ?_, ?_⟩
      · exact (hfloor_eq_one _ _).mpr (by simpa [Fin.castSucc_ne_last] using hJ j.castSucc)
      · exact (hfloor_ge_one _ _).mpr (by simpa using hJ (Fin.last k))
  rw [measure_congr hevent, ← ENNReal.ofReal_toReal (measure_ne_top P _)]
  congr 1
  have hprod_meas := (iIndepFun_iff_measure_inter_preimage_eq_mul.mp hindX) Finset.univ
    (sets := S) (fun _ _ => MeasurableSet.of_discrete)
  rw [hprod_meas, ENNReal.toReal_prod, Fintype.prod_sum_type]
  have htoReal_pre {Z : Ω → ℕ} {μ : Measure ℕ} (hlaw : HasLaw Z μ P) (s : Set ℕ) :
      (P (Z ⁻¹' s)).toReal = μ.real s := by
    rw [measureReal_def, ← hlaw.map_eq,
      Measure.map_apply_of_aemeasurable hlaw.aemeasurable MeasurableSet.of_discrete]
  have hG_val (i : Fin (k + 1)) :
      (P (X (Sum.inl i) ⁻¹' S (Sum.inl i))).toReal =
        Real.exp (-((r : ℝ) * ((a i : ℝ) - prevEndpoint b i))) := by
    have hlaw := h.hasLaw_nat_count_Ioc_smul_nnvolume (prevEndpoint b i) (a i)
    dsimp only [X, A, S, Sum.elim_inl]
    rw [htoReal_pre hlaw {0}, poissonMeasure_real_singleton_zero, NNReal.coe_mul,
      NNReal.coe_sub (prevEndpoint_le_of_separated hsep i)]
  have hJ_cast (j : Fin k) :
      (P (X (Sum.inr j.castSucc) ⁻¹' S (Sum.inr j.castSucc))).toReal =
        Real.exp (-((r : ℝ) * ((b j.castSucc : ℝ) - a j.castSucc))) *
          ((r : ℝ) * ((b j.castSucc : ℝ) - a j.castSucc)) := by
    have hlaw := h.hasLaw_nat_count_Ioc_smul_nnvolume (a j.castSucc) (b j.castSucc)
    dsimp only [X, A, S, Sum.elim_inr]
    rw [ite_eq_right (Fin.castSucc_ne_last j), htoReal_pre hlaw {1}, poissonMeasure_real_singleton]
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, NNReal.coe_mul,
      NNReal.coe_sub (hsep.le j.castSucc)]
  have hJ_last :
      (P (X (Sum.inr (Fin.last k)) ⁻¹' S (Sum.inr (Fin.last k)))).toReal =
        1 - Real.exp (-((r : ℝ) * ((b (Fin.last k) : ℝ) - a (Fin.last k)))) := by
    have hlaw := h.hasLaw_nat_count_Ioc_smul_nnvolume (a (Fin.last k)) (b (Fin.last k))
    have hcompl : (Ici 1 : Set ℕ) = ({0} : Set ℕ)ᶜ := by
      ext m
      simp [Nat.one_le_iff_ne_zero]
    dsimp only [X, A, S, Sum.elim_inr]
    rw [ite_eq_left rfl, htoReal_pre hlaw (Ici 1), hcompl,
      measureReal_compl MeasurableSet.of_discrete, probReal_univ,
      poissonMeasure_real_singleton_zero, NNReal.coe_mul,
      NNReal.coe_sub (hsep.le (Fin.last k))]
  simp_rw [hG_val]
  rw [Fin.prod_univ_castSucc (f := fun i => (P (X (Sum.inr i) ⁻¹' S (Sum.inr i))).toReal),
    hJ_last]
  simp_rw [hJ_cast]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.exp_sum]
  have hexp_sum :
      (∑ x : Fin (k + 1), -((r : ℝ) * ((a x : ℝ) - prevEndpoint b x))) +
        (∑ x : Fin k, -((r : ℝ) * ((b x.castSucc : ℝ) - a x.castSucc))) =
      -((r : ℝ) * a (Fin.last k)) := by
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hmul := congrArg ((r : ℝ) * ·) (telescoping_separated_endpoints k a b)
    linarith
  have hprod_exp :
      Real.exp (∑ x : Fin (k + 1), -((r : ℝ) * ((a x : ℝ) - prevEndpoint b x))) *
        Real.exp (∑ x : Fin k, -((r : ℝ) * ((b x.castSucc : ℝ) - a x.castSucc))) =
      Real.exp (-((r : ℝ) * a (Fin.last k))) := by
    rw [← Real.exp_add, hexp_sum]
  have hexp_b :
      -((r : ℝ) * a (Fin.last k)) + -((r : ℝ) * ((b (Fin.last k) : ℝ) - a (Fin.last k))) =
      -((r : ℝ) * b (Fin.last k)) := by ring
  calc
    Real.exp (∑ x : Fin (k + 1), -((r : ℝ) * ((a x : ℝ) - prevEndpoint b x))) *
        ((Real.exp (∑ x : Fin k, -((r : ℝ) * ((b x.castSucc : ℝ) - a x.castSucc))) *
            ∏ x : Fin k, (r : ℝ) * ((b x.castSucc : ℝ) - a x.castSucc)) *
          (1 - Real.exp (-((r : ℝ) * ((b (Fin.last k) : ℝ) - a (Fin.last k))))))
      = (∏ x : Fin k, (r : ℝ) * ((b x.castSucc : ℝ) - a x.castSucc)) *
          ((Real.exp (∑ x : Fin (k + 1), -((r : ℝ) * ((a x : ℝ) - prevEndpoint b x))) *
              Real.exp (∑ x : Fin k, -((r : ℝ) * ((b x.castSucc : ℝ) - a x.castSucc)))) *
            (1 - Real.exp (-((r : ℝ) * ((b (Fin.last k) : ℝ) - a (Fin.last k)))))) := by ring
    _ = (∏ x : Fin k, (r : ℝ) * ((b x.castSucc : ℝ) - a x.castSucc)) *
          (Real.exp (-((r : ℝ) * a (Fin.last k))) -
            Real.exp (-((r : ℝ) * a (Fin.last k))) *
              Real.exp (-((r : ℝ) * ((b (Fin.last k) : ℝ) - a (Fin.last k))))) := by
        rw [hprod_exp]
        ring
    _ = boxFormula (r : ℝ) a b := by
        rw [← Real.exp_add, hexp_b, boxFormula]

end Helpers

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A Poisson random measure with zero intensity vanishes almost surely. No topological or
countability hypothesis on the state space is needed. -/
theorem IsPoissonRandomMeasure.ae_eq_zero {X : Type*} [MeasurableSpace X]
    {N : Ω → Measure X} (h : IsPoissonRandomMeasure P N 0) :
    ∀ᵐ ω ∂P, N ω = 0 := by
  have hlaw : HasLaw (fun ω => N ω univ) (Measure.dirac 0) P := by
    simpa [poissonMeasure_zero] using h.hasLaw MeasurableSet.univ (by simp)
  filter_upwards [hlaw.ae_eq_of_dirac] with ω hω
  exact Measure.measure_univ_eq_zero.mp hω

/-- For a Poisson random measure on `ℝ≥0` with zero intensity, every occurrence time is infinite
almost surely. -/
theorem IsPoissonRandomMeasure.ae_forall_occurrenceTime_eq_top_of_zero
    {N : Ω → Measure ℝ≥0} (h : IsPoissonRandomMeasure P N 0) :
    ∀ᵐ ω ∂P, ∀ n, (N ω).occurrenceTime n = ∞ := by
  filter_upwards [h.ae_eq_zero] with ω hω n
  simp [hω]

/-- For a Poisson random measure on `ℝ≥0` with zero intensity, every extended interarrival gap is
infinite almost surely. -/
theorem IsPoissonRandomMeasure.ae_forall_occurrenceGap_eq_top_of_zero
    {N : Ω → Measure ℝ≥0} (h : IsPoissonRandomMeasure P N 0) :
    ∀ᵐ ω ∂P, ∀ n, (N ω).occurrenceGap n = ∞ := by
  filter_upwards [h.ae_eq_zero] with ω hω n
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
  let := nnvolume.isLocallyFiniteMeasure_smul (c := (r : ℝ≥0∞)) ENNReal.coe_ne_top
  have hmeas : Measurable fun ω (i : Fin m) => ((N ω).occurrenceTime i).toNNReal :=
    measurable_pi_iff.mpr fun i =>
      ((Measure.measurable_occurrenceTime i).comp h.measurable).ennreal_toNNReal
  have heq_ps : (fun (x : Fin m → ℝ≥0) (i : Fin m) => ∑ j ∈ Finset.Iic i, x j) = partialSum m := by
    funext x i
    exact (partialSum_eq_sum_Iic m x i).symm
  rw [heq_ps]
  refine ⟨hmeas.aemeasurable, ?_⟩
  cases m with
  | zero =>
    apply Measure.ext_of_Ioc_strictMono
    · exact Filter.Eventually.of_forall fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩
    · exact Filter.Eventually.of_forall fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩
    · intro a b _
      have huniv : (univ.pi fun i : Fin 0 => Ioc (a i) (b i)) = univ := by
        ext x
        simp
      rw [huniv, measure_univ, measure_univ]
  | succ k =>
    apply Measure.ext_of_Ioc_strictMono
    · apply (ae_map_iff hmeas.aemeasurable
        (p := fun s : Fin (k + 1) → ℝ≥0 => (∀ i, 0 < s i) ∧ StrictMono s)
        (measurableSet_setOf_pos_and_strictMono (k + 1))).mpr
      filter_upwards [h.ae_isLocallyFiniteMeasure, h.ae_isIntegerValued,
        h.ae_forall_singleton_le_one_smul_nnvolume,
        h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hlf hint hsimple hposfin
      refine ⟨fun i => ENNReal.toNNReal_pos (hposfin i).1.ne' (hposfin i).2.ne, ?_⟩
      have hmono_nat : StrictMono fun n : ℕ => ((N ω).occurrenceTime n).toNNReal :=
        strictMono_nat_of_lt_succ fun n =>
          (ENNReal.toNNReal_lt_toNNReal (hposfin n).2.ne (hposfin (n + 1)).2.ne).mpr
            (hint.occurrenceTime_lt_succ (hposfin n).2.ne (hsimple _))
      exact fun i j hij => hmono_nat hij
    · apply (ae_map_iff (measurable_partialSum (k + 1)).aemeasurable
        (p := fun s : Fin (k + 1) → ℝ≥0 => (∀ i, 0 < s i) ∧ StrictMono s)
        (measurableSet_setOf_pos_and_strictMono (k + 1))).mpr
      have hae_coord : ∀ᵐ x ∂Measure.pi (fun _ : Fin (k + 1) => nnrealExpMeasure r),
          ∀ i, 0 < x i := by
        rw [ae_all_iff]
        intro i
        exact (measurePreserving_eval (fun _ : Fin (k + 1) => nnrealExpMeasure r)
          i).quasiMeasurePreserving.ae ae_pos_nnrealExpMeasure
      filter_upwards [hae_coord] with x hx
      refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · rw [partialSum_eq_sum_Iic]
        exact lt_of_lt_of_le (hx i)
          (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_Iic.mpr le_rfl))
      · rw [partialSum_eq_sum_Iic, partialSum_eq_sum_Iic]
        have hsub : Finset.Iic i ⊆ Finset.Iic j := Finset.Iic_subset_Iic.mpr hij.le
        have hnotMem : j ∉ Finset.Iic i := by simp [not_le.mpr hij]
        calc
          ∑ l ∈ Finset.Iic i, x l < ∑ l ∈ Finset.Iic i, x l + x j := lt_add_of_pos_right _ (hx j)
          _ = ∑ l ∈ insert j (Finset.Iic i), x l := by rw [Finset.sum_insert hnotMem, add_comm]
          _ ≤ ∑ l ∈ Finset.Iic j, x l := Finset.sum_le_sum_of_subset
            (Finset.insert_subset (Finset.mem_Iic.mpr le_rfl) hsub)
    · intro a b hsep
      rw [poisson_occurrenceTime_apply_separatedBox h hsep,
        map_partialSum_pi_apply_separatedBox k hr' hsep]

/-- The first `m` finite interarrival-gap representatives of a positive-rate homogeneous Poisson
random measure have the product exponential law on `Fin m → ℝ≥0`. -/
theorem IsPoissonRandomMeasure.hasLaw_toNNReal_occurrenceGap_prefix
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (m : ℕ) :
    HasLaw (fun ω (i : Fin m) => ((N ω).occurrenceGap i).toNNReal)
      (Measure.pi fun _ : Fin m => nnrealExpMeasure r) P := by
  have hcomp := (hasLaw_map (measurable_gapOfPartialSum m).aemeasurable).comp
    (h.hasLaw_toNNReal_occurrenceTime_prefix hr m)
  have heq_ps : (fun (x : Fin m → ℝ≥0) (i : Fin m) => ∑ j ∈ Finset.Iic i, x j) = partialSum m := by
    funext x i
    exact (partialSum_eq_sum_Iic m x i).symm
  rw [heq_ps, Measure.map_map (measurable_gapOfPartialSum m) (measurable_partialSum m),
    gapOfPartialSum_comp_partialSum, Measure.map_id] at hcomp
  refine hcomp.congr ?_
  filter_upwards [h.ae_forall_occurrenceTime_pos_lt_top hr] with ω hfin
  funext i
  simp only [Function.comp_apply, gapOfPartialSum]
  split_ifs with hi
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
    have hi_eq : (i : ℕ) = n + 1 := hn
    simp only [hi_eq, Nat.add_sub_cancel]
    exact Measure.toNNReal_occurrenceGap_succ (hfin n).2.ne
  · have hi0 : (i : ℕ) = 0 := by omega
    simp [hi0]

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
    measurePreserving_pi _ _ fun _ => ⟨by fun_prop, map_coe_nnrealExpMeasure⟩
  exact (hmp.hasLaw.comp (h.hasLaw_toNNReal_occurrenceGap_prefix hr m)).congr
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Each finite `ℝ≥0` interarrival-gap representative of a positive-rate homogeneous Poisson
random measure has law `nnrealExpMeasure r`. -/
theorem IsPoissonRandomMeasure.hasLaw_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω => ((N ω).occurrenceGap n).toNNReal) (nnrealExpMeasure r) P := by
  have hr' : 0 < (r : ℝ) := hr
  let := isProbabilityMeasure_nnrealExpMeasure hr'
  have heval := (measurePreserving_eval (fun _ : Fin (n + 1) => nnrealExpMeasure r)
    (Fin.last n)).hasLaw.comp (h.hasLaw_toNNReal_occurrenceGap_prefix hr (n + 1))
  exact heval.congr (Filter.Eventually.of_forall fun _ => rfl)

/-- Each real-valued interarrival-gap representative of a positive-rate homogeneous Poisson
random measure has the exponential law of rate `r`. -/
theorem IsPoissonRandomMeasure.hasLaw_toReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω => ((N ω).occurrenceGap n).toReal) (expMeasure r) P := by
  have hr' : 0 < (r : ℝ) := hr
  let := isProbabilityMeasure_expMeasure hr'
  have heval := (measurePreserving_eval (fun _ : Fin (n + 1) => expMeasure r)
    (Fin.last n)).hasLaw.comp (h.hasLaw_toReal_occurrenceGap_prefix hr (n + 1))
  exact heval.congr (Filter.Eventually.of_forall fun _ => rfl)

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

/-- The finite `ℝ≥0` interarrival-gap representatives of a homogeneous Poisson random measure are
mutually independent for every rate `r : ℝ≥0`. -/
theorem IsPoissonRandomMeasure.iIndepFun_toNNReal_occurrenceGap
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ProbabilityTheory.iIndepFun (fun n ω => ((N ω).occurrenceGap n).toNNReal) P :=
  h.iIndepFun_occurrenceGap.comp (fun _ => ENNReal.toNNReal) (fun _ => ENNReal.measurable_toNNReal)

/-- The real-valued interarrival-gap representatives of a homogeneous Poisson random measure are
mutually independent for every rate `r : ℝ≥0`. -/
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
