/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Order.Interval.SeparatedBox

import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Order.Interval.Set.OrderedSub
import TauCeti.MeasureTheory.Constructions.Pi
import TauCeti.MeasureTheory.Measure.StrictMono

/-!
# Cumulative sums of independent exponential random variables

This file establishes the finite-dimensional separated-box mass formula and almost-sure chamber
concentration for cumulative sums `x ↦ (i ↦ ∑ j ∈ Finset.Iic i, x j)` of independent
`nnrealExpMeasure r` variables.

## Main results

* `TauCeti.Probability.ae_pos_and_strictMono_map_sum_Iic_pi_nnrealExpMeasure` — cumulative sums
  of `m` independent `nnrealExpMeasure r` variables are almost surely strictly positive and
  strictly increasing.
* `TauCeti.Probability.map_sum_Iic_pi_nnrealExpMeasure_univ_pi_Ioc` — explicit closed-form mass
  assigned by cumulative sums of `k + 1` independent `nnrealExpMeasure r` variables (`0 ≤ r`) to
  any separated left-open, right-closed box `∏ᵢ (aᵢ, bᵢ]`.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

section Helpers

-- Nonempty prefix sums `x₀ + ⋯ + xᵢ`, implemented via Mathlib's `Fin.partialSum`.
private def partialSum (m : ℕ) (x : Fin m → ℝ≥0) (i : Fin m) : ℝ≥0 :=
  Fin.partialSum x i.succ

private lemma fun_sum_Iic_eq_partialSum (m : ℕ) :
    (fun (x : Fin m → ℝ≥0) (i : Fin m) => ∑ j ∈ Finset.Iic i, x j) = partialSum m := by
  funext x i
  exact (Fin.partialSum_succ_eq_sum_Iic x i).symm

@[fun_prop]
private lemma measurable_partialSum (m : ℕ) : Measurable (partialSum m) := by
  rw [← fun_sum_Iic_eq_partialSum]
  exact measurable_pi_iff.mpr fun i => Finset.measurable_fun_sum _ fun j _ => measurable_pi_apply j

private lemma partialSum_cons_zero {k : ℕ} (x₀ : ℝ≥0) (y : Fin k → ℝ≥0) :
    partialSum (k + 1) (Fin.cons x₀ y) 0 = x₀ := by
  rw [partialSum, Fin.partialSum_succ']
  simp

private lemma partialSum_cons_succ {k : ℕ} (x₀ : ℝ≥0) (y : Fin k → ℝ≥0) (i : Fin k) :
    partialSum (k + 1) (Fin.cons x₀ y) i.succ = x₀ + partialSum k y i := by
  simp [partialSum, Fin.partialSum_succ']

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

-- Shifting all remaining box endpoints down by `x₀ ≤ b 0` multiplies `boxFormula` by `exp (r x₀)`.
private lemma boxFormula_shift {k : ℕ} (r : ℝ) {a b : Fin (k + 2) → ℝ≥0}
    (hsep : IsSeparatedBox a b) {x₀ : ℝ≥0} (hx₀ : x₀ ≤ b 0) :
    boxFormula r (fun i : Fin (k + 1) => a i.succ - x₀)
        (fun i : Fin (k + 1) => b i.succ - x₀) =
      boxFormula r (fun i => a i.succ) (fun i => b i.succ) * Real.exp (r * x₀) := by
  have ha_ge (i : Fin (k + 1)) : x₀ ≤ a i.succ :=
    hx₀.trans (hsep.le_of_lt (Fin.succ_pos i))
  have hb_ge (i : Fin (k + 1)) : x₀ ≤ b i.succ := (ha_ge i).trans (hsep.le i.succ)
  have hprod : (∏ j : Fin k, r *
      (((b j.castSucc.succ - x₀ : ℝ≥0) : ℝ) - (a j.castSucc.succ - x₀ : ℝ≥0))) =
      ∏ j : Fin k, r * ((b j.castSucc.succ : ℝ) - a j.castSucc.succ) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [NNReal.coe_sub (hb_ge _), NNReal.coe_sub (ha_ge _)]
    ring
  have hexp_a : Real.exp (-(r * ((a (Fin.last k).succ - x₀ : ℝ≥0) : ℝ))) =
      Real.exp (-(r * a (Fin.last k).succ)) * Real.exp (r * x₀) := by
    rw [NNReal.coe_sub (ha_ge (Fin.last k)), ← Real.exp_add]
    congr 1
    ring
  have hexp_b : Real.exp (-(r * ((b (Fin.last k).succ - x₀ : ℝ≥0) : ℝ))) =
      Real.exp (-(r * b (Fin.last k).succ)) * Real.exp (r * x₀) := by
    rw [NNReal.coe_sub (hb_ge (Fin.last k)), ← Real.exp_add]
    congr 1
    ring
  simp only [boxFormula, hprod, hexp_a, hexp_b]
  ring

-- Cross-section of the `partialSum` preimage of a separated box at first coordinate `x₀`:
-- empty outside `(a 0, b 0]`, and the `partialSum` preimage of the `x₀`-shifted tail box inside.
private lemma preimage_cons_partialSum_separatedBox {k : ℕ} {a b : Fin (k + 2) → ℝ≥0}
    (hsep : IsSeparatedBox a b) (x₀ : ℝ≥0) :
    Prod.mk x₀ ⁻¹' ((fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2) ⁻¹'
      (partialSum (k + 2) ⁻¹' (univ.pi fun i : Fin (k + 2) => Ioc (a i) (b i)))) =
      if x₀ ∈ Ioc (a 0) (b 0) then
        partialSum (k + 1) ⁻¹'
          (univ.pi fun i : Fin (k + 1) => Ioc (a i.succ - x₀) (b i.succ - x₀))
      else ∅ := by
  split_ifs with hx₀
  · ext y
    simp only [mem_preimage, mem_univ_pi]
    rw [Fin.forall_fin_succ (n := k + 1)]
    simp only [partialSum_cons_zero, partialSum_cons_succ, hx₀, true_and]
    exact forall_congr' fun i =>
      Set.add_mem_Ioc_iff_tsub (hx₀.2.trans (hsep.le_of_lt (Fin.succ_pos i)))
  · ext y
    simp only [mem_preimage, mem_univ_pi, mem_empty_iff_false, iff_false]
    intro hy
    exact hx₀ (by simpa [partialSum_cons_zero] using hy 0)

-- Induction plan: for `k = 0`, push forward a single exponential to `(a 0, b 0]` via
-- `measure_Ioc_nnrealExpMeasure`; for `k + 1`, split off the first coordinate via `Fin.cons` +
-- Tonelli (`Measure.prod_apply`), evaluate each cross-section by IH + `boxFormula_shift`, and
-- integrate `exp (r x₀)` over `(a 0, b 0]` via `setLIntegral_Ioc_exp_mul_nnrealExpMeasure`.
private lemma map_partialSum_pi_apply_separatedBox (k : ℕ) {r : ℝ} (hr : 0 < r)
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    ((Measure.pi fun _ : Fin (k + 1) => nnrealExpMeasure r).map (partialSum (k + 1)))
        (univ.pi fun i => Ioc (a i) (b i)) =
      ENNReal.ofReal (boxFormula r a b) := by
  have _ : IsProbabilityMeasure (nnrealExpMeasure r) := isProbabilityMeasure_nnrealExpMeasure hr
  induction k with
  | zero =>
    rw [Measure.map_apply (measurable_partialSum 1)
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
    have hpre : partialSum 1 ⁻¹' (univ.pi fun i => Ioc (a i) (b i)) =
        (fun x : Fin 1 → ℝ≥0 => x 0) ⁻¹' Ioc (a 0) (b 0) := by
      ext x
      simp [partialSum, Fin.forall_fin_one, Fin.partialSum_succ']
    rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioc,
      (measurePreserving_eval (fun _ : Fin 1 => nnrealExpMeasure r) 0).map_eq,
      measure_Ioc_nnrealExpMeasure hr.le]
    simp [boxFormula]
  | succ k ih =>
    -- Split off coordinate `0` via `Fin.cons` and apply Tonelli.
    let ν_tail := Measure.pi fun _ : Fin (k + 1) => nnrealExpMeasure r
    let B := univ.pi fun i : Fin (k + 2) => Ioc (a i) (b i)
    have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ioc
    have hcons : MeasurePreserving
        (fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2)
        ((nnrealExpMeasure r).prod ν_tail)
        (Measure.pi fun _ : Fin (k + 2) => nnrealExpMeasure r) := by
      have hcons_eq : (fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2) =
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) => ℝ≥0) 0).symm :=
        funext fun p => (MeasurableEquiv.piFinSuccAbove_zero_symm_apply_eq_cons p.1 p.2).symm
      rw [hcons_eq]
      exact (measurePreserving_piFinSuccAbove
        (fun _ : Fin (k + 2) => nnrealExpMeasure r) 0).symm _
    rw [Measure.map_apply (measurable_partialSum (k + 2)) hB,
      ← hcons.measure_preimage ((measurable_partialSum (k + 2)) hB).nullMeasurableSet,
      Measure.prod_apply (hcons.measurable ((measurable_partialSum (k + 2)) hB))]
    -- Evaluate each `x₀`-slice using IH on the shifted tail box and `boxFormula_shift`.
    let C_tail := boxFormula r (fun i : Fin (k + 1) => a i.succ) (fun i : Fin (k + 1) => b i.succ)
    have hC_nonneg : 0 ≤ C_tail := boxFormula_nonneg hr.le (hsep.comp Fin.strictMono_succ)
    have hslice (x₀ : ℝ≥0) :
        ν_tail (Prod.mk x₀ ⁻¹' ((fun p : ℝ≥0 × (Fin (k + 1) → ℝ≥0) => Fin.cons p.1 p.2) ⁻¹'
          (partialSum (k + 2) ⁻¹' B))) =
          (Ioc (a 0) (b 0)).indicator
            (fun x => ENNReal.ofReal C_tail * ENNReal.ofReal (Real.exp (r * (x : ℝ)))) x₀ := by
      rw [preimage_cons_partialSum_separatedBox hsep x₀]
      by_cases hx₀ : x₀ ∈ Ioc (a 0) (b 0)
      · have hshift : IsSeparatedBox (fun i : Fin (k + 1) => a i.succ - x₀)
            (fun i : Fin (k + 1) => b i.succ - x₀) :=
          (hsep.comp Fin.strictMono_succ).sub_const x₀
        rw [ite_eq_left hx₀, indicator_of_mem hx₀,
          ← Measure.map_apply (measurable_partialSum (k + 1))
            (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
        dsimp only [ν_tail]
        rw [ih hshift, boxFormula_shift r hsep hx₀.2, ENNReal.ofReal_mul hC_nonneg]
      · simp [hx₀]
    -- Integrate `exp (r x₀)` over `(a 0, b 0]` and fold the leading factor into `boxFormula`.
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Ioc, lintegral_const_mul _ (by fun_prop),
      setLIntegral_Ioc_exp_mul_nnrealExpMeasure hr.le (a 0) (b 0), ← ENNReal.ofReal_mul hC_nonneg]
    congr 1
    simp only [boxFormula, C_tail, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.succ_castSucc,
      Fin.succ_last]
    ring

end Helpers

/-- Cumulative sums of `m` independent `nnrealExpMeasure r` variables are almost surely strictly
positive and strictly increasing (trivially for `r ≤ 0`, where the measure vanishes when `m > 0`,
and vacuously at `m = 0`). -/
theorem ae_pos_and_strictMono_map_sum_Iic_pi_nnrealExpMeasure (r : ℝ) (m : ℕ) :
    ∀ᵐ s ∂((Measure.pi fun _ : Fin m => nnrealExpMeasure r).map
        fun x i => ∑ j ∈ Finset.Iic i, x j),
      (∀ i, 0 < s i) ∧ StrictMono s := by
  have : SigmaFinite (nnrealExpMeasure r) := by
    rcases le_or_gt r 0 with hr | hr
    · rw [nnrealExpMeasure_def, ProbabilityTheory.expMeasure_of_nonpos hr, Measure.map_zero]
      infer_instance
    · have := isProbabilityMeasure_nnrealExpMeasure hr
      infer_instance
  exact Measure.ae_pos_and_strictMono_map_sum_Iic_pi _ fun _ => ae_pos_nnrealExpMeasure r

/-- The mass assigned by the cumulative sums of `k + 1` independent `nnrealExpMeasure r`
variables (`0 ≤ r`) to a separated left-open, right-closed box `∏ᵢ (aᵢ, bᵢ]` equals
`(∏ j : Fin k, r * (b j - a j)) * (e^{-r a_k} - e^{-r b_k})`. At `r = 0`, both sides vanish. -/
theorem map_sum_Iic_pi_nnrealExpMeasure_univ_pi_Ioc {k : ℕ} {r : ℝ} (hr : 0 ≤ r)
    {a b : Fin (k + 1) → ℝ≥0} (hsep : IsSeparatedBox a b) :
    ((Measure.pi fun _ : Fin (k + 1) => nnrealExpMeasure r).map
        fun x i => ∑ j ∈ Finset.Iic i, x j) (univ.pi fun i => Ioc (a i) (b i)) =
      ENNReal.ofReal ((∏ j : Fin k, r * ((b j.castSucc : ℝ) - a j.castSucc)) *
        (Real.exp (-(r * (a (Fin.last k) : ℝ))) - Real.exp (-(r * (b (Fin.last k) : ℝ))))) := by
  rcases eq_or_lt_of_le hr with rfl | hrpos
  · have h0 : nnrealExpMeasure 0 = 0 := by simp [nnrealExpMeasure_def]
    have hzero : (Measure.pi fun _ : Fin (k + 1) => nnrealExpMeasure 0) = 0 := by
      simp_rw [h0]
      rw [← Measure.measure_univ_eq_zero, Measure.pi_univ]
      simp
    simp [hzero]
  · rw [fun_sum_Iic_eq_partialSum]
    exact map_partialSum_pi_apply_separatedBox k hrpos hsep

end TauCeti.Probability
