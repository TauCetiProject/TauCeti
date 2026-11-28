/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension.Basic
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Analysis.SpecialFunctions.Log.Factorial

/-!
# The Weyl dimension formula in logarithmic coordinates

Group the factors of the Weyl dimension formula by their right index. The denominator for
index `j` is `j!`; this makes it possible to cancel the contribution from an initial segment
where the shifted weights are successive integers.
-/

public section

open Finset Real

namespace TauCeti

/-- The Weyl dimension in logarithmic form, grouped by the larger index of each pair. -/
theorem log_weylDimension_eq_sum {n : ℕ} (l : DominantWeight n) :
    log (weylDimension l : ℝ) = ∑ j : Fin n,
      ((∑ i ∈ Iio j, log ((l.rhoShift i : ℝ) - l.rhoShift j)) - log (j.val.factorial : ℝ)) := by
  have hpos (i j : Fin n) (hij : i < j) : 0 < (l.rhoShift i : ℝ) - l.rhoShift j := by
    exact sub_pos.mpr (by exact_mod_cast l.rhoShift_strictAnti hij)
  have hd (i j : Fin n) (hij : i < j) : 0 < (j : ℝ) - i := by
    exact sub_pos.mpr (by exact_mod_cast hij)
  have hdim : (weylDimension l : ℝ) = ∏ i : Fin n, ∏ j ∈ Ioi i,
      ((l.rhoShift i : ℝ) - l.rhoShift j) / ((j : ℝ) - i) := by
    have he := congrArg ((↑) : ℚ → ℝ) (weylDimension_eq_prod_prod_div l)
    push_cast at he
    refine he.trans (prod_congr rfl fun i _ ↦ prod_congr rfl fun j _ ↦ ?_)
    have hf := congrArg ((↑) : ℤ → ℝ) (l.rhoShift_sub_rhoShift i j)
    push_cast at hf
    rw [hf]
  rw [hdim]
  rw [log_prod (fun i _ ↦ (prod_pos fun j hj ↦
    div_pos (hpos i j (mem_Ioi.mp hj)) (hd i j (mem_Ioi.mp hj))).ne')]
  calc
    _ = ∑ i : Fin n, ∑ j ∈ Ioi i,
        (log ((l.rhoShift i : ℝ) - l.rhoShift j) - log ((j : ℝ) - i)) := by
      refine sum_congr rfl fun i _ ↦ ?_
      rw [log_prod fun j hj ↦ (div_pos (hpos i j (mem_Ioi.mp hj))
        (hd i j (mem_Ioi.mp hj))).ne']
      exact sum_congr rfl fun j hj ↦ log_div (hpos i j (mem_Ioi.mp hj)).ne'
        (hd i j (mem_Ioi.mp hj)).ne'
    _ = ∑ j : Fin n, ∑ i ∈ Iio j,
        (log ((l.rhoShift i : ℝ) - l.rhoShift j) - log ((j : ℝ) - i)) := by
      simp only [← filter_lt_eq_Ioi, ← filter_gt_eq_Iio, sum_filter]
      exact sum_comm
    _ = _ := by simp only [sum_sub_distrib, Fin.sum_log_sub_eq_log_factorial]

/-- When the first `a` entries of a dominant weight are constant, their internal pairs contribute
`1` to the Weyl quotient. After adding back the remaining factorial denominators, the log degree
is the sum of the log differences with right index in the tail. -/
theorem log_weylDimension_add_sum_tail_log_factorial {a m : ℕ} (l : DominantWeight (a + m))
    (hl : ∀ i j : Fin (a + m), i < j → j.val < a → l.val i = l.val j) :
    log (weylDimension l : ℝ) + ∑ j : Fin m, log ((a + j.val).factorial : ℝ) =
      ∑ j : Fin m, ∑ i ∈ Iio (j.natAdd a), log ((l.rhoShift i : ℝ) - l.rhoShift (j.natAdd a)) := by
  rw [log_weylDimension_eq_sum, Fin.sum_univ_add]
  have h (j : Fin a) :
      (∑ i ∈ Iio (j.castAdd m), log ((l.rhoShift i : ℝ) - l.rhoShift (j.castAdd m))) =
        log ((j.castAdd m).val.factorial : ℝ) := by
    rw [← Fin.sum_log_sub_eq_log_factorial]
    refine sum_congr rfl fun i hi ↦ congrArg log ?_
    have hj : (j.castAdd m).val < a := j.isLt
    have he := l.rhoShift_sub_rhoShift i (j.castAdd m)
    rw [hl _ _ (mem_Iio.mp hi) hj, sub_self, zero_add] at he
    exact_mod_cast he
  simp only [h, sub_self, sum_const_zero, zero_add, Fin.val_natAdd, sum_sub_distrib,
    sub_add_cancel]

end TauCeti
