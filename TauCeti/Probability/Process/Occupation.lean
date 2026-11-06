/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.SuccessorArray
public import TauCeti.Probability.Process.PathLaw.Shift
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace

/-!
# Finite shifts of occupation frequencies

Deleting finitely many initial observations does not change a limiting visit frequency.
This pathwise fact allows occupation limits to pass through a finite entrance time.
The count `visitCount x y n` includes times zero through `n - 1`; shifting once gives the
positive-time convention, counting times one through `n`.
-/

public section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti.Probability

variable {α : Type*}

/-- Deleting any finite prefix preserves and reflects convergence of the visit frequency. -/
theorem tendsto_visitCount_shift_iterate_div_iff (x : ℕ → α) (y : α) (k : ℕ) (r : ℝ) :
    Tendsto (fun n => (visitCount ((shift α)^[k] x) y n : ℝ) / n) atTop (𝓝 r) ↔
      Tendsto (fun n => (visitCount x y n : ℝ) / n) atTop (𝓝 r) := by
  classical
  have hone (z : ℕ → α) :
      Tendsto (fun n => (visitCount (shift α z) y n : ℝ) / n) atTop (𝓝 r) ↔
        Tendsto (fun n => (visitCount z y n : ℝ) / n) atTop (𝓝 r) := by
    have hd : Tendsto (fun n =>
        (visitCount (shift α z) y n : ℝ) / n - (visitCount z y n : ℝ) / n)
        atTop (𝓝 0) := by
      have hb : Bornology.IsBounded (Set.range (fun w : ℕ → α =>
          if w 0 = y then (1 : ℝ) else 0)) := by
        refine (Metric.isBounded_Icc (0 : ℝ) 1).subset ?_
        rintro _ ⟨w, rfl⟩
        dsimp only
        split_ifs <;> norm_num
      have havg (w : ℕ → α) (n : ℕ) :
          birkhoffAverage ℝ (shift α) (fun v => if v 0 = y then (1 : ℝ) else 0) n w =
            (visitCount w y n : ℝ) / n := by
        rw [visitCount_eq_count, Nat.count_eq_card_filter_range, Finset.card_filter]
        simp only [birkhoffAverage, birkhoffSum, shift_iterate_apply, zero_add,
          Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, smul_eq_mul,
          div_eq_inv_mul]
      simpa only [havg] using
        tendsto_birkhoffAverage_apply_sub_birkhoffAverage' ℝ hb (shift α) z
    constructor
    · intro h
      simpa only [sub_zero, sub_sub_cancel] using h.sub hd
    · intro h
      simpa only [zero_add, sub_add_cancel] using hd.add h
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using (hone ((shift α)^[k] x)).trans ih

end TauCeti.Probability
