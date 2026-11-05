/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.SuccessorArray
public import TauCeti.Probability.Process.PathLaw.Shift
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Continuity

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
theorem tendsto_visitCount_div_shift_iff (x : ℕ → α) (y : α) (k : ℕ) (r : ℝ) :
    Tendsto (fun n => (visitCount ((shift α)^[k] x) y n : ℝ) / n) atTop (𝓝 r) ↔
      Tendsto (fun n => (visitCount x y n : ℝ) / n) atTop (𝓝 r) := by
  classical
  have hone (z : ℕ → α) :
      Tendsto (fun n => (visitCount (shift α z) y n : ℝ) / n) atTop (𝓝 r) ↔
        Tendsto (fun n => (visitCount z y n : ℝ) / n) atTop (𝓝 r) := by
    have hd : Tendsto (fun n =>
        (visitCount (shift α z) y n : ℝ) / n - (visitCount z y n : ℝ) / n)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (f := fun n =>
        (visitCount (shift α z) y n : ℝ) / n - (visitCount z y n : ℝ) / n) (fun n => ?_)
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0))
      have hc := visitCount_add z y 1 n
      have he : (visitCount (shift α z) y n : ℝ) - visitCount z y n =
          (if z n = y then 1 else 0) - (if z 0 = y then 1 else 0) := by
        rw [Nat.add_comm 1 n, visitCount_succ, visitCount_succ, visitCount_zero,
          zero_add] at hc
        have hc' : visitCount (fun i => z (1 + i)) y n = visitCount (shift α z) y n := by
          congr 1
          funext i
          simp [Nat.add_comm]
        rw [hc'] at hc
        have hcR := congrArg (fun m : ℕ => (m : ℝ)) hc
        push_cast at hcR
        split_ifs at hcR ⊢ <;> linarith
      rw [← sub_div, Real.norm_eq_abs, abs_div, he,
        abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hb : |(if z n = y then (1 : ℝ) else 0) - (if z 0 = y then 1 else 0)| ≤ 1 := by
        split_ifs <;> norm_num
      exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg n)
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
