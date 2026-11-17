/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.SuccessorArray
public import TauCeti.Probability.Process.PathLaw.Shift
public import Mathlib.Dynamics.BirkhoffSum.NormedSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Occupation counts and finite shifts

The expected occupation count is the sum of the individual visit probabilities.
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

/-- The expected number of visits in the first `n` observations is the sum of their
probabilities. The initial observation is included. A finite measure suffices. -/
theorem integral_visitCount {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure Ω} [IsFiniteMeasure μ]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i)) (y : α) (n : ℕ) :
    ∫ ω, (visitCount (fun k => X k ω) y n : ℝ) ∂μ =
      ∑ i ∈ Finset.range n, μ.real {ω | X i ω = y} := by
  classical
  have heq (ω : Ω) : (visitCount (fun k => X k ω) y n : ℝ) =
      ∑ i ∈ Finset.range n, {ω | X i ω = y}.indicator (fun _ => (1 : ℝ)) ω := by
    rw [visitCount_eq_count, Nat.count_eq_card_filter_range, Finset.card_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Set.indicator_apply, Set.mem_ofPred_eq]
  simp_rw [heq]
  have hs (i : ℕ) : MeasurableSet {ω | X i ω = y} :=
    (measurableSet_singleton y).preimage (hX i)
  rw [integral_finsetSum _ (fun i _ => (integrable_const (1 : ℝ)).indicator (hs i))]
  exact Finset.sum_congr rfl fun i _ =>
    integral_indicator_one ((measurableSet_singleton y).preimage (hX i))

end TauCeti.Probability
