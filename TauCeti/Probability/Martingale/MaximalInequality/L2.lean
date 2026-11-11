/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Order.PartialSups
import Mathlib.Order.SuccPred.Nat
import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Doob's L² maximal inequality

For a nonnegative square-integrable submartingale, the second moment of its running maximum
through time `n` is at most four times its terminal second moment. The martingale version
bounds the maximum of the norms, allowing Banach-valued martingales. These estimates control
uniform approximation of stochastic integral processes on finite sampling grids.

The maximum is the native `partialSups`, so no boundedness or attainment convention is needed.
All moments used in the proof are established before taking expectations. The proof uses a
pathwise summation-by-parts inequality and predictable weighted increments, rather than a
layer-cake argument.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, Theorem 3.8 (Doob's inequalities), for the statement.
* B. Acciaio, M. Beiglböck, F. Penkner, W. Schachermayer, J. Temme,
  *A trajectorial interpretation of Doob's martingale inequalities*,
  Ann. Appl. Probab. 23(4) (2013), 1494–1505, for the pathwise proof method.
-/

public section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

namespace TauCeti

/-- The pathwise maximal inequality underlying Doob's L² bound. The sum is the gain from
holding the running maximum over each following increment. This is the trajectorial method of
Acciaio–Beiglböck–Penkner–Schachermayer–Temme, *A trajectorial interpretation of Doob's
martingale inequalities* (2013). No sign assumption is needed here. -/
theorem sq_partialSups_le_four_mul_sq_sub_sum (x : ℕ → ℝ) (n : ℕ) :
    partialSups x n ^ 2 ≤ 4 * x n ^ 2 -
      4 * ∑ k ∈ range n, partialSups x k * (x (k + 1) - x k) := by
  have h (n : ℕ) : partialSups x n ^ 2 ≤ 2 * x n * partialSups x n -
      2 * ∑ k ∈ range n, partialSups x k * (x (k + 1) - x k) := by
    induction n with
    | zero => simp only [partialSups_zero, range_zero, sum_empty]; nlinarith [sq_nonneg (x 0)]
    | succ n ih =>
      have hmax := partialSups_succ x n
      simp only [Order.succ_eq_add_one] at hmax
      rw [sum_range_succ, hmax]
      rcases le_total (x (n + 1)) (partialSups x n) with hle | hle
      · rw [sup_eq_left.mpr hle]
        nlinarith
      · rw [sup_eq_right.mpr hle]
        nlinarith [sq_nonneg (x (n + 1) - partialSups x n)]
  nlinarith [h n, sq_nonneg (partialSups x n - 2 * x n)]

end TauCeti

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ}

/-- **Doob's L² maximal inequality** for a nonnegative submartingale on a finite time grid.
A second moment is required only at the terminal time. -/
theorem Submartingale.integral_sq_partialSups_le (hf : Submartingale f ℱ μ)
    (hpos : ∀ k, 0 ≤ᵐ[μ] f k) (n : ℕ) (hn : MemLp (f n) 2 μ) :
    ∫ ω, (partialSups f n ω) ^ 2 ∂μ ≤ 4 * ∫ ω, (f n ω) ^ 2 ∂μ := by
  -- Terminal square integrability controls all earlier values and their finite maxima.
  have hL2 (k : ℕ) (hk : k ≤ n) : MemLp (f k) 2 μ :=
    hf.memLp_of_le hk (hpos k) (by norm_num) hn
  have hM (k : ℕ) (hk : k ≤ n) : MemLp (partialSups f k) 2 μ := by
    rw [partialSups_apply]
    exact Finset.sup'_induction _ _ (p := fun g => MemLp g 2 μ)
      (fun _ hf _ hg => hf.sup hg) (fun j hj => hL2 j ((mem_Iic.mp hj).trans hk))
  have hMa (k : ℕ) : StronglyMeasurable[ℱ k] (partialSups f k) := by
    let : MeasurableSpace Ω := ℱ k
    rw [partialSups_apply]
    exact Finset.sup'_induction _ _ (fun _ hf _ hg => hf.sup hg)
      (fun j hj => (hf.stronglyAdapted j).mono (ℱ.mono (mem_Iic.mp hj)))
  have hG (k : ℕ) (hk : k < n) :
      Integrable (fun ω => partialSups f k ω * (f (k + 1) ω - f k ω)) μ :=
    (hM k (by omega)).integrable_mul ((hL2 _ (by omega)).sub (hL2 _ (by omega)))
  -- Each running maximum is a nonnegative position known before its next increment.
  have hGpos (k : ℕ) (hk : k < n) :
      0 ≤ ∫ ω, partialSups f k ω * (f (k + 1) ω - f k ω) ∂μ := by
    have hle := hf.integral_mul_le (Nat.le_succ k) (hMa k)
      ((hpos k).mono fun ω hp => hp.trans (le_partialSups f k ω))
      ((hM k (by omega)).integrable_mul (hL2 k (by omega)))
      ((hM k (by omega)).integrable_mul (hL2 (k + 1) (by omega)))
    simp_rw [mul_sub]
    have hprod (j : ℕ) (hj : j ≤ n) :
        Integrable (fun ω => partialSups f k ω * f j ω) μ := by
      simpa only [Pi.mul_def] using (hM k (by omega)).integrable_mul (hL2 j hj)
    rw [integral_sub (hprod (k + 1) (by omega)) (hprod k (by omega))]
    linarith
  have hsum : Integrable (fun ω => ∑ k ∈ range n,
      partialSups f k ω * (f (k + 1) ω - f k ω)) μ :=
    integrable_finsetSum _ fun k hk => hG k (mem_range.mp hk)
  have hsumpos : 0 ≤ ∫ ω, ∑ k ∈ range n,
      partialSups f k ω * (f (k + 1) ω - f k ω) ∂μ := by
    rw [integral_finsetSum _ fun k hk => hG k (mem_range.mp hk)]
    exact sum_nonneg fun k hk => hGpos k (mem_range.mp hk)
  -- Integrate the pathwise bound only after establishing integrability of every gain.
  have hbound := integral_mono (hM n le_rfl).integrable_sq
    (((hL2 n le_rfl).integrable_sq.const_mul 4).sub (hsum.const_mul 4))
    (fun ω => by simpa only [Pi.partialSups_apply, Pi.sub_apply] using
      TauCeti.sq_partialSups_le_four_mul_sq_sub_sum (fun k => f k ω) n)
  simp only [Pi.sub_apply] at hbound
  rw [integral_sub ((hL2 n le_rfl).integrable_sq.const_mul 4) (hsum.const_mul 4),
    integral_const_mul, integral_const_mul] at hbound
  linarith

/-- **Doob's L² maximal inequality** for the norms of a Banach-valued martingale.
The second moment of the finite running maximum is bounded by four times the terminal
second moment. -/
theorem Martingale.integral_sq_partialSups_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {X : ℕ → Ω → E} (hX : Martingale X ℱ μ)
    (n : ℕ) (hn : MemLp (X n) 2 μ) :
    ∫ ω, (partialSups (fun k ω => ‖X k ω‖) n ω) ^ 2 ∂μ ≤
      4 * ∫ ω, ‖X n ω‖ ^ 2 ∂μ :=
  hX.norm.integral_sq_partialSups_le (fun k => .of_forall fun ω => norm_nonneg (X k ω)) n hn.norm

end MeasureTheory
