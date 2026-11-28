/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.CycleWord.NormBounds
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.RingTheory.PowerSeries.EvalAt

/-!
# Analytic evaluation of finite cycle-trace generating functions

For a finite linearly ordered alphabet `ι` and weights `p : ι → K` over a complete normed field `K`,
`TauCeti.TypeAHeckeAlgebra.summable_norm_atomicTrace_cycleWord_mul_pow` and
`TauCeti.TypeAHeckeAlgebra.atomicTrace_cycleWord_generating_eval` establish absolute summability
and evaluate the formal generating identity on the convergence disk.
-/

public section

open Finsupp

namespace TauCeti.TypeAHeckeAlgebra

/-- Absolute summability of the finite cycle-trace generating series on the convergence disk. -/
theorem summable_norm_atomicTrace_cycleWord_mul_pow {K : Type*} [NormedField K] {ι : Type*}
    [LinearOrder ι] [Fintype ι] (pos : ι → Prop) [DecidablePred pos] (q : Kˣ) (p : ι → K)
    {x : K} (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) :
    Summable fun m : ℕ ↦ ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖ :=
  summable_norm_mul_pow_succ_of_le (by positivity) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hx
    fun m ↦ by simpa only [norm_one, one_mul] using norm_atomicTrace_cycleWord_le pos q p m

private theorem eval_denom_ne_zero {K : Type*} [NormedField K] {ι : Type*} [Fintype ι]
    (pos : ι → Prop) [DecidablePred pos] (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) (a : ι) :
    (cycleGeneratingFactor pos p ((q : K) ^ 2) 1 a).eval x ≠ 0 := by
  rw [eval_cycleGeneratingFactor]
  set M : ℝ := max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖)
  have hpa : ‖p a‖ ≤ ∑ b, ‖p b‖ := Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) (by simp)
  have h1M : 1 ≤ M := le_max_left _ _
  have hQM : ‖(q : K) ^ 2‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  split_ifs <;> intro h0
  · have : ‖(q : K) ^ 2 * p a * x‖ = 1 := by simpa [sub_eq_zero.mp h0] using norm_one (α := K)
    linarith [show ‖(q : K) ^ 2 * p a * x‖ ≤ M * (∑ b, ‖p b‖) * ‖x‖ by simp only [norm_mul]; gcongr]
  · have : ‖p a * x‖ = 1 := by rw [show p a * x = -1 from eq_neg_of_add_eq_zero_left (by
      simpa [add_comm] using h0), norm_neg, norm_one]
    linarith [show ‖p a * x‖ ≤ M * (∑ b, ‖p b‖) * ‖x‖ by rw [norm_mul, ← one_mul ‖p a‖]; gcongr]

/-- **Analytic evaluation of the cycle-trace generating function on a finite alphabet** on the disk
`max 1 (max ‖Q‖ ‖Q - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1` (`Q = q ^ 2`). -/
theorem atomicTrace_cycleWord_generating_eval {K : Type*} [NormedField K]
    [CompleteSpace K] {ι : Type*} [LinearOrder ι] [Fintype ι] (pos : ι → Prop) [DecidablePred pos]
    (q : Kˣ) (p : ι → K) {x : K}
    (hx : max 1 (max ‖(q : K) ^ 2‖ ‖(q : K) ^ 2 - 1‖) * (∑ a, ‖p a‖) * ‖x‖ < 1) :
    (Summable fun m : ℕ ↦ ‖atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) * x ^ (m + 1)‖) ∧
      1 + ((q : K) ^ 2 - 1) * (∑' m : ℕ, atomicTrace pos q p (m + 1) (cycleWord q (m + 1)) *
        x ^ (m + 1)) = ∏ a, (if pos a then (1 - p a * x) / (1 - (q : K) ^ 2 * p a * x)
          else (1 + (q : K) ^ 2 * p a * x) / (1 + p a * x)) := by
  have hsum := summable_norm_atomicTrace_cycleWord_mul_pow pos q p hx; refine ⟨hsum, ?_⟩
  let F : PowerSeries K := PowerSeries.mk fun m ↦
    if m = 0 then 1 else ((q : K) ^ 2 - 1) * atomicTrace pos q p m (cycleWord q m)
  let P : Polynomial K := ∏ a, cycleGeneratingFactor pos p ((q : K) ^ 2) 1 a
  let Qp : Polynomial K := ∏ a, cycleGeneratingFactor pos p 1 ((q : K) ^ 2) a
  have hF_sum : Summable fun m : ℕ ↦ ‖PowerSeries.coeff m F • x ^ m‖ :=
    (summable_nat_add_iff 1).mp <| (hsum.mul_left ‖(q : K) ^ 2 - 1‖).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun m ↦ by simp [F, smul_eq_mul, mul_assoc]
  have heval := PowerSeries.evalAt_mul_coe_of_summable_norm P hF_sum
  have hFP : F * (P : PowerSeries K) = (Qp : PowerSeries K) := by
    dsimp only [F, P, Qp]; simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    exact atomicTrace_cycleWord_generating_function_eq_prod pos q p
  rw [hFP, PowerSeries.evalAt_coe, PowerSeries.evalAt_def, hF_sum.of_norm.tsum_eq_zero_add] at heval
  simp only [F, P, Qp, PowerSeries.coeff_mk, ↓reduceIte, smul_eq_mul, pow_zero, mul_one,
    Nat.succ_ne_zero, mul_assoc, hsum.of_norm.tsum_mul_left, Polynomial.coe_aeval_eq_eval,
    Polynomial.eval_prod] at heval
  rw [(eq_div_iff (Finset.prod_ne_zero_iff.mpr fun a _ ↦ eval_denom_ne_zero pos q p hx a)).mpr
    heval.symm, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun a _ ↦ by
    simp only [eval_cycleGeneratingFactor]; split_ifs <;> simp

end TauCeti.TypeAHeckeAlgebra
