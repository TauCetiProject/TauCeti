/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.AuxiliaryFunction
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An instance of the auxiliary function

`TauCeti.exists_ne_zero_int_norm_sum_le` applies to the `1024` constant functions `1` in one
variable, with `N = 1`, `U = log 1024`, `V = 6`, `r = 1` and `R = e ^ 2`. Then
`W = 7 + log 1024 ≈ 13.93`, so `12 ≤ W` and `e ≤ R / r = e ^ 2 ≤ exp (W / 6)`, and the count
`(2 W) ^ 2 ≈ 776.3` is at most `1024 · 1 · log (e ^ 2) = 2048`. All the hypotheses hold together.

The conclusion gives integers `p_λ`, not all zero, with `|p_λ| ≤ e` and `|∑ p_λ| ≤ e ^ (-6)`. An
integer of absolute value less than `1` is `0`, so `∑ p_λ = 0`, as for `(1, -1, 0, …, 0)`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Grundlehren der
  mathematischen Wissenschaften 326, Springer, 2000, §4.5, Proposition 4.10 (pp. 131–132).
-/

public section

namespace TauCeti.AuxiliaryFunctionExample

open Metric

/-- The `1024` constant functions `1` in one variable admit integers `p_λ`, not all zero, with
`|p_λ| ≤ e` and `∑ p_λ = 0`, by `TauCeti.exists_ne_zero_int_norm_sum_le`. -/
example : ∃ p : Fin 1024 → ℤ, p ≠ 0 ∧ (∀ l, |(p l : ℝ)| ≤ Real.exp 1) ∧ ∑ l, p l = 0 := by
  have hlog : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  have hR : (((Real.exp 2).toNNReal : ℝ)) = Real.exp 2 := Real.coe_toNNReal _ (Real.exp_pos 2).le
  have hW : 12 ≤ 1 + Real.log 1024 + 6 := by rw [hlog]; linarith
  obtain ⟨p, hp0, hpN, hpz⟩ := exists_ne_zero_int_norm_sum_le (ι := Fin 1) (Λ := Fin 1024)
    (φ := fun _ _ ↦ 1) (P := fun _ ↦ constFormalMultilinearSeries ℂ (Fin 1 → ℂ) 1)
    (R := (Real.exp 2).toNNReal) (M := fun _ ↦ 1) (N := 1) (U := Real.log 1024) (V := 6) (r := 1)
    (fun _ ↦ hasFPowerSeriesOnBall_const.mono (by simp [Real.exp_pos]) le_top)
    (fun _ _ _ ↦ by simp)
    (by simp [Real.exp_log])
    hW
    (by rw [hR, div_one]; exact Real.exp_le_exp.2 one_le_two)
    (by rw [hR, div_one]; exact Real.exp_le_exp.2 (by linarith))
    (by
      have h28 : 2 * (1 + Real.log 1024 + 6) ≤ 28 := by rw [hlog]; linarith
      rw [hR, div_one, Real.log_exp]
      simp only [Fintype.card_fin]
      calc (2 * (1 + Real.log 1024 + 6)) ^ (1 + 1) ≤ 28 ^ (1 + 1) :=
            pow_le_pow_left₀ (by linarith) h28 _
        _ ≤ ((1024 : ℕ) : ℝ) * 1 * 2 ^ 1 := by norm_num)
  refine ⟨p, hp0, hpN, ?_⟩
  have h := hpz 0 (mem_closedBall_self zero_le_one)
  simp only [mul_one] at h
  have hlt : ‖((∑ l, p l : ℤ) : ℂ)‖ < 1 := by
    push_cast
    refine h.trans_lt ?_
    rw [Real.exp_lt_one_iff]
    norm_num
  rw [Complex.norm_intCast] at hlt
  exact_mod_cast Int.abs_lt_one_iff.1 (by exact_mod_cast hlt)

end TauCeti.AuxiliaryFunctionExample
