/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Numerical bounds for repeated certificate trials

These lemmas connect the failure product `(1 - q)^r` to a precision
parameter. They do not assume or prove independence of random trials.
-/

@[expose] public section

namespace TauCeti

/-- The independent-trial failure product has the usual exponential bound. -/
theorem failure_pow_le_exp {q : ℝ} (hq : q ≤ 1) (r : ℕ) :
    (1 - q) ^ r ≤ Real.exp (-q * (r : ℝ)) := by
  calc
    (1 - q) ^ r ≤ Real.exp (-q) ^ r :=
      pow_le_pow_left₀ (sub_nonneg.mpr hq) (Real.one_sub_le_exp_neg q) r
    _ = Real.exp (-q * (r : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Total success budget at least `k` gives failure probability at most `2⁻ᵏ`. -/
theorem failure_pow_le_half_pow {q : ℝ} (hq : q ≤ 1) (r k : ℕ)
    (hbudget : (k : ℝ) ≤ q * (r : ℝ)) :
    (1 - q) ^ r ≤ (1 / 2 : ℝ) ^ k := by
  have hhalf : Real.exp (-1 : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp (1 : ℝ)]
    simpa only [one_div] using
      (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr htwo
  calc
    (1 - q) ^ r ≤ Real.exp (-q * (r : ℝ)) := failure_pow_le_exp hq r
    _ ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-1 : ℝ) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ (1 / 2 : ℝ) ^ k := pow_le_pow_left₀ (Real.exp_pos _).le hhalf k

/-- A lower bound `q ≥ 1/R` is amplified with `k * R` trials. -/
theorem failure_pow_mul_le_half_pow {q : ℝ} (hq : q ≤ 1) (R k : ℕ)
    (hR : 0 < R) (hqR : 1 / (R : ℝ) ≤ q) :
    (1 - q) ^ (k * R) ≤ (1 / 2 : ℝ) ^ k := by
  apply failure_pow_le_half_pow hq (k * R) k
  have hR' : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hqR' : 1 ≤ q * (R : ℝ) := (div_le_iff₀ hR').mp hqR
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := mul_le_mul_of_nonneg_left hqR' hk
  push_cast
  nlinarith


end TauCeti
