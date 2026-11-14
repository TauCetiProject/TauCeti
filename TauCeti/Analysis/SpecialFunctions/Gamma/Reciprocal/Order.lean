/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic
public import TauCeti.Analysis.SpecialFunctions.Gamma.Reciprocal.Growth

/-!
# The order of the reciprocal Gamma functions

The reciprocals `1/Γ`, `1/Γ_ℝ` and `1/Γ_ℂ` are entire of order exactly one. The upper bounds are
the explicit estimates `‖Γ(s)⁻¹‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))` of
`TauCeti.Analysis.SpecialFunctions.Gamma.Reciprocal.Growth`.

The order cannot be lowered, and `1/Γ` is not even of exponential type. Euler's reflection
formula gives `‖Γ(-n - 1/2)⁻¹‖ = Γ(n + 3/2)/π ≥ n!/π`, which beats every `exp (C n)`; at the
intervening points `-n` the reciprocal is `0`. The same half-integer points give the lower
bounds for `1/Γ_ℝ` (at `-2n - 1`) and for `1/Γ_ℂ` (at `-n - 1/2`).

## Main results

* `TauCeti.orderLE_inv_Gamma`, `TauCeti.orderLE_inv_Gammaℝ`, `TauCeti.orderLE_inv_Gammaℂ`:
  the three reciprocals have order at most one.
* `TauCeti.norm_inv_Gamma_neg_nat_sub_half`: `‖Γ(-n - 1/2)⁻¹‖ = Γ(n + 3/2)/π`.
* `TauCeti.not_isBigO_inv_Gamma_exp_mul_norm`: `1/Γ` is not `O(exp (C ‖s‖))` for any `C`, and
  likewise `TauCeti.not_isBigO_inv_Gammaℝ_exp_mul_norm` and
  `TauCeti.not_isBigO_inv_Gammaℂ_exp_mul_norm`.
* `TauCeti.orderLE_inv_Gamma_iff`, `TauCeti.orderLE_inv_Gammaℝ_iff`,
  `TauCeti.orderLE_inv_Gammaℂ_iff`: each reciprocal has order at most `A` exactly when `1 ≤ A`.

## References

* DLMF 5.5.3 (reflection) and 5.11.1 (Stirling).
* H. Davenport, *Multiplicative Number Theory*, §11.
-/

public section

open Complex Filter Asymptotics Bornology Topology Nat
open scoped Real

namespace TauCeti

/-! ### Upper bounds -/

/-- `1/Γ` has order at most one. -/
theorem orderLE_inv_Gamma : OrderLE (fun s ↦ (Gamma s)⁻¹) 1 :=
  orderLE_one_of_norm_le_exp_mul_log norm_inv_Gamma_le_exp_mul_log

/-- `1/Γ_ℝ` has order at most one. -/
theorem orderLE_inv_Gammaℝ : OrderLE (fun s ↦ (Gammaℝ s)⁻¹) 1 :=
  orderLE_one_of_norm_le_exp_mul_log norm_inv_Gammaℝ_le_exp_mul_log

/-- `1/Γ_ℂ` has order at most one. -/
theorem orderLE_inv_Gammaℂ : OrderLE (fun s ↦ (Gammaℂ s)⁻¹) 1 :=
  orderLE_one_of_norm_le_exp_mul_log norm_inv_Gammaℂ_le_exp_mul_log

/-! ### Lower bounds at the negative half-integers -/

/-- Euler's reflection formula at the negative half-integers:
`‖Γ(-n - 1/2)⁻¹‖ = Γ(n + 3/2)/π`. -/
theorem norm_inv_Gamma_neg_nat_sub_half (n : ℕ) :
    ‖(Gamma (-n - 1 / 2))⁻¹‖ = Real.Gamma (n + 3 / 2) / π := by
  have hrefl := Real.Gamma_mul_Gamma_one_sub (-n - 1 / 2)
  have hsin : |Real.sin (π * (-n - 1 / 2))| = 1 := by
    have : π * (-n - 1 / 2) = -((n : ℝ) * π + π / 2) := by ring
    simp only [this, Real.sin_neg, abs_neg, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi,
      abs_pow, abs_one, one_pow]
  have hpos : 0 < Real.Gamma (n + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h1 : (1 : ℝ) - (-n - 1 / 2) = n + 3 / 2 := by ring
  have habs : |Real.Gamma (-n - 1 / 2)| * Real.Gamma (n + 3 / 2) = π := by
    have h := congrArg abs hrefl
    simp only [h1, abs_mul, abs_div, hsin, abs_of_pos hpos, abs_of_pos Real.pi_pos, div_one] at h
    exact h
  have hcast : (-(n : ℂ) - 1 / 2) = ((-n - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Gamma_ofReal, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← habs]
  field_simp [hpos.ne']

/-- `n! ≤ Γ(n + 3/2)` for `n ≥ 1`, by monotonicity of `Γ` on `[2, ∞)`. -/
private theorem factorial_le_Gamma_add_three_halves {n : ℕ} (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ Real.Gamma (n + 3 / 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.Gamma_nat_eq_factorial]
  exact Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.2 (by linarith))
    (Set.mem_Ici.2 (by linarith)) (by linarith)

/-- `n! ≤ π ‖Γ(-n - 1/2)⁻¹‖` for `n ≥ 1`. -/
private theorem factorial_le_norm_inv_Gamma {n : ℕ} (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ π * ‖(Gamma (-n - 1 / 2))⁻¹‖ := by
  rw [norm_inv_Gamma_neg_nat_sub_half, mul_div_cancel₀ _ Real.pi_ne_zero]
  exact factorial_le_Gamma_add_three_halves hn

/-- The points `-n - 1/2` tend to infinity. -/
private theorem tendsto_neg_nat_sub_half :
    Tendsto (fun n : ℕ ↦ -(n : ℂ) - 1 / 2) atTop (cobounded ℂ) :=
  (tendsto_sub_const_cobounded _).comp (tendsto_neg_cobounded.comp tendsto_natCast_atTop_cobounded)

/-- `‖-n - 1/2‖ ≤ n + 1/2`. -/
private theorem norm_neg_nat_sub_half_le (n : ℕ) : ‖-(n : ℂ) - 1 / 2‖ ≤ 1 * n + 1 / 2 := by
  calc ‖-(n : ℂ) - 1 / 2‖ ≤ ‖-(n : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
    _ = 1 * n + 1 / 2 := by simp

/-- `1/Γ` is not of exponential type: it is not `O(exp (C ‖s‖))` for any `C`. -/
theorem not_isBigO_inv_Gamma_exp_mul_norm (C : ℝ) :
    ¬ (fun s ↦ (Gamma s)⁻¹) =O[cobounded ℂ] fun s ↦ Real.exp (C * ‖s‖) :=
  not_isBigO_exp_mul_norm_of_factorial_le tendsto_neg_nat_sub_half norm_neg_nat_sub_half_le
    zero_le_one Real.pi_pos.le (fun n hn ↦ by simpa using factorial_le_norm_inv_Gamma hn) C

/-- `1/Γ` has order at most `A` exactly when `1 ≤ A`. -/
@[simp]
theorem orderLE_inv_Gamma_iff {A : ℝ} : OrderLE (fun s ↦ (Gamma s)⁻¹) A ↔ 1 ≤ A :=
  ⟨fun h ↦ h.one_le_of_not_isBigO_exp
    (by simpa using not_isBigO_inv_Gamma_exp_mul_norm 1),
    orderLE_inv_Gamma.mono⟩

/-- `1/Γ_ℝ` is not of exponential type, by its values at `-2n - 1`. -/
theorem not_isBigO_inv_Gammaℝ_exp_mul_norm (C : ℝ) :
    ¬ (fun s ↦ (Gammaℝ s)⁻¹) =O[cobounded ℂ] fun s ↦ Real.exp (C * ‖s‖) := by
  have hz : Tendsto (fun n : ℕ ↦ 2 * (-(n : ℂ) - 1 / 2)) atTop (cobounded ℂ) :=
    (tendsto_mul_left_cobounded two_ne_zero).comp tendsto_neg_nat_sub_half
  refine not_isBigO_exp_mul_norm_of_factorial_le hz (a := 2) (b := 1) (K := π)
    (L := π * π ^ (1 / 2 : ℝ)) (fun n ↦ ?_) Real.pi_pos.le (by positivity) (fun n hn ↦ ?_) C
  · rw [norm_mul, Complex.norm_two]
    linarith [norm_neg_nat_sub_half_le n]
  · have hhalf : 2 * (-(n : ℂ) - 1 / 2) / 2 = -(n : ℂ) - 1 / 2 := by ring
    have hexp : -(2 * (-(n : ℂ) - 1 / 2)) / 2 = ((n + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    have hpow : ‖(π : ℂ) ^ (-(2 * (-(n : ℂ) - 1 / 2)) / 2)‖ = π ^ n * π ^ (1 / 2 : ℝ) := by
      rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, hexp, ofReal_re, Real.rpow_add Real.pi_pos,
        Real.rpow_natCast]
    simp only [Gammaℝ_def, hhalf, mul_inv, norm_mul, norm_inv, hpow]
    exact (factorial_le_norm_inv_Gamma hn).trans_eq (by rw [norm_inv]; field_simp)

/-- `1/Γ_ℝ` has order at most `A` exactly when `1 ≤ A`. -/
@[simp]
theorem orderLE_inv_Gammaℝ_iff {A : ℝ} : OrderLE (fun s ↦ (Gammaℝ s)⁻¹) A ↔ 1 ≤ A :=
  ⟨fun h ↦ h.one_le_of_not_isBigO_exp
    (by simpa using not_isBigO_inv_Gammaℝ_exp_mul_norm 1),
    orderLE_inv_Gammaℝ.mono⟩

/-- `1/Γ_ℂ` is not of exponential type, by its values at `-n - 1/2`. -/
theorem not_isBigO_inv_Gammaℂ_exp_mul_norm (C : ℝ) :
    ¬ (fun s ↦ (Gammaℂ s)⁻¹) =O[cobounded ℂ] fun s ↦ Real.exp (C * ‖s‖) := by
  refine not_isBigO_exp_mul_norm_of_factorial_le tendsto_neg_nat_sub_half
    norm_neg_nat_sub_half_le (K := 2 * π) (L := 2 * (2 * π) ^ (1 / 2 : ℝ) * π) (by positivity)
    (by positivity) (fun n hn ↦ ?_) C
  have h2π : 0 < 2 * π := by positivity
  have hexp : -(-(n : ℂ) - 1 / 2) = ((n + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have hpow : ‖(2 * (π : ℂ)) ^ (-(-(n : ℂ) - 1 / 2))‖ = (2 * π) ^ n * (2 * π) ^ (1 / 2 : ℝ) := by
    have hc : 2 * (π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [hc, norm_cpow_eq_rpow_re_of_pos h2π, hexp, ofReal_re,
      Real.rpow_add h2π, Real.rpow_natCast]
  simp only [Gammaℂ_def, mul_inv, norm_mul, norm_inv, hpow, Complex.norm_two]
  exact (factorial_le_norm_inv_Gamma hn).trans_eq (by rw [norm_inv]; field_simp)

/-- `1/Γ_ℂ` has order at most `A` exactly when `1 ≤ A`. -/
@[simp]
theorem orderLE_inv_Gammaℂ_iff {A : ℝ} : OrderLE (fun s ↦ (Gammaℂ s)⁻¹) A ↔ 1 ≤ A :=
  ⟨fun h ↦ h.one_le_of_not_isBigO_exp
    (by simpa using not_isBigO_inv_Gammaℂ_exp_mul_norm 1),
    orderLE_inv_Gammaℂ.mono⟩

end TauCeti
