/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic
public import TauCeti.Analysis.SpecialFunctions.Gamma.ReciprocalGrowth
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Basic

/-!
# The order of the reciprocal gamma factors

The reciprocals `1/Γ`, `1/Γ_ℝ` and `1/Γ_ℂ` are entire of order exactly one, and so the analytic
reciprocal `invGammaFactor d` of the gamma factor of an analytic L-function record has order at
most one. The upper bounds are the explicit estimates
`‖Γ(s)⁻¹‖ ≤ exp (C (1 + ‖s‖) log (2 + ‖s‖))` of
`TauCeti.Analysis.SpecialFunctions.Gamma.ReciprocalGrowth`.

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
* `TauCeti.LFunctions.AnalyticLFunctionData.orderLE_invGammaFactor`: the analytic reciprocal of
  the gamma factor of every record has order at most one.
* `TauCeti.LFunctions.orderLE_invGammaFactor_riemannZetaData_iff`: for the `ζ` record the
  order is exactly one.

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
    rw [this, Real.sin_neg, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi, abs_neg, abs_pow,
      abs_neg, abs_one, one_pow]
  have hpos : 0 < Real.Gamma (n + 3 / 2) := Real.Gamma_pos_of_pos (by positivity)
  have h1 : (1 : ℝ) - (-n - 1 / 2) = n + 3 / 2 := by ring
  rw [h1] at hrefl
  have habs := congrArg abs hrefl
  rw [abs_mul, abs_div, hsin, abs_of_pos hpos, abs_of_pos Real.pi_pos, div_one] at habs
  have hcast : (-(n : ℂ) - 1 / 2) = ((-n - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Gamma_ofReal, norm_inv, Complex.norm_real, Real.norm_eq_abs, ← habs]
  field_simp [hpos.ne']

/-- `n! ≤ Γ(n + 3/2)` for `n ≥ 1`, by monotonicity of `Γ` on `[2, ∞)`. -/
private theorem factorial_le_Gamma_add_three_halves {n : ℕ} (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ Real.Gamma (n + 3 / 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.Gamma_nat_eq_factorial]
  exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith) (by simp; linarith)
    (by linarith)

/-- `n! ≤ π ‖Γ(-n - 1/2)⁻¹‖` for `n ≥ 1`. -/
private theorem factorial_le_norm_inv_Gamma {n : ℕ} (hn : 1 ≤ n) :
    (n ! : ℝ) ≤ π * ‖(Gamma (-n - 1 / 2))⁻¹‖ := by
  rw [norm_inv_Gamma_neg_nat_sub_half, mul_div_cancel₀ _ Real.pi_ne_zero]
  exact factorial_le_Gamma_add_three_halves hn

/-- If `f` is at least `n! / (L K ^ n)` along points `z n → ∞` with `‖z n‖ ≤ a n + b`, then `f`
is not `O(exp (C ‖s‖))` for any `C`, since `n!` outgrows every geometric sequence. -/
private theorem not_isBigO_exp_mul_norm_of_factorial_le {f : ℂ → ℂ} {z : ℕ → ℂ} {a b K L : ℝ}
    (hz : Tendsto z atTop (cobounded ℂ)) (hnorm : ∀ n, ‖z n‖ ≤ a * n + b) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hf : ∀ n, 1 ≤ n → (n ! : ℝ) ≤ L * K ^ n * ‖f (z n)‖) (C : ℝ) :
    ¬ f =O[cobounded ℂ] fun s ↦ Real.exp (C * ‖s‖) := by
  intro h
  obtain ⟨c, hc0, hc⟩ := h.exists_pos
  set M := K * Real.exp (|C| * a)
  set D := L * c * Real.exp (|C| * b)
  have hlim : Tendsto (fun n : ℕ ↦ D * (M ^ n / n !)) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop M).const_mul D
  obtain ⟨n, hn1, hlt, hle⟩ := ((eventually_ge_atTop 1).and
    ((hlim.eventually (gt_mem_nhds one_pos)).and (hz.eventually hc.bound))).exists
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hle
  have hexp : Real.exp (C * ‖z n‖) ≤ Real.exp (|C| * b) * Real.exp (|C| * a) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    calc C * ‖z n‖ ≤ |C| * ‖z n‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ ≤ |C| * (a * n + b) := mul_le_mul_of_nonneg_left (hnorm n) (abs_nonneg C)
      _ = |C| * b + n * (|C| * a) := by ring
  have hfac : (n ! : ℝ) ≤ D * M ^ n :=
    calc (n ! : ℝ) ≤ L * K ^ n * ‖f (z n)‖ := hf n hn1
      _ ≤ L * K ^ n * (c * (Real.exp (|C| * b) * Real.exp (|C| * a) ^ n)) := by
        gcongr
        exact hle.trans (mul_le_mul_of_nonneg_left hexp hc0.le)
      _ = D * M ^ n := by simp only [D, M, mul_pow]; ring
  have hpos : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [← mul_div_assoc, div_lt_one hpos] at hlt
  linarith

/-- An order bound below one rules out a function that is not of exponential type. -/
private theorem one_le_of_orderLE_of_not_isBigO {f : ℂ → ℂ} {A : ℝ} (hf : OrderLE f A)
    (h : ¬ f =O[cobounded ℂ] fun s ↦ Real.exp (1 * ‖s‖)) : 1 ≤ A := by
  by_contra! hA
  exact h (by simpa using hf.isBigO hA)

/-- The points `-n - 1/2` tend to infinity. -/
private theorem tendsto_neg_nat_sub_half :
    Tendsto (fun n : ℕ ↦ -(n : ℂ) - 1 / 2) atTop (cobounded ℂ) := by
  refine tendsto_norm_atTop_iff_cobounded.1 ?_
  refine tendsto_atTop_mono (fun n : ℕ ↦ ?_) (tendsto_natCast_atTop_atTop.atTop_add
    (tendsto_const_nhds (x := (-1 / 2 : ℝ))))
  calc (n : ℝ) + -1 / 2 = ‖-(n : ℂ)‖ - ‖(1 / 2 : ℂ)‖ := by simp; ring
    _ ≤ ‖-(n : ℂ) - 1 / 2‖ := norm_sub_norm_le _ _

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
  ⟨fun h ↦ one_le_of_orderLE_of_not_isBigO h (not_isBigO_inv_Gamma_exp_mul_norm 1),
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
    have hpow : ‖(π : ℂ) ^ (-(2 * (-(n : ℂ) - 1 / 2)) / 2)‖ = π ^ ((n : ℝ) + 1 / 2) := by
      rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      congr 1
      simp
      ring
    rw [Gammaℝ_def, hhalf, mul_inv, norm_mul, norm_inv, hpow,
      Real.rpow_add Real.pi_pos, Real.rpow_natCast]
    have h := factorial_le_norm_inv_Gamma hn
    have hp : 0 < π ^ (1 / 2 : ℝ) := by positivity
    have hpn : 0 < π ^ n := by positivity
    calc (n ! : ℝ) ≤ π * ‖(Gamma (-n - 1 / 2))⁻¹‖ := h
      _ = π * π ^ (1 / 2 : ℝ) * π ^ n * ((π ^ n * π ^ (1 / 2 : ℝ))⁻¹ *
          ‖(Gamma (-n - 1 / 2))⁻¹‖) := by field_simp
      _ = _ := rfl

/-- `1/Γ_ℝ` has order at most `A` exactly when `1 ≤ A`. -/
@[simp]
theorem orderLE_inv_Gammaℝ_iff {A : ℝ} : OrderLE (fun s ↦ (Gammaℝ s)⁻¹) A ↔ 1 ≤ A :=
  ⟨fun h ↦ one_le_of_orderLE_of_not_isBigO h (not_isBigO_inv_Gammaℝ_exp_mul_norm 1),
    orderLE_inv_Gammaℝ.mono⟩

/-- `1/Γ_ℂ` is not of exponential type, by its values at `-n - 1/2`. -/
theorem not_isBigO_inv_Gammaℂ_exp_mul_norm (C : ℝ) :
    ¬ (fun s ↦ (Gammaℂ s)⁻¹) =O[cobounded ℂ] fun s ↦ Real.exp (C * ‖s‖) := by
  refine not_isBigO_exp_mul_norm_of_factorial_le tendsto_neg_nat_sub_half
    norm_neg_nat_sub_half_le (K := 2 * π) (L := 2 * (2 * π) ^ (1 / 2 : ℝ) * π) (by positivity)
    (by positivity) (fun n hn ↦ ?_) C
  have hpow : ‖((2 * π : ℝ) : ℂ) ^ (-(-(n : ℂ) - 1 / 2))‖ = (2 * π) ^ ((n : ℝ) + 1 / 2) := by
    rw [norm_cpow_eq_rpow_re_of_pos (by positivity)]
    congr 1
    simp
    ring
  have h2π : ((2 * π : ℝ) : ℂ) = 2 * π := by push_cast; ring
  rw [Gammaℂ_def, ← h2π, mul_inv, mul_inv, norm_mul, norm_mul, norm_inv, norm_inv, hpow,
    Complex.norm_two, Real.rpow_add (by positivity), Real.rpow_natCast]
  have h := factorial_le_norm_inv_Gamma hn
  have hp : 0 < (2 * π) ^ (1 / 2 : ℝ) := by positivity
  have hpn : 0 < (2 * π) ^ n := by positivity
  calc (n ! : ℝ) ≤ π * ‖(Gamma (-n - 1 / 2))⁻¹‖ := h
    _ = 2 * (2 * π) ^ (1 / 2 : ℝ) * π * (2 * π) ^ n * (2⁻¹ * ((2 * π) ^ n *
        (2 * π) ^ (1 / 2 : ℝ))⁻¹ * ‖(Gamma (-n - 1 / 2))⁻¹‖) := by field_simp
    _ = _ := rfl

/-- `1/Γ_ℂ` has order at most `A` exactly when `1 ≤ A`. -/
@[simp]
theorem orderLE_inv_Gammaℂ_iff {A : ℝ} : OrderLE (fun s ↦ (Gammaℂ s)⁻¹) A ↔ 1 ≤ A :=
  ⟨fun h ↦ one_le_of_orderLE_of_not_isBigO h (not_isBigO_inv_Gammaℂ_exp_mul_norm 1),
    orderLE_inv_Gammaℂ.mono⟩

/-! ### The analytic reciprocal of a record's gamma factor -/

namespace LFunctions

namespace AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- The analytic reciprocal of the gamma factor of a record has order at most one. -/
theorem orderLE_invGammaFactor : OrderLE d.invGammaFactor 1 := by
  rw [funext d.invGammaFactor_eq_prod]
  refine (OrderLE.multisetProd fun μ _ ↦ ?_).mul (OrderLE.multisetProd fun ν _ ↦ ?_)
  · simpa using orderLE_inv_Gammaℝ.comp_mul_add 1 μ
  · simpa using orderLE_inv_Gammaℂ.comp_mul_add 1 ν

end AnalyticLFunctionData

/-- The analytic reciprocal of the gamma factor of the `ζ` record is `1/Γ_ℝ`. -/
theorem riemannZetaData_invGammaFactor :
    riemannZetaData.invGammaFactor = fun s ↦ (Gammaℝ s)⁻¹ :=
  funext fun s ↦ by
    rw [AnalyticLFunctionData.invGammaFactor_def, riemannZetaData_gammaFactor]

/-- For the `ζ` record the analytic reciprocal of the gamma factor has order exactly one: order
at most `A` holds exactly when `1 ≤ A`. -/
theorem orderLE_invGammaFactor_riemannZetaData_iff {A : ℝ} :
    OrderLE riemannZetaData.invGammaFactor A ↔ 1 ≤ A := by
  rw [riemannZetaData_invGammaFactor, orderLE_inv_Gammaℝ_iff]

end LFunctions

end TauCeti
