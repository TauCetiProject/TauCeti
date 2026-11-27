/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.FiniteDifference

/-!
# Truncation of a Dirichlet logarithmic derivative at one

An estimate for the increment of the first Riesz sum, corrected by the linear main term,
controls the error in truncating `−L′/L` at one. The discrete error involves only the newly
included integers. This permits taking a short forward difference while retaining a power saving
from a zero-free-box estimate. The input estimate has the normalization used in Levent Alpöge's
[formalization of GRH](https://github.com/leanprover-community/riemann-hypothesis).
-/

public section

open Finset Real TauCeti
open scoped ArithmeticFunction.vonMangoldt

namespace DirichletCharacter

/-- A bound on a corrected Riesz increment gives a bound on the truncation error at one.
Besides the bound divided by the step length, only the contribution of the new terms enters. -/
theorem norm_logDeriv_one_add_sum_le_of_riesz_increment {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {z y B : ℝ} (hz : 0 < z) (hzy : z < y)
    (hB : ‖rieszSum (fun n ↦ χ n * (Λ n : ℂ)) y - rieszSum (fun n ↦ χ n * (Λ n : ℂ)) z +
      ((y - z : ℝ) : ℂ) * logDeriv χ.LFunction 1‖ ≤ B) :
    ‖logDeriv χ.LFunction 1 + ∑ n ∈ Icc 1 ⌊z⌋₊, χ n * (Λ n : ℂ) / n‖ ≤
      B / (y - z) + (y - z + 1) * log (max y 1) / z := by
  let a : ℕ → ℂ := fun n ↦ χ n * (Λ n : ℂ)
  let S := ∑ n ∈ Icc 1 ⌊z⌋₊, a n / n
  let h : ℝ := y - z
  have hh : 0 < h := sub_pos.mpr hzy
  have hmass : (∑ n ∈ Ioc ⌊z⌋₊ ⌊y⌋₊, ‖a n‖ / n) ≤ (h + 1) * log (max y 1) / z := by
    have hcard : ((Ioc ⌊z⌋₊ ⌊y⌋₊).card : ℝ) ≤ h + 1 := by
      rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_le_floor hzy.le)]
      linarith [Nat.floor_le (hz.trans hzy).le, Nat.lt_floor_add_one z]
    have hlog : 0 ≤ log (max y 1) := log_nonneg (le_max_right ..)
    calc
      _ ≤ ∑ _n ∈ Ioc ⌊z⌋₊ ⌊y⌋₊, log (max y 1) / z := by
        refine sum_le_sum fun n hn ↦ ?_
        obtain ⟨h₁, h₂⟩ := mem_Ioc.mp hn
        have hn₀ : 0 < n := (Nat.zero_le _).trans_lt h₁
        have hzn := (Nat.floor_lt' hn₀.ne').mp h₁
        have hny := (Nat.le_floor_iff' hn₀.ne').mp h₂
        apply div_le_div₀ hlog ?_ hz hzn.le
        exact (χ.norm_mul_vonMangoldt_le n).trans (ArithmeticFunction.vonMangoldt_le_log.trans
          (log_le_log (Nat.cast_pos.mpr hn₀) (hny.trans (le_max_left ..))))
      _ ≤ _ := by
        rw [sum_const, nsmul_eq_mul, mul_div_assoc]
        gcongr
  have heq : (h : ℂ) * (logDeriv χ.LFunction 1 + S) =
      (rieszSum a y - rieszSum a z + (h : ℂ) * logDeriv χ.LFunction 1) -
      (rieszSum a y - rieszSum a z - (h : ℂ) * S) := by ring
  have hnorm := (norm_sub_le _ _).trans (add_le_add hB
    ((norm_rieszSum_sub_sub_mul_sum_div_le a hzy.le).trans
      (mul_le_mul_of_nonneg_left hmass hh.le)))
  rw [← heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] at hnorm
  calc
    _ ≤ (B + h * ((h + 1) * log (max y 1) / z)) / h :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm _ h] using hnorm)
    _ = _ := by rw [add_div, mul_div_cancel_left₀ _ hh.ne']

-- Divide the analytic error by the chosen forward step, keeping the power saving.
private theorem riesz_box_error_div_step_le {x Q δ₀ δ K : ℝ} (hx : 1 ≤ x) (hδ₀ : 0 < δ₀)
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hQ : x ^ (1 / δ₀ + 3) ≤ Q) (hlog : 1 / 2 ≤ log Q) :
    let z := x ^ (1 / δ₀); let η := x ^ (-2 : ℝ)
    K * log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q) / (z * η) ≤
      3 * K * x ^ (-1 + δ / δ₀) * (log Q) ^ 2 := by
  intro z η
  let E := x ^ (-1 + δ / δ₀)
  have hx₀ := zero_lt_one.trans_le hx
  have hz : 0 < z := rpow_pos_of_pos hx₀ _
  have hη : 0 < η := rpow_pos_of_pos hx₀ _
  have hQ₀ : 0 < Q := (rpow_pos_of_pos hx₀ _).trans_le hQ
  have he : x ^ (-1 : ℝ) ≤ E :=
    rpow_le_rpow_of_exponent_le hx (le_add_of_nonneg_right (div_nonneg hδ hδ₀.le))
  have hratio : z / (Q * η) ≤ x ^ (-1 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hQ₀ hη)).mpr
    calc
      z = x ^ (-1 : ℝ) * (x ^ (1 / δ₀ + 3) * η) := by
        dsimp only [z, η]
        rw [← rpow_add hx₀, ← rpow_add hx₀]
        congr 1
        ring
      _ ≤ _ := by gcongr
  have hpow : z ^ (1 - δ₀ + δ) / z = E := by
    rw [← rpow_sub_one hz.ne']
    dsimp only [z, E]
    rw [← rpow_mul hx₀.le]
    congr 1
    field_simp
    ring
  calc
    _ = K * log Q * (E * log Q + z / (Q * η)) := by
      rw [← hpow]
      field_simp [hη.ne', hQ₀.ne', hz.ne']
    _ ≤ K * log Q * (E * log Q + E) := by gcongr; exact hratio.trans he
    _ ≤ _ := by
      calc
        K * log Q * (E * log Q + E) = K * log Q * (E * (log Q + 1)) := by ring
        _ ≤ K * log Q * (E * (3 * log Q)) := by gcongr; linarith
        _ = _ := by ring

-- The integers in the forward step contribute an error of size `(η + 1/z) log y`.
private theorem riesz_box_discrete_error_le {x Q δ₀ δ : ℝ} (hx : 2 ≤ x) (hxQ : x ≤ Q)
    (hδ₀ : 0 < δ₀) (hhalf : δ₀ ≤ 1 / 2) (hδ : 0 ≤ δ) (hlog : 1 / 2 ≤ log Q) :
    let r := 1 / δ₀; let z := x ^ r; let η := x ^ (-2 : ℝ)
    (z * η + 1) * log (z * (1 + η)) / z ≤ 4 * (r + 1) * x ^ (-1 + δ / δ₀) * (log Q) ^ 2 := by
  intro r z η
  let E := x ^ (-1 + δ / δ₀)
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := zero_lt_one.trans_le hx₁
  have hr : 2 ≤ r := (le_div_iff₀ hδ₀).mpr (by linarith)
  have hz : 0 < z := rpow_pos_of_pos hx₀ _
  have hη : 0 < η := rpow_pos_of_pos hx₀ _
  have hinv : z⁻¹ ≤ η := by
    dsimp only [z, η]
    rw [← rpow_neg hx₀.le]
    exact rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  have hηE : η ≤ E := rpow_le_rpow_of_exponent_le hx₁ (by
    linarith [div_nonneg hδ hδ₀.le])
  have hη₁ : η ≤ 1 := rpow_le_one_of_one_le_of_nonpos hx₁ (by norm_num)
  have hly : log (z * (1 + η)) ≤ (r + 1) * log Q := by
    rw [log_mul hz.ne' (by positivity : 1 + η ≠ 0), log_rpow hx₀]
    calc
      _ ≤ r * log x + log x := by gcongr; linarith
      _ = (r + 1) * log x := by ring
      _ ≤ _ := by gcongr
  have hy : 1 ≤ z * (1 + η) := one_le_mul_of_one_le_of_one_le
    (one_le_rpow hx₁ (by linarith)) (le_add_of_nonneg_right hη.le)
  calc
    _ = (η + z⁻¹) * log (z * (1 + η)) := by field_simp [hz.ne']
    _ ≤ (2 * E) * ((r + 1) * log Q) := by
      have := log_nonneg hy
      gcongr
      linarith
    _ ≤ (2 * E) * ((r + 1) * (2 * log Q * log Q)) := by
      gcongr ?_ * (?_ * ?_)
      nlinarith only [mul_nonneg (by linarith : 0 ≤ log Q) (by linarith : 0 ≤ 2 * log Q - 1)]
    _ = _ := by ring

/-- With cutoff `z = x^(1/δ₀)` and relative increment `x⁻²`, a corrected Riesz increment of
size `K log Q (η z^(1-δ₀+δ) log Q + z²/Q)` yields a truncation error of order
`x^(-1+δ/δ₀) (log Q)^2`. Only the estimate at this pair of cutoffs is needed. -/
theorem norm_logDeriv_one_add_sum_le_of_riesz_box_estimate {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {δ₀ δ x Q K : ℝ} (hδ₀ : 0 < δ₀) (hhalf : δ₀ ≤ 1 / 2)
    (hδ : 0 ≤ δ) (hx : 2 ≤ x) (hQ : x ^ (1 / δ₀ + 3) ≤ Q)
    (hR : let z := x ^ (1 / δ₀); let η := x ^ (-2 : ℝ)
      let a := fun n : ℕ ↦ χ n * (Λ n : ℂ)
      ‖rieszSum a (z * (1 + η)) - rieszSum a z + (z * η : ℝ) * logDeriv χ.LFunction 1‖ ≤
        K * log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q)) :
    ‖logDeriv χ.LFunction 1 + ∑ n ∈ Icc 1 ⌊x ^ (1 / δ₀)⌋₊, χ n * (Λ n : ℂ) / n‖ ≤
      (3 * K + 4 * (1 / δ₀ + 1)) * x ^ (-1 + δ / δ₀) * (log Q) ^ 2 := by
  let r := 1 / δ₀
  let z := x ^ r
  let η := x ^ (-2 : ℝ)
  let y := z * (1 + η)
  let B := K * log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q)
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  have hr : 2 ≤ r := (le_div_iff₀ hδ₀).mpr (by linarith)
  have hz : 1 ≤ z := one_le_rpow hx₁ (by linarith)
  have hη : 0 < η := rpow_pos_of_pos hx₀ _
  have hstep : y - z = z * η := by dsimp only [y]; ring
  have hh : 0 < z * η := mul_pos (by linarith) hη
  have hzy : z < y := sub_pos.mp (hstep ▸ hh)
  have hxQ : x ≤ Q := by
    refine le_trans ?_ hQ
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hx₁ (by linarith : 1 ≤ r + 3)
  have hQ₀ : 0 < Q := hx₀.trans_le hxQ
  have hz₀ : 0 < z := zero_lt_one.trans_le hz
  have hlog : 1 / 2 ≤ log Q := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 2) (hx.trans hxQ)
    linarith [one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hK : 0 ≤ K := by
    have hl : 0 < log Q := by linarith
    have hfac : 0 < log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q) :=
      mul_pos hl (add_pos_of_pos_of_nonneg (mul_pos (by positivity) hl) (by positivity))
    apply nonneg_of_mul_nonneg_left _ hfac
    rw [← mul_assoc]
    exact (norm_nonneg _).trans hR
  have happ := χ.norm_logDeriv_one_add_sum_le_of_riesz_increment hz₀ hzy
    (by simpa only [hstep] using hR : _ ≤ B)
  rw [hstep, max_eq_left (hz.trans hzy.le)] at happ
  exact happ.trans ((add_le_add (riesz_box_error_div_step_le hx₁ hδ₀ hδ hK hQ hlog)
    (riesz_box_discrete_error_le hx hxQ hδ₀ hhalf hδ hlog)).trans_eq (by ring))

end DirichletCharacter
