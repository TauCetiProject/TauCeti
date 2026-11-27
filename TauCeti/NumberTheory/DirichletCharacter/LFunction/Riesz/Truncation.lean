/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Increment

/-!
# Truncating the logarithmic derivative at one

A finite difference of the compensated first Riesz sum controls the approximation of
`L′/L(1, χ)` by a sharp von Mangoldt sum with weight `χ(n)/n`. Only prime powers between
the two cutoffs contribute to the smoothing error. This is the finite-difference step of
L. Alpöge's zero-free-box argument in his formalization of the Riemann hypothesis for
Dirichlet L-functions (https://github.com/leanprover-community/riemann-hypothesis).
-/

public section

open ArithmeticFunction Finset Real TauCeti

namespace DirichletCharacter

/-- A bound `B` on a compensated Riesz increment over `(z,y]` bounds the error in truncating
`L′/L(1, χ)` at `z`. The additional error is due to the integers in `(z,y]`. This estimate is
algebraic and also holds with the totalized logarithmic derivative for the principal character. -/
theorem norm_logDeriv_add_sum_vonMangoldt_div_le_of_riesz_increment {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {z y B : ℝ} (hz : 0 < z) (hzy : z < y) (hy : 1 ≤ y)
    (hinc : ‖rieszSum (fun n ↦ χ n * Λ n) y - rieszSum (fun n ↦ χ n * Λ n) z +
      ((y - z : ℝ) : ℂ) * logDeriv χ.LFunction 1‖ ≤ B) :
    ‖logDeriv χ.LFunction 1 + ∑ n ∈ Icc 1 ⌊z⌋₊, χ n * Λ n / (n : ℂ)‖ ≤
      B / (y - z) + (y - z + 1) * (log y / z) := by
  let a : ℕ → ℂ := fun n ↦ χ n * Λ n
  let d := logDeriv χ.LFunction 1
  let R := rieszSum a y - rieszSum a z
  let S := ∑ n ∈ Icc 1 ⌊z⌋₊, a n / (n : ℂ)
  have hs : 0 < y - z := sub_pos.mpr hzy
  have hs₀ : ((y - z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hshort := norm_rieszSum_sub_div_sub_sum_div_le a hz hzy (M := log y) (fun n hn ↦ by
    have hnz := (mem_Ioc.mp hn).1
    have hn₀ : 0 < n := by omega
    have hny := (Nat.le_floor_iff' hn₀.ne').mp (mem_Ioc.mp hn).2
    exact (χ.norm_mul_vonMangoldt_le n).trans
      (vonMangoldt_le_log.trans (log_le_log (Nat.cast_pos.mpr hn₀) hny)))
  have hcard : ((Ioc ⌊z⌋₊ ⌊y⌋₊).card : ℝ) ≤ y - z + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_le_floor hzy.le)]
    linarith [Nat.floor_le (hz.trans hzy).le, Nat.lt_floor_add_one z]
  have hsplit : d + S = (R + ((y - z : ℝ) : ℂ) * d) / ((y - z : ℝ) : ℂ) -
      (R / ((y - z : ℝ) : ℂ) - S) := by
    rw [add_div, mul_div_cancel_left₀ _ hs₀]
    ring
  calc
    ‖d + S‖ ≤ ‖(R + ((y - z : ℝ) : ℂ) * d) / ((y - z : ℝ) : ℂ)‖ +
        ‖R / ((y - z : ℝ) : ℂ) - S‖ := hsplit ▸ norm_sub_le _ _
    _ ≤ B / (y - z) + (y - z + 1) * (log y / z) := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le]
      exact add_le_add (div_le_div_of_nonneg_right hinc hs.le)
        (hshort.trans (mul_le_mul_of_nonneg_right hcard
          (div_nonneg (log_nonneg hy) hz.le)))

private theorem rpow_box_error_div_le {x Q r σ K : ℝ} (hx : 1 ≤ x)
    (hQ : x ^ r * x ^ (3 : ℝ) ≤ Q) (hlogQ : 1 ≤ log Q) (hK : 0 ≤ K)
    (hσ : -1 ≤ r * (σ - 1)) :
    let z := x ^ r; let η := x ^ (-2 : ℝ)
    K * log Q * (η * z ^ σ * log Q + z ^ 2 / Q) / (z * η) ≤
      2 * K * x ^ (r * (σ - 1)) * (log Q) ^ 2 := by
  intro z η
  have hx₀ := zero_lt_one.trans_le hx
  have hz : 0 < z := rpow_pos_of_pos hx₀ _
  have hη : 0 < η := rpow_pos_of_pos hx₀ _
  have hQ₀ : 0 < Q := (mul_pos hz (rpow_pos_of_pos hx₀ _)).trans_le hQ
  have hpow : z ^ σ / z = x ^ (r * (σ - 1)) := by
    rw [← rpow_mul hx₀.le, mul_sub, mul_one, rpow_sub hx₀, rpow_mul hx₀.le]
  have htail : (z ^ 2 / Q) / (z * η) ≤ x ^ (-1 : ℝ) := calc
    _ ≤ (z ^ 2 / (z * x ^ (3 : ℝ))) / (z * η) := by gcongr
    _ = 1 / (x ^ (3 : ℝ) * η) := by
      field_simp [hz.ne', hη.ne', (rpow_pos_of_pos hx₀ 3).ne']
    _ = x ^ (-1 : ℝ) := by
      apply (div_eq_iff (mul_ne_zero (rpow_pos_of_pos hx₀ 3).ne' hη.ne')).mpr
      rw [mul_comm, ← rpow_add hx₀, ← rpow_add hx₀]
      norm_num
  have htail' : (z ^ 2 / Q) / (z * η) ≤ x ^ (r * (σ - 1)) * log Q :=
    htail.trans ((rpow_le_rpow_of_exponent_le hx hσ).trans
      (le_mul_of_one_le_right (by positivity) hlogQ))
  calc
    _ = K * log Q * (z ^ σ / z * log Q + (z ^ 2 / Q) / (z * η)) := by
      field_simp [hz.ne', hη.ne', hQ₀.ne']
    _ ≤ _ := by
      rw [hpow]
      calc
        _ ≤ K * log Q * (x ^ (r * (σ - 1)) * log Q + x ^ (r * (σ - 1)) * log Q) := by
          gcongr
        _ = _ := by ring

private theorem rpow_smoothing_error_le {x Q r e : ℝ} (hx : 2 ≤ x) (hr : 1 ≤ r)
    (he : -1 ≤ e) (hQ : x ^ r * x ^ (3 : ℝ) ≤ Q) (hlogQ : 1 ≤ log Q) :
    let z := x ^ r; let η := x ^ (-2 : ℝ)
    (z * η + 1) * (log (z * (1 + η)) / z) ≤ 2 * x ^ e * (log Q) ^ 2 := by
  intro z η
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hz : 0 < z := rpow_pos_of_pos hx₀ _
  have hη : 0 < η := rpow_pos_of_pos hx₀ _
  have hlog : log (z * (1 + η)) ≤ log Q := by
    apply log_le_log (by positivity)
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hz.le) hQ
    calc
      1 + η ≤ 2 := by linarith [rpow_le_one_of_one_le_of_nonpos hx₁ (by norm_num : (-2 : ℝ) ≤ 0)]
      _ ≤ x ^ (3 : ℝ) := by
        refine hx.trans ?_
        simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hx₁ (by norm_num : (1 : ℝ) ≤ 3)
  have hηe : η ≤ x ^ e := rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  have hze : 1 / z ≤ x ^ e := by
    rw [one_div, ← rpow_neg hx₀.le]
    exact rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  calc
    _ = (η + 1 / z) * log (z * (1 + η)) := by field_simp [hz.ne']
    _ ≤ (2 * x ^ e) * log Q := by
      refine (mul_le_mul_of_nonneg_left hlog (add_nonneg hη.le (one_div_nonneg.mpr hz.le))).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith

/-- With `z = x^(1/δ₀)` and relative width `η = x⁻²`, the smoothed zero-free-box increment
bound gives a sharp truncation error of at most `(2K + 2) x^(-1 + δ/δ₀) (log Q)²`. This
separates the finite-difference argument from the contour estimate supplying the increment. -/
theorem norm_logDeriv_add_sum_vonMangoldt_div_le_at_rpow {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x Q δ₀ δ K : ℝ} (hx : 2 ≤ x) (hδ₀ : 0 < δ₀)
    (hδ₀' : δ₀ ≤ 1) (hδ : 0 ≤ δ) (hQ : x ^ (1 / δ₀ + 3) ≤ Q)
    (hinc : let z := x ^ (1 / δ₀); let η := x ^ (-2 : ℝ)
      ‖rieszSum (fun n ↦ χ n * Λ n) (z * (1 + η)) - rieszSum (fun n ↦ χ n * Λ n) z +
        ((z * η : ℝ) : ℂ) * logDeriv χ.LFunction 1‖ ≤
        K * log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q)) :
    ‖logDeriv χ.LFunction 1 + ∑ n ∈ Icc 1 ⌊x ^ (1 / δ₀)⌋₊, χ n * Λ n / (n : ℂ)‖ ≤
      (2 * K + 2) * x ^ (-1 + δ / δ₀) * (log Q) ^ 2 := by
  let z := x ^ (1 / δ₀)
  let η := x ^ (-2 : ℝ)
  have hx₀ : 0 < x := by linarith
  have hx₁ : 1 ≤ x := by linarith
  have hr : 1 ≤ 1 / δ₀ := (le_div_iff₀ hδ₀).mpr (by simpa using hδ₀')
  have hz : 1 ≤ z := one_le_rpow hx₁ (by positivity)
  have hη : 0 < η := rpow_pos_of_pos hx₀ _
  have hQ' : z * x ^ (3 : ℝ) ≤ Q := by rwa [← rpow_add hx₀]
  have hlogQ : 1 ≤ log Q := by
    have hh : (2 : ℝ) ^ (3 : ℝ) ≤ z * x ^ (3 : ℝ) := by
      calc
        _ ≤ x ^ (3 : ℝ) := rpow_le_rpow (by norm_num) hx (by norm_num)
        _ ≤ _ := le_mul_of_one_le_left (by positivity) hz
    have := log_le_log (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) (hh.trans hQ')
    rw [log_rpow (by norm_num : (0 : ℝ) < 2)] at this
    linarith [log_two_gt_d9]
  have hy : z < z * (1 + η) := by nlinarith
  have hstep : z * (1 + η) - z = z * η := by ring
  have h := χ.norm_logDeriv_add_sum_vonMangoldt_div_le_of_riesz_increment
    (zero_lt_one.trans_le hz) hy (hz.trans hy.le) (by simpa only [hstep] using hinc)
  rw [hstep] at h
  apply h.trans
  have hK : 0 ≤ K := by
    have hpos : 0 < log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q) := by
      have hQ₀ : 0 < Q := (mul_pos (zero_lt_one.trans_le hz) (rpow_pos_of_pos hx₀ _)).trans_le hQ'
      positivity
    have hn : 0 ≤ K * (log Q * (η * z ^ (1 - δ₀ + δ) * log Q + z ^ 2 / Q)) := by
      rw [← mul_assoc]
      exact (norm_nonneg _).trans hinc
    exact nonneg_of_mul_nonneg_right (mul_comm K _ ▸ hn) hpos
  have hexp : (1 / δ₀) * ((1 - δ₀ + δ) - 1) = -1 + δ / δ₀ := by
    field_simp [hδ₀.ne']
    ring
  have he : -1 ≤ -1 + δ / δ₀ := by linarith [div_nonneg hδ hδ₀.le]
  have hbox := rpow_box_error_div_le (σ := 1 - δ₀ + δ) hx₁ hQ' hlogQ hK (hexp ▸ he)
  rw [hexp] at hbox
  calc
    _ ≤ 2 * K * x ^ (-1 + δ / δ₀) * (log Q) ^ 2 + 2 * x ^ (-1 + δ / δ₀) * (log Q) ^ 2 :=
      add_le_add hbox (rpow_smoothing_error_le hx hr he hQ' hlogQ)
    _ = _ := by ring

end DirichletCharacter
