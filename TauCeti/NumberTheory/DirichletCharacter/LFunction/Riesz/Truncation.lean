/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.FiniteDifference
import TauCeti.NumberTheory.DirichletCharacter.LFunction.VonMangoldt

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

/-- With `z = x^(1/δ₀)` and relative width `η = x⁻²`, the smoothed zero-free-box increment
bound gives a sharp truncation error of at most `(2K + 2) x^(-1 + δ/δ₀) (log Q)²`. This
separates the finite-difference argument from the contour estimate supplying the increment;
it is `Chebyshev.norm_add_sum_div_le_at_rpow` for `c(n) = χ(n) Λ(n)`. -/
theorem norm_logDeriv_add_sum_vonMangoldt_div_le_at_rpow {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x Q δ₀ δ K : ℝ} (hx : 2 ≤ x) (hδ₀ : 0 < δ₀)
    (hδ₀' : δ₀ ≤ 1) (hδ : 0 ≤ δ) (hQ : x ^ (1 / δ₀ + 3) ≤ Q)
    (hinc : ‖rieszSum (fun n ↦ χ n * Λ n) (x ^ (1 / δ₀) * (1 + x ^ (-2 : ℝ))) -
        rieszSum (fun n ↦ χ n * Λ n) (x ^ (1 / δ₀)) +
        ((x ^ (1 / δ₀) * x ^ (-2 : ℝ) : ℝ) : ℂ) * logDeriv χ.LFunction 1‖ ≤
      K * log Q * (x ^ (-2 : ℝ) * (x ^ (1 / δ₀)) ^ (1 - δ₀ + δ) * log Q +
        (x ^ (1 / δ₀)) ^ 2 / Q)) :
    ‖logDeriv χ.LFunction 1 + ∑ n ∈ Icc 1 ⌊x ^ (1 / δ₀)⌋₊, χ n * Λ n / (n : ℂ)‖ ≤
      (2 * K + 2) * x ^ (-1 + δ / δ₀) * log Q ^ 2 :=
  Chebyshev.norm_add_sum_div_le_at_rpow χ.norm_mul_vonMangoldt_le _ hx hδ₀ hδ₀' hδ hQ hinc

end DirichletCharacter
