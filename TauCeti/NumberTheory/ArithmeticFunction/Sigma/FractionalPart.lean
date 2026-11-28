/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Average
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.NumberTheory.Harmonic.Basic

/-!
# The fractional-part form of the Dirichlet divisor remainder

`TauCeti.abs_sum_Ioc_sigma_zero_sub_add_bernoulliFun_le` expresses the divisor remainder
`Δ(x)` as `-2 ∑_{n ≤ √x} B₁({x / n})` with absolute error at most `1/2` for `x ≥ 0`.
The exact formula `TauCeti.sum_Ioc_sigma_zero_sub_add_bernoulliFun_eq` identifies the smooth
error term in terms of the harmonic number at `⌊√x⌋`. It uses
`TauCeti.sum_Ioc_sigma_zero_natFloor_add_sq` and `bernoulliFun_one`. The bound then uses
`TauCeti.harmonic_sub_eulerMascheroniConstant_le_log` and Mathlib's convexity of
`x ↦ x log x` (`Real.convexOn_mul_log`).

## References

* K. Berkane, O. Bordellès, O. Ramaré, *Explicit upper bounds for the remainder term in the
  divisor problem*, Math. Comp. 81 (2012), Lemma 3.1.
-/

public section

open Finset Real
open scoped ArithmeticFunction.sigma

namespace TauCeti

/-- Lower bound for the smooth error at a square, used for both endpoints of the interval. -/
private theorem neg_one_half_le_hyperbola_correction_at_square (n : ℕ) :
    -(1 / 2 : ℝ) ≤ (n : ℝ) ^ 2 *
      (2 * ((harmonic n : ℝ) - eulerMascheroniConstant) + 1) -
      (n : ℝ) ^ 2 * log ((n : ℝ) ^ 2) - ((n : ℝ) ^ 2 + n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · norm_num
  have h := one_div_two_mul_add_le_harmonic_sub_log_sub_eulerMascheroniConstant hn
  have hnonneg : 0 ≤ 2 * (n : ℝ) ^ 2 := by positivity
  have h' := mul_le_mul_of_nonneg_left h hnonneg
  have hrat : (n : ℝ) - 1 / 2 ≤ 2 * (n : ℝ) ^ 2 / (2 * n + 2 / 5) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [← mul_div_assoc, mul_one] at h'
  simp only [log_pow, Nat.cast_ofNat]
  linarith

/-- Bound the smooth error when the harmonic number is fixed between successive squares. -/
private theorem abs_hyperbola_correction_le {n : ℕ} {x : ℝ}
    (hx : x ∈ Set.Icc ((n : ℝ) ^ 2) ((n + 1 : ℝ) ^ 2)) :
    |x * (2 * ((harmonic n : ℝ) - eulerMascheroniConstant) + 1) -
      x * log x - ((n : ℝ) ^ 2 + n)| ≤ 1 / 2 := by
  rw [abs_le]
  constructor
  · have hleft := neg_one_half_le_hyperbola_correction_at_square n
    have hright : -(1 / 2 : ℝ) ≤ (n + 1 : ℝ) ^ 2 *
        (2 * ((harmonic n : ℝ) - eulerMascheroniConstant) + 1) -
        (n + 1 : ℝ) ^ 2 * log ((n + 1 : ℝ) ^ 2) - ((n : ℝ) ^ 2 + n) := by
      have hn := neg_one_half_le_hyperbola_correction_at_square (n + 1)
      rw [harmonic_succ] at hn
      push_cast at hn
      convert hn using 1
      field
    have hconcave : ConcaveOn ℝ (Set.Ici (0 : ℝ))
        (fun t ↦ t * (2 * ((harmonic n : ℝ) - eulerMascheroniConstant) + 1) -
          t * log t - ((n : ℝ) ^ 2 + n)) := by
      have hlinear := (LinearMap.mulRight ℝ (2 * ((harmonic n : ℝ) -
        eulerMascheroniConstant) + 1)).concaveOn (convex_Ici (0 : ℝ))
      convert (hlinear.sub convexOn_mul_log).sub
        (convexOn_const ((n : ℝ) ^ 2 + n) (convex_Ici (0 : ℝ))) using 1
      ext t
      simp only [Pi.sub_apply, LinearMap.mulRight_apply]
    exact (le_min hleft hright).trans
      (hconcave.min_le_of_mem_Icc (Set.mem_Ici.2 (sq_nonneg _)) (Set.mem_Ici.2 (sq_nonneg _)) hx)
  · have hH := harmonic_sub_eulerMascheroniConstant_le_log n
    have hupper : x * (log ((n : ℝ) ^ 2 + n + 1 / 2) + 1) - x * log x ≤
        (n : ℝ) ^ 2 + n + 1 / 2 := by
      have hx0 : 0 ≤ x := (sq_nonneg _).trans hx.1
      rcases hx0.eq_or_lt with rfl | hx0
      · simp only [zero_mul, sub_zero]
        positivity
      have hc : 0 < (n : ℝ) ^ 2 + n + 1 / 2 := by positivity
      have h := log_le_sub_one_of_pos (div_pos hc hx0)
      rw [log_div hc.ne' hx0.ne'] at h
      have hm := mul_le_mul_of_nonneg_left h hx0.le
      have hcancel : x * (((n : ℝ) ^ 2 + n + 1 / 2) / x - 1) =
          (n : ℝ) ^ 2 + n + 1 / 2 - x := by field
      rw [hcancel] at hm
      linarith
    have h := mul_le_mul_of_nonneg_left hH ((sq_nonneg _).trans hx.1)
    linarith

/-- The divisor remainder plus twice the sum of periodic first Bernoulli values equals a
smooth expression involving the harmonic number at `⌊√x⌋`. -/
theorem sum_Ioc_sigma_zero_sub_add_bernoulliFun_eq (x : ℝ) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ)) - (x * log x + (2 * eulerMascheroniConstant - 1) * x) +
      2 * ∑ n ∈ Ioc 0 ⌊√x⌋₊, bernoulliFun 1 (Int.fract (x / n)) =
    x * (2 * ((harmonic ⌊√x⌋₊ : ℝ) - eulerMascheroniConstant) + 1) -
      x * log x - ((⌊√x⌋₊ : ℝ) ^ 2 + ⌊√x⌋₊) := by
  rcases le_or_gt 0 x with hx | hx
  · have hhyperbola : (∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ)) + (⌊√x⌋₊ : ℝ) ^ 2 =
        2 * ∑ n ∈ Ioc 0 ⌊√x⌋₊, (⌊x / n⌋₊ : ℝ) := by
      exact_mod_cast sum_Ioc_sigma_zero_natFloor_add_sq x
    have hBernoulli : ∀ n : ℕ,
        bernoulliFun 1 (Int.fract (x / n)) = x * (n : ℝ)⁻¹ - (⌊x / n⌋₊ : ℝ) - 1 / 2 := by
      intro n
      rw [bernoulliFun_one, ← Int.self_sub_floor, ← natCast_floor_eq_intCast_floor (by positivity),
        div_eq_mul_inv]
    have hcount : ∑ _n ∈ Ioc 0 ⌊√x⌋₊, (1 / 2 : ℝ) = (⌊√x⌋₊ : ℝ) / 2 := by
      simp [div_eq_mul_inv]
    simp only [hBernoulli, sum_sub_distrib, ← mul_sum, hcount]
    rw [← cast_harmonic_eq_sum_Ioc]
    linarith
  · rw [sqrt_eq_zero_of_nonpos hx.le, Nat.floor_zero, Nat.floor_eq_zero.mpr (by linarith : x < 1)]
    simp only [Ioc_self, sum_empty, Nat.cast_zero, harmonic_zero, Rat.cast_zero]
    ring

/-- The Dirichlet divisor remainder at a nonnegative real cutoff is within `1/2` of
`-2 ∑_{1 ≤ n ≤ √x} B₁({x / n})`, where `B₁({t}) = {t} - 1/2`.
This is Berkane–Bordellès–Ramaré, Lemma 3.1, with the cutoff extended to `0 ≤ x < 1`. -/
theorem abs_sum_Ioc_sigma_zero_sub_add_bernoulliFun_le {x : ℝ} (hx : 0 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) - (x * log x + (2 * eulerMascheroniConstant - 1) * x) +
      2 * ∑ n ∈ Ioc 0 ⌊√x⌋₊, bernoulliFun 1 (Int.fract (x / n))| ≤ 1 / 2 := by
  rw [sum_Ioc_sigma_zero_sub_add_bernoulliFun_eq]
  apply abs_hyperbola_correction_le
  have hleft : (⌊√x⌋₊ : ℝ) ^ 2 ≤ (√x) ^ 2 := by
    gcongr
    exact Nat.floor_le (sqrt_nonneg x)
  have hright : (√x) ^ 2 ≤ (⌊√x⌋₊ + 1 : ℝ) ^ 2 := by
    gcongr
    exact (Nat.lt_floor_add_one _).le
  rw [sq_sqrt hx] at hleft hright
  exact ⟨hleft, hright⟩

end TauCeti
