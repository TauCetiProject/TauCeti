/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.DirichletEulerProduct
import TauCeti.NumberTheory.ArithmeticFunction.Misc
import TauCeti.NumberTheory.DirichletCharacter.PartialSum
import Mathlib.NumberTheory.Chebyshev

/-!
# Linear growth of the first Riesz remainder for nonprincipal Dirichlet characters

The harmonic sums of `χ(n) Λ(n)` are bounded for a nonprincipal character `χ`. Apply the twisted
von Mangoldt convolution identity and replace the inner harmonic character sums by `L(1, χ)`.
The truncation error is controlled by Chebyshev's bound and the logarithmically weighted character
sum is bounded by Abel summation. This gives a linear bound for the first Riesz remainder, without
using an explicit formula for the zeros.

## References

* T. M. Apostol, *Introduction to Analytic Number Theory*, §7.5 (the harmonic von Mangoldt sum
  for a nonprincipal character) and Theorem 6.17 (partial summation for nonprincipal characters).
* The normalization of the remainder is that of Levent Alpöge's `Deduction.Gchi` for nonprincipal
  characters in `Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean`.
-/

public section

open ArithmeticFunction Finset
open scoped LSeries.notation

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- The finite harmonic form of the twisted von Mangoldt convolution identity. -/
theorem sum_mul_log_div_eq_sum_mul_vonMangoldt_div_mul_sum_div (m : ℕ) :
    ∑ n ∈ Ioc 0 m, χ n * (Real.log n : ℂ) / (n : ℂ) =
      ∑ d ∈ Ioc 0 m, (χ d * (Λ d : ℂ) / (d : ℂ)) *
        ∑ n ∈ Ioc 0 (m / d), χ n / (n : ℂ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_smul_eq_sum_sum
    (toArithmeticFunction (↗χ * ↗Λ)) (toArithmeticFunction (↗χ))
    (fun n : ℕ ↦ (n : ℂ)⁻¹) m
  rw [← LSeries.convolution, χ.convolution_twist_vonMangoldt] at h
  refine Eq.trans ?_ (h.trans ?_)
  · refine sum_congr rfl fun n _ ↦ ?_
    simp [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm]
  · refine sum_congr rfl fun d hd ↦ ?_
    have hd₀ : d ≠ 0 := (mem_Ioc.mp hd).1.ne'
    simp only [smul_eq_mul, toArithmeticFunction, ArithmeticFunction.coe_mk,
      hd₀, ite_false, Pi.mul_apply, Finset.mul_sum]
    refine sum_congr rfl fun n hn ↦ ?_
    have hn₀ : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
    simp [hn₀, Nat.cast_mul, div_eq_mul_inv]
    ring

private theorem norm_sum_mul_vonMangoldt_div_mul_truncationError_le [NeZero N]
    (hχ : χ ≠ 1) (m : ℕ) :
    ‖∑ d ∈ Ioc 0 m, (χ d * (Λ d : ℂ) / (d : ℂ)) *
      (χ.LFunction 1 - ∑ n ∈ Ioc 0 (m / d), χ n / (n : ℂ))‖ ≤
        2 * (N : ℝ) * (Real.log 4 + 4) := by
  have hterm (d : ℕ) (hd : d ∈ Ioc 0 m) :
      ‖(χ d * (Λ d : ℂ) / (d : ℂ)) * (χ.LFunction 1 - ∑ n ∈ Ioc 0 (m / d), χ n / (n : ℂ))‖ ≤
        Λ d * (2 * (N : ℝ)) / (m : ℝ) := by
    have hd₀ := (mem_Ioc.mp hd).1
    have hlt : (m : ℝ) < (d : ℝ) * ((m / d : ℕ) + 1) := by
      have := (Nat.div_lt_iff_lt_mul hd₀).mp (Nat.lt_succ_self (m / d))
      exact_mod_cast (by simpa [mul_comm] using this : m < d * (m / d + 1))
    have hm : 0 < (m : ℝ) := by exact_mod_cast hd₀.trans_le (mem_Ioc.mp hd).2
    have htail := χ.norm_LFunction_one_sub_sum_Icc_div_le hχ (χ.norm_sum_Icc_le_level hχ) (m / d)
    have hcut : Icc 1 (m / d) = Ioc 0 (m / d) := Icc_add_one_left_eq_Ioc 0 _
    rw [hcut] at htail
    have hΛ : 0 ≤ Λ d := vonMangoldt_nonneg
    calc
      _ ≤ (Λ d / (d : ℝ)) * (2 * N / ((m / d : ℕ) + 1 : ℝ)) := by
        rw [norm_mul, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_of_nonneg hΛ]
        have hχΛ := mul_le_of_le_one_left hΛ (χ.norm_le_one d)
        exact mul_le_mul (div_le_div_of_nonneg_right hχΛ (Nat.cast_nonneg d))
          htail (norm_nonneg _) (by positivity)
      _ = (Λ d * (2 * N)) / ((d : ℝ) * ((m / d : ℕ) + 1)) := div_mul_div_comm ..
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hm hlt.le
  calc
    _ ≤ ∑ d ∈ Ioc 0 m, Λ d * (2 * (N : ℝ)) / (m : ℝ) :=
      (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = Chebyshev.psi m * (2 * (N : ℝ) / (m : ℝ)) := by
      simp only [Chebyshev.psi, Nat.floor_natCast, ← sum_mul, mul_div_assoc]
    _ ≤ ((Real.log 4 + 4) * m) * (2 * (N : ℝ) / m) :=
      mul_le_mul_of_nonneg_right (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg m))
        (by positivity)
    _ ≤ _ := by
      by_cases hm : m = 0
      · subst m
        simp only [Nat.cast_zero, mul_zero, _root_.div_zero]
        positivity
      · have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
        rw [mul_assoc, mul_div_cancel₀ _ hm', mul_comm]

/-- The harmonic sums of the twisted von Mangoldt coefficients of a nonprincipal Dirichlet
character are uniformly bounded. -/
theorem exists_norm_sum_mul_vonMangoldt_div_le (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ m : ℕ, ‖∑ d ∈ Ioc 0 m, χ d * (Λ d : ℂ) / (d : ℂ)‖ ≤ C := by
  by_cases hN : N = 0
  · subst N
    refine ⟨0, fun m ↦ ?_⟩
    simp_rw [mul_div_assoc]
    rw [χ.sum_mul_eq_zero_of_level_zero (Ioc 0 m) (fun d ↦ (Λ d : ℂ) / d) (by simp),
      norm_zero]
  let _ : NeZero N := ⟨hN⟩
  obtain ⟨B, hB⟩ := χ.exists_norm_sum_mul_log_div_le hχ
  let l := χ.LFunction 1
  have hL : 0 < ‖l‖ := norm_pos_iff.mpr
    (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simp))
  refine ⟨(B + 2 * N * (Real.log 4 + 4)) / ‖l‖, fun m ↦ (le_div_iff₀ hL).mpr ?_⟩
  rw [← norm_mul, sum_mul]
  calc
    _ = ‖(∑ n ∈ Ioc 0 m, χ n * (Real.log n : ℂ) / (n : ℂ)) +
        ∑ d ∈ Ioc 0 m, (χ d * (Λ d : ℂ) / (d : ℂ)) *
          (l - ∑ n ∈ Ioc 0 (m / d), χ n / (n : ℂ))‖ := by
      rw [χ.sum_mul_log_div_eq_sum_mul_vonMangoldt_div_mul_sum_div, ← sum_add_distrib]
      congr 1
      exact sum_congr rfl fun _ _ ↦ by ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add (hB m)
      (χ.norm_sum_mul_vonMangoldt_div_mul_truncationError_le hχ m))

/-- A nonprincipal Dirichlet character's first Riesz remainder grows at most linearly for
`y ≥ 0`. No primitivity is needed. -/
theorem exists_norm_rieszSum_add_mul_logDeriv_le_linear [NeZero N] (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ y ≥ 0,
      ‖TauCeti.rieszSum (fun n ↦ χ n * (Λ n : ℂ)) y +
        (y : ℂ) * logDeriv χ.LFunction 1‖ ≤ C * y := by
  obtain ⟨B, hB⟩ := χ.exists_norm_sum_mul_vonMangoldt_div_le hχ
  refine ⟨B + (Real.log 4 + 4) + ‖logDeriv χ.LFunction 1‖, fun y hy₀ ↦ ?_⟩
  have hpsi : ‖∑ n ∈ Ioc 0 ⌊y⌋₊, χ n * (Λ n : ℂ)‖ ≤ (Real.log 4 + 4) * y := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun n _ ↦ ?_).trans
      (Chebyshev.psi_le_const_mul_self hy₀))
    rw [norm_mul, Complex.norm_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one n)
  have hyIcc : y ∈ Set.Icc (⌊y⌋₊ : ℝ) ((⌊y⌋₊ : ℝ) + 1) :=
    ⟨Nat.floor_le hy₀, (Nat.lt_floor_add_one y).le⟩
  rw [TauCeti.rieszSum_eq_sum_mul_sub_sum_of_mem_Icc _ hyIcc]
  have hcut : Icc 1 ⌊y⌋₊ = Ioc 0 ⌊y⌋₊ := Icc_add_one_left_eq_Ioc 0 _
  rw [hcut, mul_comm _ (y : ℂ)]
  calc
    _ ≤ ‖(y : ℂ) * (∑ n ∈ Ioc 0 ⌊y⌋₊, χ n * (Λ n : ℂ) / (n : ℂ))‖ +
        ‖∑ n ∈ Ioc 0 ⌊y⌋₊, χ n * (Λ n : ℂ)‖ + ‖(y : ℂ) * logDeriv χ.LFunction 1‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ _ := by
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg hy₀]
      calc
        _ ≤ y * B + (Real.log 4 + 4) * y + y * ‖logDeriv χ.LFunction 1‖ :=
          add_le_add_left (add_le_add (mul_le_mul_of_nonneg_left (hB _) hy₀) hpsi) _
        _ = _ := by ring

end DirichletCharacter
