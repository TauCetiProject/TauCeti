/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.Chebyshev
import TauCeti.NumberTheory.DirichletCharacter.ArithmeticFunction
import TauCeti.NumberTheory.DirichletCharacter.PartialSum
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.DirichletEulerProduct

/-!
# Harmonic sums of twisted von Mangoldt coefficients

For a nonprincipal Dirichlet character `χ`, the partial sums of `χ(n) Λ(n) / n` are
uniformly bounded. In the finite twisted convolution
`DirichletCharacter.sum_mul_log_div_eq_sum_mul_vonMangoldt_div_mul_sum_div`, replace the inner
harmonic character sums by `L(1, χ)`. Chebyshev's bound controls the truncation error, and
Abel summation bounds the logarithmically weighted character sum.

## References

* T. M. Apostol, *Introduction to Analytic Number Theory*, §7.5 (the harmonic von Mangoldt sum
  for a nonprincipal character) and Theorem 6.17 (partial summation for nonprincipal characters).
-/

public section

open ArithmeticFunction Finset

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

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

end DirichletCharacter
