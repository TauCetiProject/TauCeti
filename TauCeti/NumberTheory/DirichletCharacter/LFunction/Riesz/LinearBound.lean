/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.NumberTheory.Chebyshev
import TauCeti.NumberTheory.DirichletCharacter.LFunction.VonMangoldt

/-!
# Linear growth of the first Riesz remainder for nonprincipal Dirichlet characters

The uniform bound `DirichletCharacter.exists_norm_sum_mul_vonMangoldt_div_le` for the harmonic
sums of `χ(n) Λ(n)`, together with Chebyshev's bound on `∑_{n ≤ y} Λ(n)`, gives a linear
bound for the first Riesz remainder without using an explicit formula for the zeros.

## References

* The normalization of the remainder is that of Levent Alpöge's `Deduction.Gchi` for nonprincipal
  characters in `Development/AutomorphicArithmetic/DedekindLFunctions/CharFamily.lean`.
-/

public section

open ArithmeticFunction Finset

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

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
