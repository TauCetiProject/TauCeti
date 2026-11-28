/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Laplace
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Riesz.Mellin
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire

/-!
# Laplace transform of a Dirichlet character's Riesz remainder

The pole-removed `L`-function gives a uniform expression for the main term subtracted from
first Riesz sums at any level, including for imprimitive and principal characters. In
logarithmic coordinates this identifies the Laplace integral with the meromorphic Riesz
expression on the half-plane of absolute convergence.

The pole-clearing normalization is the one in `New.integral_primeRemainder`,
`grh/src/New/Reduction/Zeros/PrimeError.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open ArithmeticFunction TauCeti

namespace DirichletCharacter

open Classical in
/-- For any Dirichlet character, the first Riesz sum of `χ(n) Λ(n)` with the main term removed
has Laplace transform `rieszRemainderMellin χ.LFunction`. This form uses logarithmic cutoffs and
normalizes the Riesz sum by its length, which shifts the Laplace parameter by one. -/
theorem hasLaplace_normalized_rieszSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    HasLaplace (fun u ↦ rieszSum (fun n ↦ χ n * (Λ n : ℂ)) (Real.exp u) / (Real.exp u : ℂ) +
      logDeriv χ.entireLFunction 1 - (if χ = 1 then 1 else 0) * ((u : ℂ) - 1)) (s - 1)
      (rieszRemainderMellin χ.LFunction s) := by
  let δ : ℂ := if χ = 1 then 1 else 0
  have hL := χ.LSeriesHasSum_twist_vonMangoldt hs
  have h := hasLaplace_normalized_riesz_remainder hs hL.summable δ
    (-logDeriv χ.entireLFunction 1 - δ)
  rw [hL.LSeries_eq] at h
  have hs₀ : s ≠ 0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hs₁ : s - 1 ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using sub_pos.mpr hs)
  convert h using 1
  · ext u
    ring
  · by_cases hχ : χ = 1
    · subst χ
      rw [rieszRemainderMellin_LFunctionTrivChar q hs, entireLFunction_one]
      simp only [δ, ite_true, one_div]
      field_simp
      ring
    · rw [χ.rieszRemainderMellin_LFunction_of_ne_one hχ hs, entireLFunction_of_ne_one hχ]
      simp only [δ, ite_eq_right hχ, zero_div, sub_zero]
      field_simp
      ring

end DirichletCharacter
