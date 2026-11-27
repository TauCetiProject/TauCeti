/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ZeroFreeRegion
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.PowerLevel
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# A uniform zero-free disc for powers of a fixed modulus

At levels `m ^ k`, the characters whose square is principal come from finitely many levels with
unchanged regularized L-functions. Their lower bound near `1` is therefore uniform in `k`.
This allows the zero-free region with the logarithmic derivative bound to be applied throughout
the tower, in the discs used to detect primes in logarithmic windows.

The fixed-family argument and logarithmic choice of scale are from
`New.eventually_norm_logDeriv_entireL_le_near_one` in [lsernau/grh-lean, `Primes.lean`]
(https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/Lib/Analytic/Primes.lean).
-/

public section

open Complex Filter Real Asymptotics
open scoped Topology

namespace DirichletCharacter

/-- On a tower of powers of a fixed nonzero modulus, regularized L-functions of characters
whose square is principal satisfy a common lower bound on sufficiently small discs at `1`. -/
theorem eventually_le_norm_regularizedLFunction_pow_level (m : ℕ) [NeZero m] :
    ∀ᶠ r : ℝ in 𝓝 0, ∀ (k : ℕ) (χ : DirichletCharacter ℂ (m ^ k)), χ ^ 2 = 1 →
      ∀ z : ℂ, ‖z - 1‖ ≤ r → r ≤ ‖χ.regularizedLFunction z‖ := by
  have hb : ∀ᶠ r : ℝ in 𝓝 0, ∀ (j : Fin 4) (ψ : DirichletCharacter ℂ (m ^ (j : ℕ))),
      ∀ z : ℂ, ‖z - 1‖ ≤ r → r ≤ ‖ψ.regularizedLFunction z‖ :=
    eventually_all.mpr fun j ↦ eventually_all.mpr fun ψ ↦ ψ.eventually_le_norm_regularizedLFunction
  filter_upwards [hb] with r hr k χ hχ z hz
  obtain ⟨hd, ψ, rfl⟩ := χ.factorsThrough_pow_min_three_of_sq_eq_one hχ
  have hpf : (m ^ k).primeFactors = (m ^ min k 3).primeFactors := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp
    · rw [Nat.primeFactors_pow m hk, Nat.primeFactors_pow m (by omega : min k 3 ≠ 0)]
  rw [ψ.regularizedLFunction_changeLevel_eq_of_primeFactors_eq hd hpf]
  exact hr ⟨min k 3, by omega⟩ ψ z hz

/-- For sufficiently large `X` depending only on `m` and `A`, all Dirichlet characters of level
`m ^ k ≤ X ^ A` have a zero-free pole-cleared L-function on `‖s - 1‖ ≤ 1 / X`, with logarithmic
derivative of norm at most `X` there. -/
theorem eventually_entireLFunction_ne_zero_and_norm_logDeriv_le_pow_level
    (m : ℕ) [NeZero m] (A : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ k : ℕ, (↑(m ^ k) : ℝ) ≤ X ^ A →
      ∀ (χ : DirichletCharacter ℂ (m ^ k)) (s : ℂ), ‖s - 1‖ ≤ X⁻¹ →
        χ.entireLFunction s ≠ 0 ∧ ‖logDeriv χ.entireLFunction s‖ ≤ X := by
  let l (X : ℝ) : ℝ := (↑(A + 1) : ℝ) * Real.log X
  have hl : Tendsto l atTop atTop := Real.tendsto_log_atTop.const_mul_atTop (by positivity)
  have hinv : Tendsto (fun X : ℝ ↦ (l X)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hl
  have hsmall := (IsLittleO.const_mul_left
    (isLittleO_log_rpow_rpow_atTop 25 (by norm_num : (0 : ℝ) < 1))
    (2 * (↑(A + 1) : ℝ) ^ 25)).eventuallyLE
  filter_upwards [hl.eventually (eventually_ge_atTop (10 ^ 10)),
    hinv.eventually (eventually_le_norm_regularizedLFunction_pow_level m), hsmall,
    eventually_ge_atTop (2 : ℝ)] with X hlarge hnear hsmall hX k hk χ s hs
  have hX₀ : 0 < X := by linarith
  have hl₀ : 0 < l X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hpow : Real.log X ^ (25 : ℝ) = Real.log X ^ (25 : ℕ) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log X) 25
  rw [Real.rpow_one, hpow, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg hX₀.le, mul_assoc, ← mul_pow] at hsmall
  have hsmall' : 2 * l X ^ 25 ≤ X := hsmall
  have hexp : Real.exp (l X) = X ^ (A + 1) := by
    dsimp only [l]
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hXinv : X⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hre : 1 - 1 / l X ^ 25 ≤ s.re := by
    have h := (abs_le.mp ((abs_re_le_norm (s - 1)).trans hs)).1
    simp only [sub_re, one_re] at h
    have hle : X⁻¹ ≤ 1 / l X ^ 25 := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by linarith : l X ^ 25 ≤ X)
    linarith
  have hnorm : ‖s‖ ≤ Real.exp (l X) := calc
    ‖s‖ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_le_norm_sub_add s 1
    _ ≤ 2 := by simp only [norm_one]; linarith
    _ ≤ Real.exp (l X) := by linarith [Real.add_one_le_exp (l X)]
  have hmod : (↑(m ^ k) : ℝ) ≤ Real.exp (l X) := by
    rw [hexp, pow_succ]
    exact hk.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  obtain ⟨hnz, hbound⟩ := χ.entireLFunction_ne_zero_and_norm_logDeriv_le hlarge hmod
    (by simpa only [one_div] using hnear k χ) hre hnorm
  exact ⟨hnz, hbound.trans hsmall'⟩

end DirichletCharacter
