/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import Mathlib.Tactic.Linarith

/-!
# The higher-prime-power remainder and right-half-plane bound for zeta

On the real half-line greater than one, subtracting the prime sum from `-ζ'/ζ` leaves the
exact geometric higher-prime-power tail. On `2 ≤ Re s`, specializing the uniform Dirichlet
majorant (built on Michael Stoll's `DirichletCharacter.LSeries_twist_vonMangoldt_eq` and
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`) to level `1` and `σ = 2`
bounds `‖ζ'/ζ(s)‖` by `-(ζ'/ζ)(2).re`.
-/

public section

open Complex DirichletCharacter ArithmeticFunction LSeries

namespace TauCeti

/-- The difference between minus zeta's logarithmic derivative and its prime sum is the
exact geometric higher-prime-power tail. -/
theorem neg_re_logDeriv_riemannZeta_sub_tsum_prime_eq {σ : ℝ} (hσ : 1 < σ) :
    -(logDeriv riemannZeta (σ : ℂ)).re - ∑' p : Nat.Primes, Real.log p / (p : ℝ) ^ σ =
      ∑' p : Nat.Primes, Real.log p / ((p : ℝ) ^ σ * ((p : ℝ) ^ σ - 1)) := by
  have h := (1 : DirichletCharacter ℂ 1).logDeriv_LFunction_add_tsum_prime_eq
    (s := (σ : ℂ)) (by simpa)
  have hχ (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  rw [DirichletCharacter.LFunction_modOne_eq] at h
  simp only [hχ, one_mul] at h
  have hs0 : (σ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (zero_lt_one.trans hσ)
  have hpow (n : ℕ) : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_cpow n.cast_nonneg σ).symm
  simp only [term_of_ne_zero' hs0, Pi.mul_apply, one_mul, hpow, ← Complex.ofReal_div] at h
  have hif (n : ℕ) :
      (if n.Prime then (0 : ℂ) else ((vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ)) =
        (((if n.Prime then 0 else vonMangoldt n) / (n : ℝ) ^ σ : ℝ) : ℂ) := by
    split_ifs <;> simp_all
  simp only [hif, ← Complex.ofReal_tsum] at h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re] at hr
  linarith [(vonMangoldt.hasSum_prime_log_div_rpow_mul_sub_one (by linarith : 1 / 2 < σ)).tsum_eq]

/-- On the half-plane `2 ≤ Re s`, `‖ζ'/ζ(s)‖` is bounded by `-(ζ'/ζ)(2).re`. -/
theorem norm_logDeriv_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ -(logDeriv riemannZeta 2).re := by
  simpa only [LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq, Complex.ofReal_ofNat] using
    (1 : DirichletCharacter ℂ 1).norm_logDeriv_LFunction_le_neg_re_logDeriv_LFunctionTrivChar
      (σ := 2) one_lt_two hs

end TauCeti
