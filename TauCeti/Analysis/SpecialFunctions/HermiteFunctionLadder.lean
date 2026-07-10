module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.SpecialFunctions.HermiteFunction
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Ladder relations for the Hermite functions

This file adds the **A2 ladder relations** of the `OrthogonalL2Bases` roadmap to the Hermite
function object API (`TauCeti.hermiteFunction`,
`ψₙ(x) = Hₙ(x√2) exp(-x²/2) / √(n!√π)`).

The two relations expose how the position operator `x·` and the derivative `d/dx` shift the Hermite
index:

* `TauCeti.mul_hermiteFunction` — `x·ψₙ = √((n+1)/2)·ψ_{n+1} + √(n/2)·ψ_{n-1}`;
* `TauCeti.hasDerivAt_hermiteFunction` (and its `deriv` form `TauCeti.deriv_hermiteFunction`) —
  `ψₙ' = √(n/2)·ψ_{n-1} - √((n+1)/2)·ψ_{n+1}`.

Adding and subtracting them yields the annihilation/creation identities for the ladder operators
`a = (x + d/dx)/√2` and `a† = (x - d/dx)/√2`:

* `TauCeti.hermiteFunction_lowering` — `x·ψₙ + ψₙ' = √(2n)·ψ_{n-1}` (so `a ψₙ = √n ψ_{n-1}`);
* `TauCeti.hermiteFunction_raising` — `x·ψₙ - ψₙ' = √(2(n+1))·ψ_{n+1}`
  (so `a† ψₙ = √(n+1) ψ_{n+1}`).

Both relations are purely pointwise and reduce, after clearing the Gaussian envelope and the
normalization `√(n!√π)`, to Mathlib's three-term recurrence for `Polynomial.hermite`
(`hermite_succ` together with `Polynomial.derivative_hermite`); no integration is involved. This is
the level at which the roadmap wants these identities stated, so that they elevate to the ladder
operators on `𝒮(ℝ)` / `L²(ℝ)` later without re-proof.

The `n = 0` boundary is covered by the `√(n/2) = 0` coefficient, which annihilates the (Nat-clamped)
`ψ_{n-1}` term, so the relations hold uniformly for all `n : ℕ`.
-/

public section

namespace TauCeti

open Polynomial

/-- The `n`-step three-term recurrence for the probabilists' Hermite polynomials, evaluated at a
point: `y·Hₙ(y) = H_{n+1}(y) + n·H_{n-1}(y)`. This is Mathlib's `hermite_succ`
(`H_{n+1} = X·Hₙ - H'ₙ`) with the derivative eliminated via `Polynomial.derivative_hermite`
(`H'ₙ = n·H_{n-1}`). At `n = 0` the last term vanishes. -/
private lemma aeval_hermite_recurrence (n : ℕ) (y : ℝ) :
    y * aeval y (hermite n) =
      aeval y (hermite (n + 1)) + (n : ℝ) * aeval y (hermite (n - 1)) := by
  have h : aeval y (hermite (n + 1))
      = y * aeval y (hermite n) - (n : ℝ) * aeval y (hermite (n - 1)) := by
    rw [hermite_succ, Polynomial.derivative_hermite, map_sub, map_mul, map_nsmul, aeval_X,
      nsmul_eq_mul]
  rw [h]; ring

/-- The Hermite normalization `√(n!·√π)` at successor index: `√((n+1)!·√π) = √(n+1)·√(n!·√π)`. -/
private lemma normFactor_succ (n : ℕ) :
    Real.sqrt (((n + 1).factorial : ℝ) * Real.sqrt Real.pi)
      = Real.sqrt (n + 1) * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- `2·√(k/2) = √(2k)`: the coefficient identity behind the ladder-operator normalizations. -/
private lemma two_mul_sqrt_half (k : ℝ) : 2 * Real.sqrt (k / 2) = Real.sqrt (2 * k) := by
  rw [show (2 : ℝ) * k = 4 * (k / 2) by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
    show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]

/-- **Target A2 (position ladder relation).** Multiplying `ψₙ` by `x` mixes the neighbouring modes:
`x·ψₙ = √((n+1)/2)·ψ_{n+1} + √(n/2)·ψ_{n-1}`. -/
theorem mul_hermiteFunction (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x =
      Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) x
        + Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) x := by
  rcases n with _ | m
  · simp only [Nat.cast_zero, zero_add, Nat.zero_sub, hermiteFunction_one, zero_div,
      Real.sqrt_zero, zero_mul, add_zero]
    rw [show Real.sqrt (1 / 2) * (Real.sqrt 2 * x * hermiteFunction 0 x)
          = (Real.sqrt (1 / 2) * Real.sqrt 2) * (x * hermiteFunction 0 x) by ring,
      ← Real.sqrt_mul (by norm_num), show (1 : ℝ) / 2 * 2 = 1 by norm_num, Real.sqrt_one,
      one_mul]
  · -- successor case: reduce to the recurrence `√2·x·Hₘ₊₁ = Hₘ₊₂ + (m+1)·Hₘ`
    have hrec := aeval_hermite_recurrence (m + 1) (x * Real.sqrt 2)
    simp only [Nat.add_sub_cancel] at hrec ⊢
    rw [hermiteFunction_def, hermiteFunction_def, hermiteFunction_def,
      Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
    simp only [normFactor_succ]
    set e := Real.exp (-((x : ℝ) ^ 2 / 2)) with he
    set N := Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi) with hN
    have hN0 : N ≠ 0 := (sqrt_factorial_mul_sqrt_pi_pos m).ne'
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsm1 : Real.sqrt ((m : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsm2 : Real.sqrt ((m : ℝ) + 1 + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsq : Real.sqrt (1 + (m : ℝ)) * Real.sqrt (1 + (m : ℝ)) = 1 + (m : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    push_cast at hrec
    field_simp
    ring_nf
    ring_nf at hrec
    push_cast
    linear_combination e * hrec - e * aeval (x * Real.sqrt 2) (hermite m) * hsq

/-- **Target A2 (derivative ladder relation).** Differentiating `ψₙ` mixes the neighbouring modes:
`ψₙ' = √(n/2)·ψ_{n-1} - √((n+1)/2)·ψ_{n+1}`. -/
theorem hasDerivAt_hermiteFunction (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFunction n)
      (Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) x
        - Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) x) x := by
  have hP : HasDerivAt (fun x : ℝ => aeval (x * Real.sqrt 2) (hermite n))
      (aeval (x * Real.sqrt 2) (derivative (hermite n)) * Real.sqrt 2) x := by
    have h := (Polynomial.hasDerivAt_aeval (hermite n) (x * Real.sqrt 2)).comp x
      ((hasDerivAt_id x).mul_const (Real.sqrt 2))
    simpa only [Function.comp_def, one_mul, id_eq] using h
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2 / 2)))
      (-x * Real.exp (-(x ^ 2 / 2))) x := by
    have hx2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    simpa [mul_comm] using hx2.neg.exp
  have key :
      (aeval (x * Real.sqrt 2) (derivative (hermite n)) * Real.sqrt 2 * Real.exp (-(x ^ 2 / 2))
          + aeval (x * Real.sqrt 2) (hermite n) * (-x * Real.exp (-(x ^ 2 / 2))))
          / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)
        = Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) x
          - Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) x := by
    rw [Polynomial.derivative_hermite, map_nsmul, nsmul_eq_mul]
    rcases n with _ | m
    · simp only [Nat.cast_zero, zero_add, Nat.zero_sub, hermiteFunction_zero, hermiteFunction_one,
        zero_div, Real.sqrt_zero, zero_mul, hermite_zero, map_one]
      rw [show Real.sqrt (1 / 2) * (Real.sqrt 2 * x
            * (Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi)))
            = (Real.sqrt (1 / 2) * Real.sqrt 2)
              * (x * (Real.exp (-(x ^ 2 / 2)) / Real.sqrt (Real.sqrt Real.pi))) by ring,
        ← Real.sqrt_mul (by norm_num), show (1 : ℝ) / 2 * 2 = 1 by norm_num, Real.sqrt_one,
        one_mul, Nat.factorial_zero, Nat.cast_one, one_mul]
      ring
    · have hrec := aeval_hermite_recurrence (m + 1) (x * Real.sqrt 2)
      simp only [Nat.add_sub_cancel] at hrec ⊢
      rw [hermiteFunction_def, hermiteFunction_def,
        Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
      simp only [normFactor_succ]
      set e := Real.exp (-((x : ℝ) ^ 2 / 2)) with he
      set N := Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi) with hN
      have hN0 : N ≠ 0 := (sqrt_factorial_mul_sqrt_pi_pos m).ne'
      have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      have hsm1 : Real.sqrt ((m : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      have hsm2 : Real.sqrt ((m : ℝ) + 1 + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      have hsq : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      push_cast at hrec ⊢
      field_simp
      linear_combination -e * hrec
        + e * aeval (x * Real.sqrt 2) (hermite m) * ((m : ℝ) + 1) * hs2sq
        - e * aeval (x * Real.sqrt 2) (hermite m) * hsq
  have hfun : hermiteFunction n
      = fun x => aeval (x * Real.sqrt 2) (hermite n) * Real.exp (-(x ^ 2 / 2))
          / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := by
    funext y; exact hermiteFunction_def n y
  rw [hfun]
  exact key ▸ (hP.mul hE).div_const (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))

/-- The `deriv` form of `hasDerivAt_hermiteFunction`. -/
theorem deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (hermiteFunction n) x =
      Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) x
        - Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) x :=
  (hasDerivAt_hermiteFunction n x).deriv

/-- **Annihilation identity.** For the ladder operator `a = (x + d/dx)/√2`, `a ψₙ = √n·ψ_{n-1}`,
here as `x·ψₙ + ψₙ' = √(2n)·ψ_{n-1}`. -/
theorem hermiteFunction_lowering (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x + deriv (hermiteFunction n) x
      = Real.sqrt (2 * (n : ℝ)) * hermiteFunction (n - 1) x := by
  rw [mul_hermiteFunction, deriv_hermiteFunction, ← two_mul_sqrt_half (n : ℝ)]
  ring

/-- **Creation identity.** For the ladder operator `a† = (x - d/dx)/√2`, `a† ψₙ = √(n+1)·ψ_{n+1}`,
here as `x·ψₙ - ψₙ' = √(2(n+1))·ψ_{n+1}`. -/
theorem hermiteFunction_raising (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x - deriv (hermiteFunction n) x
      = Real.sqrt (2 * ((n : ℝ) + 1)) * hermiteFunction (n + 1) x := by
  rw [mul_hermiteFunction, deriv_hermiteFunction, ← two_mul_sqrt_half ((n : ℝ) + 1)]
  ring

end TauCeti
