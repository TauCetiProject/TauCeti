/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import TauCeti.Analysis.SpecialFunctions.QPochhammer
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Product identities for the Dedekind eta function

Mathlib's Dedekind eta function is `η(τ) = q^{1/24} ∏_{n ≥ 1} (1 - qⁿ)` with `q = e^{2π i τ}` and
`q^{1/24} = e^{2π i τ / 24}` (`ModularForm.eta`). This file compares `η` at `2τ`, `τ / 2` and
`(τ + 1) / 2` with `η(τ)` by explicit products: with `s = e^{π i τ}`, so that `q = s²`,
* `η(2τ) = e^{π i τ / 12} η(τ) ∏_{n ≥ 1} (1 + qⁿ)`;
* `η(τ / 2) = e^{-π i τ / 24} η(τ) ∏_{n ≥ 0} (1 - s^{2n+1})`;
* `η((τ + 1) / 2) = e^{π i / 24} e^{-π i τ / 24} η(τ) ∏_{n ≥ 0} (1 + s^{2n+1})`.

Up to powers of `q`, the three products on the right are Weber's modular functions `𝔣₂/√2`, `𝔣₁`
and `𝔣`, so these identities express Weber's functions, and the level-two Siegel functions, as
quotients of eta values. The file also records the square of the
transformation of `η` under `S : τ ↦ -1/τ`, `η(-1/τ)² = -i τ η(τ)²`, which avoids the branch of
`√τ` in Mathlib's `ModularForm.eta_comp_eq_csqrt_I_inv`, and compares that transformation at `τ`
and at `c τ` for real `c > 0`, where the branches of `√(c τ)` and `√τ` differ by the factor `√c`.

## Main results

* `TauCeti.ModularForm.eta_eq_exp_mul_tprod`: `η(τ) = e^{2π i τ / 24} ∏_{n ≥ 1} (1 - qⁿ)`.
* `TauCeti.ModularForm.eta_two_mul`, `TauCeti.ModularForm.eta_div_two`,
  `TauCeti.ModularForm.eta_add_one_div_two`: the three product identities above.
* `TauCeti.ModularForm.eta_neg_one_div_sq`: `η(-1/τ)² = -i τ η(τ)²` on the upper half-plane.
* `TauCeti.ModularForm.eta_neg_one_div_ofReal_mul_mul`: `η(-1/(c τ)) η(τ) = √c η(c τ) η(-1/τ)`
  for real `c > 0`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber's functions as eta quotients).
-/

public section

open Complex
open scoped Real ModularForm

namespace TauCeti.ModularForm

/-- Mathlib's Dedekind eta function as an exponential times the Euler product:
`η(τ) = e^{2π i τ / 24} ∏_{n ≥ 1} (1 - qⁿ)` with `q = e^{2π i τ}`. -/
theorem eta_eq_exp_mul_tprod (τ : ℂ) :
    η τ = cexp (2 * π * I * τ / 24) * ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) := by
  simp only [_root_.ModularForm.eta, _root_.ModularForm.eta_q_eq_pow, Function.Periodic.qParam,
    ofReal_ofNat]

/-- `η(2τ) = e^{π i τ / 12} η(τ) ∏_{n ≥ 1} (1 + qⁿ)` on the upper half-plane, where
`q = e^{2π i τ}`. -/
theorem eta_two_mul {τ : ℂ} (hτ : 0 < τ.im) :
    η (2 * τ) = cexp (π * I * τ / 12) * η τ *
      ∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (n + 1)) := by
  have hq : cexp (2 * π * I * (2 * τ)) = cexp (2 * π * I * τ) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have he :
      cexp (2 * π * I * (2 * τ) / 24) = cexp (π * I * τ / 12) * cexp (2 * π * I * τ / 24) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [eta_eq_exp_mul_tprod, eta_eq_exp_mul_tprod, hq, he,
    ← tprod_one_add_pow_mul_tprod_one_sub_pow (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩)]
  ring

/-- `η(τ / 2) = e^{-π i τ / 24} η(τ) ∏_{n ≥ 0} (1 - s^{2n+1})` on the upper half-plane, where
`s = e^{π i τ}`. -/
theorem eta_div_two {τ : ℂ} (hτ : 0 < τ.im) :
    η (τ / 2) = cexp (-(π * I * τ / 24)) * η τ *
      ∏' n : ℕ, (1 - cexp (π * I * τ) ^ (2 * n + 1)) := by
  have hs : cexp (2 * π * I * (τ / 2)) = cexp (π * I * τ) := by
    congr 1
    ring
  have he : cexp (2 * π * I * (τ / 2) / 24) =
      cexp (-(π * I * τ / 24)) * cexp (2 * π * I * τ / 24) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [eta_eq_exp_mul_tprod, eta_eq_exp_mul_tprod, hs, he,
    tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul (UpperHalfPlane.norm_exp_pi_I_lt_one hτ),
    ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq]
  ring

/-- `η((τ + 1) / 2) = e^{π i / 24} e^{-π i τ / 24} η(τ) ∏_{n ≥ 0} (1 + s^{2n+1})` on the upper
half-plane, where `s = e^{π i τ}`. -/
theorem eta_add_one_div_two {τ : ℂ} (hτ : 0 < τ.im) :
    η ((τ + 1) / 2) = cexp (π * I / 24) * cexp (-(π * I * τ / 24)) * η τ *
      ∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1)) := by
  have hs : cexp (2 * π * I * ((τ + 1) / 2)) = -cexp (π * I * τ) := by
    have harg : 2 * π * I * ((τ + 1) / 2) = π * I * τ + π * I := by ring
    rw [harg, Complex.exp_add, exp_pi_mul_I, mul_neg_one]
  have he : cexp (2 * π * I * ((τ + 1) / 2) / 24) =
      cexp (π * I / 24) * cexp (-(π * I * τ / 24)) * cexp (2 * π * I * τ / 24) := by
    simp only [← Complex.exp_add]
    congr 1
    ring
  have hs' : ‖-cexp (π * I * τ)‖ < 1 := by
    rw [norm_neg]
    exact UpperHalfPlane.norm_exp_pi_I_lt_one hτ
  rw [eta_eq_exp_mul_tprod, eta_eq_exp_mul_tprod, hs, he,
    tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul hs', neg_sq,
    ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq]
  simp only [one_sub_neg_pow_odd]
  ring

/-- **The square of the `S`-transformation of `η`**: `η(-1/τ)² = -i τ η(τ)²` on the upper
half-plane. -/
theorem eta_neg_one_div_sq {τ : ℂ} (hτ : 0 < τ.im) : η (-1 / τ) ^ 2 = -I * τ * η τ ^ 2 := by
  have h : η (-1 / τ) = (Complex.sqrt I)⁻¹ * (Complex.sqrt τ * η τ) := by
    simpa using _root_.ModularForm.eta_comp_eq_csqrt_I_inv hτ
  rw [h, mul_pow, mul_pow, inv_pow, Complex.sq_sqrt, Complex.sq_sqrt, inv_I]
  ring

/-- **The `S`-transformation of `η` at a positive real multiple**: for real `c > 0`,
`η(-1/(c τ)) η(τ) = √c η(c τ) η(-1/τ)` on the upper half-plane. The branch of `√(c τ)` in
Mathlib's `ModularForm.eta_comp_eq_csqrt_I_inv` is `√c √τ`, so no sign is lost. -/
theorem eta_neg_one_div_ofReal_mul_mul {c : ℝ} (hc : 0 < c) {τ : ℂ} (hτ : 0 < τ.im) :
    η (-1 / (c * τ)) * η τ = √c * η (c * τ) * η (-1 / τ) := by
  have hcτ : 0 < (c * τ : ℂ).im := by simpa [im_ofReal_mul] using mul_pos hc hτ
  have h₁ : η (-1 / (c * τ)) = (Complex.sqrt I)⁻¹ * (Complex.sqrt (c * τ) * η (c * τ)) := by
    simpa using _root_.ModularForm.eta_comp_eq_csqrt_I_inv hcτ
  have h₂ : η (-1 / τ) = (Complex.sqrt I)⁻¹ * (Complex.sqrt τ * η τ) := by
    simpa using _root_.ModularForm.eta_comp_eq_csqrt_I_inv hτ
  -- `Complex.sqrt` is the principal power `2⁻¹`, which splits across the real factor `c ≥ 0`.
  have hsqrt : Complex.sqrt (c * τ) = √c * Complex.sqrt τ :=
    (TauCeti.ofReal_mul_cpow hc.le τ 2⁻¹).trans
      (congrArg (· * Complex.sqrt τ) (Complex.sqrt_of_nonneg (zero_le_real.2 hc.le)))
  rw [h₁, h₂, hsqrt]
  ring

end TauCeti.ModularForm
