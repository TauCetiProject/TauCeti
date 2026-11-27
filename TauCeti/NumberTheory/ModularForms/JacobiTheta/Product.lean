/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.JacobiTripleProduct
import TauCeti.Analysis.SpecialFunctions.QPochhammer

/-!
# Jacobi's product formula and nonvanishing of the theta function

Specializing the field-general quadratic theta product formula (`TauCeti.tsum_zpow_sq`) and
nonvanishing theorem (`TauCeti.tsum_zpow_sq_ne_zero`) from
`TauCeti.Analysis.SpecialFunctions.JacobiTripleProduct` to `q = e^{π i τ}` on the upper
half-plane gives the infinite product formula and nonvanishing of Mathlib's `jacobiTheta`, together
with the eta quotient identity `θ(2τ) = η(2τ)⁵ / (η(τ)² η(4τ)²)` for `τ` in the upper
half-plane.

## Main results

* `TauCeti.jacobiTheta_eq_tsum_zpow_sq`: `jacobiTheta τ` written as
  `∑' k : ℤ, (e^{π i τ}) ^ (k ^ 2)`.
* `TauCeti.jacobiTheta_eq_tprod`: the infinite product expansion of `jacobiTheta τ` on the upper
  half-plane.
* `TauCeti.jacobiTheta_ne_zero`: `jacobiTheta τ ≠ 0` whenever `0 < τ.im`.
* `TauCeti.jacobiTheta_two_mul_eq_eta_div`:
  `jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2)` for `0 < τ.im`.

## References

* C. G. J. Jacobi, *Fundamenta Nova Theoriae Functionum Ellipticarum* (1829), §61.
* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. **97** (1973), 440–481.
-/

public section

open Complex
open scoped ModularForm Real

namespace TauCeti


/-- `jacobiTheta τ` written as the quadratic nome series `∑' k : ℤ, (e^{π i τ}) ^ (k ^ 2)`. -/
theorem jacobiTheta_eq_tsum_zpow_sq (τ : ℂ) :
    jacobiTheta τ = ∑' k : ℤ, cexp (π * I * τ) ^ (k ^ 2) := by
  refine tsum_congr fun k ↦ ?_
  rw [← Complex.exp_intCast_mul]
  congr 1
  push_cast
  ring

/-- **Jacobi's product formula** for `jacobiTheta` on the upper half-plane: with `s = e^{π i τ}`
and `q = e^{2π i τ}`,
`θ(τ) = (∏_{n ≥ 0} (1 + s^{2n+1}))² ∏_{n ≥ 1} (1 - qⁿ)`. -/
theorem jacobiTheta_eq_tprod {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ =
      (∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 2 *
        ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) := by
  rw [jacobiTheta_eq_tsum_zpow_sq, tsum_zpow_sq (UpperHalfPlane.norm_exp_pi_I_lt_one hτ),
    ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq]

/-- The Jacobi theta function `jacobiTheta` does not vanish on the upper half-plane. -/
theorem jacobiTheta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiTheta τ ≠ 0 := by
  rw [jacobiTheta_eq_tsum_zpow_sq]
  exact tsum_zpow_sq_ne_zero (UpperHalfPlane.norm_exp_pi_I_lt_one hτ)

/-- **Theta as a Dedekind eta quotient**: for `τ` in the upper half-plane,
`θ(2τ) = η(2τ)⁵ / (η(τ)² η(4τ)²)`. -/
theorem jacobiTheta_two_mul_eq_eta_div {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2) := by
  set s := cexp (2 * π * I * τ)
  have h2τ : 0 < (2 * τ).im := by simpa using mul_pos two_pos hτ
  have h4τ : 0 < (4 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 4) hτ
  have hs : ‖s‖ < 1 := by
    simpa [s, mul_assoc, mul_left_comm] using UpperHalfPlane.norm_exp_pi_I_lt_one h2τ
  have hs2 : cexp (2 * π * I * (2 * τ)) = s ^ 2 := by
    simpa [s, show π * I * (2 * τ) = 2 * π * I * τ by ring] using
      UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq (2 * τ)
  have hsplit : ∏' n : ℕ, (1 + s ^ (n + 1)) =
      (∏' n : ℕ, (1 + s ^ (2 * n + 1))) * ∏' n : ℕ, (1 + (s ^ 2) ^ (n + 1)) := by
    have hm1 := multipliable_one_add_pow_odd hs
    have hm2 := multipliable_one_add_pow (norm_pow_lt_one hs two_ne_zero)
    rw [← tprod_even_mul_odd hm1 (by simpa [← pow_mul, mul_add] using hm2)]
    simp [← pow_mul, mul_add]
  have hθ : jacobiTheta (2 * τ) =
      (∏' n : ℕ, (1 + s ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (s ^ 2) ^ (n + 1)) := by
    rw [jacobiTheta_eq_tprod h2τ, show π * I * (2 * τ) = 2 * π * I * τ by ring, hs2]
  have hη2 : η (2 * τ) = cexp (π * I * τ / 12) * η τ *
      ((∏' n : ℕ, (1 + s ^ (2 * n + 1))) * ∏' n : ℕ, (1 + (s ^ 2) ^ (n + 1))) := by
    rw [ModularForm.eta_two_mul hτ, hsplit]
  have hη4 : η (4 * τ) =
      cexp (π * I * τ / 6) * η (2 * τ) * ∏' n : ℕ, (1 + (s ^ 2) ^ (n + 1)) := by
    rw [show (4 : ℂ) * τ = 2 * (2 * τ) by ring, ModularForm.eta_two_mul h2τ, hs2,
      show π * I * (2 * τ) / 12 = π * I * τ / 6 by ring]
  have hη2_prod : η (2 * τ) = cexp (π * I * τ / 6) * ∏' n : ℕ, (1 - (s ^ 2) ^ (n + 1)) := by
    rw [ModularForm.eta_eq_exp_mul_tprod, hs2,
      show 2 * π * I * (2 * τ) / 24 = π * I * τ / 6 by ring]
  have hexp : cexp (π * I * τ / 12) ^ 2 = cexp (π * I * τ / 6) := by
    rw [← Complex.exp_natCast_mul]; congr 1; push_cast; ring
  refine eq_div_of_mul_eq (mul_ne_zero (pow_ne_zero 2 (_root_.ModularForm.eta_ne_zero hτ))
    (pow_ne_zero 2 (_root_.ModularForm.eta_ne_zero h4τ))) ?_
  calc
    jacobiTheta (2 * τ) * (η τ ^ 2 * η (4 * τ) ^ 2)
      = ((∏' n : ℕ, (1 + s ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (s ^ 2) ^ (n + 1))) *
          (η τ ^ 2 * (cexp (π * I * τ / 6) * η (2 * τ) *
            ∏' n : ℕ, (1 + (s ^ 2) ^ (n + 1))) ^ 2) := by rw [hθ, hη4]
    _ = ((cexp (π * I * τ / 12) * η τ * ((∏' n : ℕ, (1 + s ^ (2 * n + 1))) *
            ∏' n : ℕ, (1 + (s ^ 2) ^ (n + 1)))) ^ 2 * η (2 * τ) ^ 2) *
          (cexp (π * I * τ / 6) * ∏' n : ℕ, (1 - (s ^ 2) ^ (n + 1))) := by rw [← hexp]; ring
    _ = η (2 * τ) ^ 5 := by rw [← hη2, ← hη2_prod]; ring

end TauCeti
