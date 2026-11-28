/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Quotient.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic
import TauCeti.NumberTheory.ModularForms.JacobiTheta.Product

/-!
# Eta-quotient representation of `jacobiTheta (2 * τ)`

Using the infinite-product formula `TauCeti.jacobiTheta_eq_tprod`, the Euler-product splitting
`TauCeti.tprod_one_add_pow_eq_tprod_one_add_pow_odd_mul`, and the Dedekind eta product identities
`TauCeti.ModularForm.eta_eq_exp_mul_tprod` and `TauCeti.ModularForm.eta_two_mul`, this file
expresses `θ(2 τ)` as `η(2 τ)⁵ / (η(τ)² η(4 τ)²)` and packages it as the level-`4` eta quotient
`etaQuotient 4 thetaExpVec τ`.

## Main definitions

* `TauCeti.thetaExpVec`: the level-`4` eta-quotient exponent vector (`1 ↦ -2`, `2 ↦ 5`, `4 ↦ -2`)
  representing `τ ↦ θ(2 τ)`.

## Main results

* `TauCeti.jacobiTheta_two_mul_eq_eta_pow_div`:
  `jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2)` on `0 < τ.im`.
* `TauCeti.thetaExpVec_eq_zero_iff`: `thetaExpVec δ = 0 ↔ δ ∉ (4 : ℕ).divisors`.
* `TauCeti.sum_divisors_four_thetaExpVec`: `∑ δ ∈ (4 : ℕ).divisors, thetaExpVec δ = 1`.
* `TauCeti.prod_divisors_four_thetaExpVec`: expanding `∏ δ ∈ (4 : ℕ).divisors, f δ ^ thetaExpVec δ`.
* `TauCeti.jacobiTheta_two_mul_eq_etaQuotient`:
  `jacobiTheta (2 * τ) = etaQuotient 4 thetaExpVec τ` on `0 < τ.im`.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. (2) **97** (1973),
  440–481, (1.10).
-/

public section

open Complex TauCeti.ModularForm
open scoped ModularForm Real UpperHalfPlane

namespace TauCeti

/-- **Eta-quotient identity for `jacobiTheta (2 * τ)`**: on `0 < τ.im`,
`jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2)`. -/
theorem jacobiTheta_two_mul_eq_eta_pow_div {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2) := by
  have h2τ : 0 < (2 * τ).im := by simpa using mul_pos two_pos hτ
  have h4τ : 0 < (4 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 4) hτ
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have hη4 : η (4 * τ) ≠ 0 := _root_.ModularForm.eta_ne_zero h4τ
  refine (eq_div_iff (mul_ne_zero (pow_ne_zero 2 hη) (pow_ne_zero 2 hη4))).mpr ?_
  set q : ℂ := cexp (2 * π * I * τ)
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩
  have h2π : cexp (π * I * (2 * τ)) = q := by congr 1; ring
  have h4π : cexp (2 * π * I * (2 * τ)) = q ^ 2 := by
    rw [UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq (2 * τ), h2π]
  have hA : (∏' n : ℕ, (1 + q ^ (2 * n + 1))) * (∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) =
      ∏' n : ℕ, (1 + q ^ (n + 1)) := by
    rw [tprod_one_add_pow_eq_tprod_one_add_pow_odd_mul hq, mul_comm]
  have hη2_prod : η (2 * τ) = cexp (π * I * τ / 6) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
    rw [eta_eq_exp_mul_tprod, h4π]
    congr 2
    ring
  have hη2_tau : η (2 * τ) = cexp (π * I * τ / 12) * η τ * ∏' n : ℕ, (1 + q ^ (n + 1)) :=
    eta_two_mul hτ
  have h22τ : 2 * (2 * τ) = 4 * τ := by ring
  have hη4_tau : η (4 * τ) = cexp (π * I * (2 * τ) / 12) * η (2 * τ) *
      ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)) := by
    simpa [h22τ, h4π] using eta_two_mul h2τ
  have hexp : cexp (π * I * (2 * τ) / 12) ^ 2 =
      cexp (π * I * τ / 6) * cexp (π * I * τ / 12) ^ 2 := by
    rw [← Complex.exp_natCast_mul, ← Complex.exp_natCast_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hθ : jacobiTheta (2 * τ) = (∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 *
      ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
    rw [jacobiTheta_eq_tprod h2τ, h2π, h4π]
  calc jacobiTheta (2 * τ) * (η τ ^ 2 * η (4 * τ) ^ 2)
      = ((∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
          (η τ ^ 2 * (cexp (π * I * (2 * τ) / 12) * η (2 * τ) *
            ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))) ^ 2) := by rw [hθ, hη4_tau]
    _ = (cexp (π * I * τ / 6) * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) *
          (cexp (π * I * τ / 12) * η τ * ((∏' n : ℕ, (1 + q ^ (2 * n + 1))) *
            ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1)))) ^ 2 * η (2 * τ) ^ 2 := by
          rw [mul_pow, mul_pow, hexp]
          ring
    _ = η (2 * τ) * η (2 * τ) ^ 2 * η (2 * τ) ^ 2 := by
          rw [hA, ← hη2_prod, ← hη2_tau]
    _ = η (2 * τ) ^ 5 := by ring

/-- The exponent vector of the level-`4` eta quotient representing `τ ↦ θ(2 τ)`, sending
`1 ↦ -2`, `2 ↦ 5`, `4 ↦ -2`, and all other natural numbers to `0`. -/
def thetaExpVec : ℕ → ℤ :=
  fun δ ↦ if δ = 2 then 5 else if δ = 1 ∨ δ = 4 then -2 else 0

/-- Defining formula for `thetaExpVec`. -/
theorem thetaExpVec_def (δ : ℕ) :
    thetaExpVec δ = if δ = 2 then 5 else if δ = 1 ∨ δ = 4 then -2 else 0 :=
  (rfl)

@[simp]
theorem thetaExpVec_one : thetaExpVec 1 = -2 := by decide

@[simp]
theorem thetaExpVec_two : thetaExpVec 2 = 5 := by decide

@[simp]
theorem thetaExpVec_four : thetaExpVec 4 = -2 := by decide

/-- `thetaExpVec` vanishes outside the divisors `{1, 2, 4}` of `4`. -/
@[simp]
theorem thetaExpVec_eq_zero_iff (δ : ℕ) : thetaExpVec δ = 0 ↔ δ ∉ (4 : ℕ).divisors := by
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [hdiv, thetaExpVec_def]
  rcases eq_or_ne δ 2 with rfl | h2; · simp
  rcases eq_or_ne δ 1 with rfl | h1; · simp
  rcases eq_or_ne δ 4 with rfl | h4; · simp
  simp [h1, h2, h4]

/-- The exponents of `thetaExpVec` over the divisors of `4` sum to `1` (weight `1/2`). -/
theorem sum_divisors_four_thetaExpVec : ∑ δ ∈ (4 : ℕ).divisors, thetaExpVec δ = 1 := by
  decide

/-- Expanding a `thetaExpVec`-weighted product over `4.divisors` into its three factors at
`1`, `2`, and `4`. -/
theorem prod_divisors_four_thetaExpVec {G : Type*} [DivisionCommMonoid G] (f : ℕ → G) :
    ∏ δ ∈ (4 : ℕ).divisors, f δ ^ thetaExpVec δ =
      f 1 ^ (-2 : ℤ) * f 2 ^ (5 : ℤ) * f 4 ^ (-2 : ℤ) := by
  have hdiv : (4 : ℕ).divisors = {1, 2, 4} := by decide
  rw [hdiv, Finset.prod_insert (by decide : (1 : ℕ) ∉ ({2, 4} : Finset ℕ)),
    Finset.prod_insert (by decide : (2 : ℕ) ∉ ({4} : Finset ℕ)), Finset.prod_singleton,
    thetaExpVec_one, thetaExpVec_two, thetaExpVec_four, ← mul_assoc]

/-- **Eta-quotient form of `jacobiTheta (2 * τ)`**: on `0 < τ.im`, `jacobiTheta (2 * τ)` equals
the level-`4` eta quotient `etaQuotient 4 thetaExpVec τ`. -/
theorem jacobiTheta_two_mul_eq_etaQuotient {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (2 * τ) = etaQuotient 4 thetaExpVec τ := by
  rw [jacobiTheta_two_mul_eq_eta_pow_div hτ, etaQuotient_apply, prod_divisors_four_thetaExpVec]
  norm_num [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end TauCeti
