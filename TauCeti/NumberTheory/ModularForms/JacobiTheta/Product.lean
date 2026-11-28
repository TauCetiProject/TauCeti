/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.JacobiTripleProduct
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic

/-!
# Infinite-product formula, nonvanishing, and eta-quotient identity for `jacobiTheta`

Using the triple-product specialization `TauCeti.tsum_pow_sq`, the Euler-product splitting
`TauCeti.tprod_one_add_pow_eq_tprod_one_add_pow_odd_mul`, and the Dedekind eta product identities
`TauCeti.ModularForm.eta_eq_exp_mul_tprod` and `TauCeti.ModularForm.eta_two_mul`, this file
expresses Mathlib's `jacobiTheta` on the upper half-plane as a convergent nonvanishing infinite
product, deduces nonvanishing, and expresses `θ(2 τ)` as the eta quotient
`η(2 τ)⁵ / (η(τ)² η(4 τ)²)`.

## Main results

* `TauCeti.jacobiTheta_eq_tprod`: on `0 < τ.im`,
  `jacobiTheta τ = (∏' n, (1 + e^{π i (2n+1) τ})) ^ 2 * ∏' n, (1 - e^{2π i (n+1) τ})`.
* `TauCeti.jacobiTheta_ne_zero`, `TauCeti.jacobiTheta_two_mul_ne_zero`: `jacobiTheta τ ≠ 0`
  whenever `0 < τ.im`, and `jacobiTheta (2 * (z : ℂ)) ≠ 0` for `z : ℍ`.
* `TauCeti.jacobiTheta_two_mul_eq_eta_pow_div`:
  `jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2)` on `0 < τ.im`.

## References

* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. (2) **97** (1973),
  440–481, (1.10).
-/

public section

open Complex TauCeti.ModularForm
open scoped ModularForm Real UpperHalfPlane

namespace TauCeti

/-- **Infinite-product formula for `jacobiTheta`**: for `0 < τ.im`,
`jacobiTheta τ = (∏_{n ≥ 0} (1 + e^{π i (2n+1) τ}))² ∏_{n ≥ 1} (1 - e^{2π i n τ})`. -/
theorem jacobiTheta_eq_tprod {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ = (∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 2 *
      ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) := by
  have hs := UpperHalfPlane.norm_exp_pi_I_lt_one hτ
  have hθ : jacobiTheta τ = ∑' k : ℤ, cexp (π * I * τ) ^ (k ^ 2) := by
    refine tsum_congr fun k ↦ ?_
    rw [← Complex.exp_intCast_mul]
    congr 1
    push_cast
    ring
  rw [hθ, tsum_pow_sq hs, ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq]

/-- **`jacobiTheta` never vanishes on the upper half-plane**. -/
theorem jacobiTheta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiTheta τ ≠ 0 := by
  rw [jacobiTheta_eq_tprod hτ]
  have h1 : ∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1)) ≠ 0 := by
    have h := tprod_one_sub_pow_odd_ne_zero (q := -cexp (π * I * τ))
      (by simpa [norm_neg] using UpperHalfPlane.norm_exp_pi_I_lt_one hτ)
    rwa [tprod_congr (one_sub_neg_pow_odd (cexp (π * I * τ)))] at h
  have h2 : ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) ≠ 0 :=
    tprod_one_sub_pow_ne_zero (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩)
  exact mul_ne_zero (pow_ne_zero 2 h1) h2

/-- `jacobiTheta (2 * (z : ℂ))` never vanishes on the upper half-plane. -/
theorem jacobiTheta_two_mul_ne_zero (z : ℍ) : jacobiTheta (2 * (z : ℂ)) ≠ 0 :=
  jacobiTheta_ne_zero (by simpa using mul_pos two_pos z.im_pos)

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

end TauCeti
