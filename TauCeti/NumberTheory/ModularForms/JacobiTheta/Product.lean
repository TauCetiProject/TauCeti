/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import TauCeti.Analysis.SpecialFunctions.QPochhammer
public import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.JacobiTripleProduct
import TauCeti.Data.Int.MulPred

/-!
# Jacobi's product formula and nonvanishing of the theta function

Specializing Jacobi's triple product identity (`TauCeti.hasSum_qTheta_mul_tprod_one_sub_pow`) to
nome `q²` and parameter `q` (and, after replacing `q` with `-q`, to nome `q²` and parameter `-q`)
yields the product expansions of the alternating and ordinary quadratic theta series over any
complete normed field for `‖q‖ < 1`:
* `∑_{k ∈ ℤ} (-1)ᵏ q^{k²} = ∏_{n ≥ 1} (1 - qⁿ) / (1 + qⁿ)`
  `= (∏_{n ≥ 0} (1 - q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`;
* `∑_{k ∈ ℤ} q^{k²} = (∏_{n ≥ 0} (1 + q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`.

Since each factor `∏_{n ≥ 0} (1 ± q^{2n+1})` and `∏_{n ≥ 1} (1 - q^{2n})` is nonzero for
`‖q‖ < 1`, neither series vanishes. Over `ℂ`, setting `q = e^{π i τ}` on the upper half-plane
gives the infinite product formula and nonvanishing of Mathlib's `jacobiTheta`, together with the
eta quotient identity `θ(2τ) = η(2τ)⁵ / (η(τ)² η(4τ)²)` for `τ` in the upper half-plane.

## Main results

* `TauCeti.jacobi_product_specialization`:
  `∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) = ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1))`
  for `‖q‖ < 1`.
* `TauCeti.tsum_zpow_sq`, `TauCeti.tsum_zpow_sq_ne_zero`: the product formula and nonvanishing of
  `∑' k : ℤ, q ^ (k ^ 2)` for `‖q‖ < 1`.
* `TauCeti.jacobiTheta_eq_tprod`: the infinite product expansion of `jacobiTheta τ` on the upper
  half-plane.
* `TauCeti.jacobiTheta_ne_zero`: `jacobiTheta τ ≠ 0` whenever `0 < τ.im`.
* `TauCeti.jacobiTheta_two_mul_eq_eta_div`:
  `jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2)` for `0 < τ.im`.

## References

* C. G. J. Jacobi, *Fundamenta Nova Theoriae Functionum Ellipticarum* (1829), §61.
* G. Gasper, M. Rahman, *Basic Hypergeometric Series*, 2nd ed., Cambridge University Press, 2004,
  §1.6.
* G. Shimura, *On modular forms of half integral weight*, Ann. of Math. **97** (1973), 440–481.
-/

public section

open Complex
open scoped ModularForm Real

namespace TauCeti

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Gauss's product identity** for the alternating theta series over any complete normed field:
for `‖q‖ < 1`,
`∑_{k ∈ ℤ} (-1)ᵏ q^{k²} = (∏_{n ≥ 0} (1 - q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`. -/
theorem hasSum_neg_one_pow_mul_zpow_sq_eq_tprod {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ ↦ (-1) ^ k * q ^ (k ^ 2))
      ((∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) := by
  rcases eq_or_ne q 0 with rfl | hq₀
  · have h1 : (fun n : ℕ ↦ (1 : 𝕜) - 0 ^ (2 * n + 1)) = fun _ ↦ 1 := by
      ext n
      simp
    have h2 : (fun n : ℕ ↦ (1 : 𝕜) - ((0 : 𝕜) ^ 2) ^ (n + 1)) = fun _ ↦ 1 := by
      ext n
      simp
    rw [h1, h2, tprod_one, one_pow, one_mul]
    have hsum : HasSum (fun k : ℤ ↦ (-1 : 𝕜) ^ k * (0 : 𝕜) ^ (k ^ 2))
        ((-1 : 𝕜) ^ (0 : ℤ) * (0 : 𝕜) ^ ((0 : ℤ) ^ 2)) :=
      hasSum_single (0 : ℤ) fun k hk ↦ mul_eq_zero_of_right _ (zero_zpow _ (pow_ne_zero 2 hk))
    simpa using hsum
  have h := hasSum_qTheta_mul_tprod_one_sub_pow (norm_pow_lt_one hq two_ne_zero) hq₀
  rw [qTheta_sq_self hq] at h
  refine h.congr_fun fun k ↦ ?_
  have hmul : (q ^ 2) ^ (k * (k - 1) / 2) * q ^ k = q ^ (k ^ 2) := by
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hq₀, Nat.cast_ofNat,
      Int.two_mul_mul_sub_one_ediv_two]
    congr 1
    ring
  rw [mul_assoc, hmul]

/-- For `‖q‖ < 1` in a complete normed field, the ratio product
`∏_{n ≥ 1} (1 - qⁿ) / (1 + qⁿ)` equals
`(∏_{n ≥ 0} (1 - q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`. -/
theorem tprod_one_sub_div_one_add_pow {q : 𝕜} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) := by
  have hm₁ : Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) := by
    simpa using multipliable_one_sub_pow_mul hq 1
  have hm₂ : Multipliable fun n : ℕ ↦ 1 + q ^ (n + 1) := multipliable_one_add_pow hq
  have heuler := tprod_one_add_pow_mul_tprod_one_sub_pow_odd hq
  have hP0 : ∏' n : ℕ, (1 + q ^ (n + 1)) ≠ 0 := left_ne_zero_of_mul_eq_one heuler
  rw [hm₁.tprod_div₀ hm₂ hP0, div_eq_mul_inv, inv_eq_of_mul_eq_one_right heuler,
    tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul hq]
  ring

/-- For `‖q‖ < 1` in a complete normed field,
`∏_{n ≥ 1} (1 - qⁿ) / (1 + qⁿ) = (∏_{n ≥ 1} (1 - qⁿ)) /` `∏_{n ≥ 1} (1 + qⁿ)`. -/
theorem tprod_one_sub_div_one_add_pow_eq_div {q : 𝕜} (hq : ‖q‖ < 1) :
    ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1)) =
      (∏' n : ℕ, (1 - q ^ (n + 1))) / ∏' n : ℕ, (1 + q ^ (n + 1)) := by
  have hm₁ : Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) := by
    simpa using multipliable_one_sub_pow_mul hq 1
  have hP0 : ∏' n : ℕ, (1 + q ^ (n + 1)) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (tprod_one_add_pow_mul_tprod_one_sub_pow_odd hq)
  exact hm₁.tprod_div₀ (multipliable_one_add_pow hq) hP0

/-- **Jacobi's product formula** in `HasSum` form: for `‖q‖ < 1`, the series
`∑_{k ∈ ℤ} (-1)ᵏ q^{k²}` has sum `∏_{n ≥ 1} (1 - qⁿ) / (1 + qⁿ)`. -/
theorem hasSum_neg_one_pow_mul_zpow_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ ↦ (-1) ^ k * q ^ (k ^ 2))
      (∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1))) := by
  rw [tprod_one_sub_div_one_add_pow hq]
  exact hasSum_neg_one_pow_mul_zpow_sq_eq_tprod hq

/-- **Jacobi's product specialization**: for `‖q‖ < 1` in a complete normed field,
`∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) = ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1))`. -/
theorem jacobi_product_specialization {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) = ∏' n : ℕ, (1 - q ^ (n + 1)) / (1 + q ^ (n + 1)) :=
  (hasSum_neg_one_pow_mul_zpow_sq hq).tsum_eq

/-- For `‖q‖ < 1`, the alternating quadratic theta series `∑_{k ∈ ℤ} (-1)ᵏ q^{k²}`
does not vanish. -/
theorem jacobi_product_specialization_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, (-1) ^ k * q ^ (k ^ 2) ≠ 0 := by
  rw [(hasSum_neg_one_pow_mul_zpow_sq_eq_tprod hq).tsum_eq]
  exact mul_ne_zero (pow_ne_zero 2 (tprod_one_sub_pow_odd_ne_zero hq))
    (tprod_one_sub_pow_ne_zero (norm_pow_lt_one hq two_ne_zero))

/-- **Gauss's product identity** for the theta series `∑_{k ∈ ℤ} q^{k²}`: for `‖q‖ < 1`,
`∑_{k ∈ ℤ} q^{k²}` has sum `(∏_{n ≥ 0} (1 + q^{2n+1}))² ∏_{n ≥ 1} (1 - q^{2n})`. -/
theorem hasSum_zpow_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun k : ℤ ↦ q ^ (k ^ 2))
      ((∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))) := by
  have h := hasSum_neg_one_pow_mul_zpow_sq_eq_tprod (q := -q) (by rwa [norm_neg])
  simp only [one_sub_neg_pow_odd, neg_sq] at h
  refine h.congr_fun fun k ↦ ?_
  obtain ⟨m, hm⟩ := Int.even_mul_pred_self (-k)
  have hpow : k ^ 2 = ((k.natAbs ^ 2 : ℕ) : ℤ) := by
    rw [Int.natCast_pow, Int.natCast_natAbs, sq_abs]
  rw [hpow, zpow_natCast, zpow_natCast, neg_pow, ← mul_assoc, ← zpow_natCast (-1 : 𝕜),
    ← zpow_add₀ (by norm_num : (-1 : 𝕜) ≠ 0), ← hpow]
  have heven : k + k ^ 2 = 2 * m := by linear_combination hm
  rw [heven, zpow_mul, zpow_ofNat, neg_one_sq, one_zpow, one_mul]

/-- For `‖q‖ < 1`,
`∑' k : ℤ, q ^ (k ^ 2) =`
`(∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1))`. -/
theorem tsum_zpow_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, q ^ (k ^ 2) =
      (∏' n : ℕ, (1 + q ^ (2 * n + 1))) ^ 2 * ∏' n : ℕ, (1 - (q ^ 2) ^ (n + 1)) :=
  (hasSum_zpow_sq hq).tsum_eq

/-- For `‖q‖ < 1` in a complete normed field, the quadratic theta series
`∑' k : ℤ, q ^ (k ^ 2)` does not vanish. -/
theorem tsum_zpow_sq_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) :
    ∑' k : ℤ, q ^ (k ^ 2) ≠ 0 := by
  rw [tsum_zpow_sq hq]
  have hodd : ∏' n : ℕ, (1 + q ^ (2 * n + 1)) ≠ 0 := by
    simpa only [one_sub_neg_pow_odd] using
      tprod_one_sub_pow_odd_ne_zero (q := -q) (by rwa [norm_neg])
  exact mul_ne_zero (pow_ne_zero 2 hodd)
    (tprod_one_sub_pow_ne_zero (norm_pow_lt_one hq two_ne_zero))

end NormedField

section Complex

/-- **Jacobi's product formula** for `jacobiTheta` on the upper half-plane: with `s = e^{π i τ}`
and `q = e^{2π i τ}`,
`θ(τ) = (∏_{n ≥ 0} (1 + s^{2n+1}))² ∏_{n ≥ 1} (1 - qⁿ)`. -/
theorem jacobiTheta_eq_tprod {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ =
      (∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 2 *
        ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) := by
  have hterm (k : ℤ) : cexp (π * I * (k : ℂ) ^ 2 * τ) = cexp (π * I * τ) ^ (k ^ 2) := by
    rw [← Complex.exp_intCast_mul]
    congr 1
    push_cast
    ring
  rw [jacobiTheta, tsum_congr hterm, tsum_zpow_sq (UpperHalfPlane.norm_exp_pi_I_lt_one hτ),
    ← UpperHalfPlane.exp_two_pi_I_eq_exp_pi_I_sq]

/-- The Jacobi theta function `jacobiTheta` does not vanish on the upper half-plane. -/
theorem jacobiTheta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : jacobiTheta τ ≠ 0 := by
  have hterm (k : ℤ) : cexp (π * I * (k : ℂ) ^ 2 * τ) = cexp (π * I * τ) ^ (k ^ 2) := by
    rw [← Complex.exp_intCast_mul]
    congr 1
    push_cast
    ring
  rw [jacobiTheta, tsum_congr hterm]
  exact tsum_zpow_sq_ne_zero (UpperHalfPlane.norm_exp_pi_I_lt_one hτ)

/-- **Theta as a Dedekind eta quotient**: for `τ` in the upper half-plane,
`θ(2τ) = η(2τ)⁵ / (η(τ)² η(4τ)²)`. -/
theorem jacobiTheta_two_mul_eq_eta_div {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta (2 * τ) = η (2 * τ) ^ 5 / (η τ ^ 2 * η (4 * τ) ^ 2) := by
  have h2τ : 0 < (2 * τ).im := by simpa using mul_pos two_pos hτ
  have h4τ : 0 < (4 * τ).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 4) hτ
  have hq : ‖cexp (2 * π * I * τ)‖ < 1 := by
    simpa [mul_assoc, mul_left_comm] using UpperHalfPlane.norm_exp_pi_I_lt_one h2τ
  have heq1 : cexp (2 * π * I * (2 * τ)) = cexp (2 * π * I * τ) ^ 2 := by
    rw [← Complex.exp_natCast_mul]
    congr 1
    push_cast
    ring
  have heq2 : cexp (π * I * (2 * τ)) = cexp (2 * π * I * τ) := by
    congr 1
    ring
  have hsplit : ∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (n + 1)) =
      (∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (2 * n + 1))) *
        ∏' n : ℕ, (1 + (cexp (2 * π * I * τ) ^ 2) ^ (n + 1)) := by
    have hm1 : Multipliable fun n : ℕ ↦ 1 + cexp (2 * π * I * τ) ^ (2 * n + 1) :=
      multipliable_one_add_pow_odd hq
    have hm2 : Multipliable fun n : ℕ ↦ 1 + (cexp (2 * π * I * τ) ^ 2) ^ (n + 1) :=
      multipliable_one_add_pow (norm_pow_lt_one hq two_ne_zero)
    rw [← tprod_even_mul_odd hm1 (by simpa [← pow_mul, mul_add] using hm2)]
    simp [← pow_mul, mul_add]
  have hθ : jacobiTheta (2 * τ) =
      (∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (2 * n + 1))) ^ 2 *
        ∏' n : ℕ, (1 - (cexp (2 * π * I * τ) ^ 2) ^ (n + 1)) := by
    rw [jacobiTheta_eq_tprod h2τ, heq2, heq1]
  have hη2 : η (2 * τ) = cexp (π * I * τ / 12) * η τ *
      ((∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (2 * n + 1))) *
        ∏' n : ℕ, (1 + (cexp (2 * π * I * τ) ^ 2) ^ (n + 1))) := by
    rw [ModularForm.eta_two_mul hτ, hsplit]
  have hη4 : η (4 * τ) = cexp (π * I * τ / 6) * η (2 * τ) *
      ∏' n : ℕ, (1 + (cexp (2 * π * I * τ) ^ 2) ^ (n + 1)) := by
    have h4 : (4 : ℂ) * τ = 2 * (2 * τ) := by ring
    rw [h4, ModularForm.eta_two_mul h2τ, heq1]
    congr 2
    congr 1
    ring
  have hη2_prod : η (2 * τ) = cexp (π * I * τ / 6) *
      ∏' n : ℕ, (1 - (cexp (2 * π * I * τ) ^ 2) ^ (n + 1)) := by
    rw [ModularForm.eta_eq_exp_mul_tprod, heq1]
    congr 1
    congr 1
    ring
  have hexp : cexp (π * I * τ / 12) ^ 2 = cexp (π * I * τ / 6) := by
    rw [← Complex.exp_natCast_mul]
    congr 1
    push_cast
    ring
  have hden0 : η τ ^ 2 * η (4 * τ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (_root_.ModularForm.eta_ne_zero hτ))
      (pow_ne_zero 2 (_root_.ModularForm.eta_ne_zero h4τ))
  refine eq_div_of_mul_eq hden0 ?_
  calc
    jacobiTheta (2 * τ) * (η τ ^ 2 * η (4 * τ) ^ 2)
      = ((∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (2 * n + 1))) ^ 2 *
          ∏' n : ℕ, (1 - (cexp (2 * π * I * τ) ^ 2) ^ (n + 1))) *
          (η τ ^ 2 * (cexp (π * I * τ / 6) * η (2 * τ) *
            ∏' n : ℕ, (1 + (cexp (2 * π * I * τ) ^ 2) ^ (n + 1))) ^ 2) := by
          rw [hθ, hη4]
    _ = ((cexp (π * I * τ / 12) * η τ *
          ((∏' n : ℕ, (1 + cexp (2 * π * I * τ) ^ (2 * n + 1))) *
            ∏' n : ℕ, (1 + (cexp (2 * π * I * τ) ^ 2) ^ (n + 1)))) ^ 2 *
          η (2 * τ) ^ 2) *
          (cexp (π * I * τ / 6) *
            ∏' n : ℕ, (1 - (cexp (2 * π * I * τ) ^ 2) ^ (n + 1))) := by
          rw [← hexp]
          ring
    _ = η (2 * τ) ^ 5 := by
          rw [← hη2, ← hη2_prod]
          ring

end Complex

end TauCeti
