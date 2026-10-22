/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import TauCeti.Analysis.Complex.UpperHalfPlane.Exp

/-!
# The infinite q-Pochhammer products `∏_{n ≥ 1} (1 - qⁿ w)`

For `‖q‖ < 1` in a complete normed field, the product `∏_{n ≥ 1} (1 - qⁿ w)` (the q-Pochhammer
symbol `(q w; q)_∞`) converges absolutely. This file records its convergence, the shift identity
obtained by splitting off the first factor, and its nonvanishing. With `q = e^{2π i τ}` and `w`
depending continuously on `τ`, the product converges locally uniformly on the upper half-plane,
and is holomorphic there when `w` is entire.

## Main results

* `TauCeti.multipliable_one_sub_pow_mul`: for `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w)`
  converges.
* `TauCeti.tprod_one_sub_pow_mul_eq`: `∏_{n ≥ 1} (1 - qⁿ w) = (1 - q w) ∏_{n ≥ 1} (1 - qⁿ (q w))`.
* `TauCeti.tprod_one_sub_pow_mul_ne_zero`: the product is nonzero when all of its factors are.
* `TauCeti.hasProdLocallyUniformlyOn_one_sub_pow_mul`: for continuous `w`, the product
  `∏_{n ≥ 1} (1 - e^{2π i n τ} w(τ))` converges locally uniformly on the upper half-plane.
* `TauCeti.differentiableOn_tprod_one_sub_pow_mul`: for entire `w`, this product is holomorphic on
  the upper half-plane.
-/

public section

open Complex
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜]

/-- For `‖q‖ < 1` the norms `‖qⁿ⁺¹ w‖` are summable. -/
theorem summable_norm_pow_succ_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Summable fun n : ℕ ↦ ‖q ^ (n + 1) * w‖ := by
  simpa [norm_pow, pow_succ, mul_assoc] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (‖q‖ * ‖w‖)

variable [CompleteSpace 𝕜]

/-- For `‖q‖ < 1` the product `∏_{n ≥ 1} (1 - qⁿ w)` converges. -/
theorem multipliable_one_sub_pow_mul {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) * w :=
  multipliable_one_sub_of_summable (summable_norm_pow_succ_mul hq w)

/-- Shifting the product: `∏_{n ≥ 1} (1 - qⁿ w) = (1 - q w) ∏_{n ≥ 1} (1 - qⁿ (q w))`. -/
theorem tprod_one_sub_pow_mul_eq {q : 𝕜} (hq : ‖q‖ < 1) (w : 𝕜) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * w) = (1 - q * w) * ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)) := by
  rw [tprod_eq_zero_mul' (by simpa [pow_succ, mul_assoc] using
    multipliable_one_sub_pow_mul hq (q * w))]
  simp [pow_succ, mul_assoc]

/-- Shifting the product with an inverted argument:
`∏_{n ≥ 1} (1 - qⁿ (q w)⁻¹) = (1 - w⁻¹) ∏_{n ≥ 1} (1 - qⁿ w⁻¹)` for `q ≠ 0`. -/
theorem tprod_one_sub_pow_mul_inv_eq {q : 𝕜} (hq : ‖q‖ < 1) (hq₀ : q ≠ 0) (w : 𝕜) :
    ∏' n : ℕ, (1 - q ^ (n + 1) * (q * w)⁻¹) = (1 - w⁻¹) * ∏' n : ℕ, (1 - q ^ (n + 1) * w⁻¹) := by
  have h : ∀ n : ℕ, q ^ (n + 1) * (q * w)⁻¹ = q ^ n * w⁻¹ := fun n ↦ by
    rw [mul_inv, pow_succ]
    field_simp
  simp_rw [h]
  rw [tprod_eq_zero_mul' (f := fun n ↦ 1 - q ^ n * w⁻¹) (multipliable_one_sub_pow_mul hq w⁻¹)]
  simp

/-- If the factors `1 - qⁿ⁺¹ w` are nonzero, so is `∏_{n ≥ 1} (1 - qⁿ w)`. -/
theorem tprod_one_sub_pow_mul_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {w : 𝕜}
    (h : ∀ n : ℕ, 1 - q ^ (n + 1) * w ≠ 0) : ∏' n : ℕ, (1 - q ^ (n + 1) * w) ≠ 0 := by
  simp_rw [sub_eq_add_neg] at h ⊢
  exact tprod_one_add_ne_zero_of_summable h (by simpa using summable_norm_pow_succ_mul hq w)

end NormedField

section UpperHalfPlane

/-- For a continuous `w`, the product `∏_{n ≥ 1} (1 - qⁿ w(τ))` with `q = e^{2π i τ}` converges
locally uniformly on the upper half-plane. -/
theorem hasProdLocallyUniformlyOn_one_sub_pow_mul {w : ℂ → ℂ} (hw : Continuous w) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) τ ↦ 1 - cexp (2 * π * I * τ) ^ (n + 1) * w τ)
      (fun τ ↦ ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * w τ)) upperHalfPlaneSet := by
  simp_rw [sub_eq_add_neg]
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_upperHalfPlaneSet
    fun S hSH hS ↦ ?_
  obtain ⟨ρ, hρ₀, hρ₁, hρ⟩ := UpperHalfPlane.exists_norm_exp_two_pi_I_le_of_isCompact hS hSH
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hw.continuousOn
  refine ((summable_geometric_of_lt_one hρ₀ hρ₁).mul_left (ρ * M)).hasProdUniformlyOn_nat_one_add
    hS (.of_forall fun n τ hτ ↦ ?_) fun n ↦ by fun_prop
  calc ‖-(cexp (2 * π * I * τ) ^ (n + 1) * w τ)‖
      = ‖cexp (2 * π * I * τ)‖ ^ (n + 1) * ‖w τ‖ := by simp [norm_pow]
    _ ≤ ρ ^ (n + 1) * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hρ τ hτ) _) (hM τ hτ) (norm_nonneg _)
        (pow_nonneg hρ₀ _)
    _ = ρ * M * ρ ^ n := by ring

/-- For an entire `w`, the product `∏_{n ≥ 1} (1 - qⁿ w(τ))` with `q = e^{2π i τ}` is holomorphic
on the upper half-plane. -/
theorem differentiableOn_tprod_one_sub_pow_mul {w : ℂ → ℂ} (hw : Differentiable ℂ w) :
    DifferentiableOn ℂ (fun τ ↦ ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1) * w τ))
      upperHalfPlaneSet :=
  (hasProdLocallyUniformlyOn_one_sub_pow_mul hw.continuous).differentiableOn
    (.of_forall fun s ↦ by
      simpa [Finset.prod_fn] using DifferentiableOn.finsetProd fun _ _ ↦ by fun_prop)
    isOpen_upperHalfPlaneSet

end UpperHalfPlane

end TauCeti
