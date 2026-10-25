/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The level-two Siegel functions as eta quotients

The three Siegel functions of level two, `g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}` and
`g₂ = g_{(1/2, 1/2)}`, are quotients of values of Mathlib's Dedekind eta function
`η = ModularForm.eta`, with exact constants:
`g₀(τ) = 2 i (η(2τ) / η(τ))²`, `g₁(τ) = -(η(τ/2) / η(τ))²` and
`g₂(τ) = -e^{-π i / 3} (η((τ + 1)/2) / η(τ))²`.
These follow from the product expansions of `g₀, g₁, g₂` and the product identities for `η` at
`2τ`, `τ/2` and `(τ + 1)/2`.

The transformation of `η` under `S : τ ↦ -1/τ` then gives the transformation of the level-two
Siegel functions under `S`, with exact roots of unity:
`g₀(-1/τ) = -i g₁(τ)`, `g₁(-1/τ) = i g₀(τ)` and `g₂(-1/τ) = g₂(τ)`; the last follows from the first
two and `g₀ g₁ g₂ = 2 ζ₈`. Together with the translations `τ ↦ τ + 1`
(`siegelFunction_zero_half_apply_add_one` and its two companions) this shows that `SL₂(ℤ)`
permutes the twelfth powers `g₀¹², g₁¹², g₂¹²`: `S` exchanges `g₀¹²` and `g₁¹²` and fixes `g₂¹²`,
while `T` fixes `g₀¹²` and exchanges `g₁¹²` and `g₂¹²`. Equivalently, the monic cubic
`(X - g₀¹²)(X - g₁¹²)(X - g₂¹²)` is invariant under `SL₂(ℤ)`: its coefficients are
`SL₂(ℤ)`-invariant holomorphic functions on the upper half-plane. This is the input for expressing
the cube root `γ₂` of `j` through the level-two Siegel functions.

## Main results

* `TauCeti.ModularForm.siegelFunction_zero_half_eq_eta`,
  `TauCeti.ModularForm.siegelFunction_half_zero_eq_eta`,
  `TauCeti.ModularForm.siegelFunction_half_half_eq_eta`: `g₀, g₁, g₂` as eta quotients.
* `TauCeti.ModularForm.siegelFunction_zero_half_apply_neg_one_div`,
  `TauCeti.ModularForm.siegelFunction_half_zero_apply_neg_one_div`,
  `TauCeti.ModularForm.siegelFunction_half_half_apply_neg_one_div`: the transformation of
  `g₀, g₁, g₂` under `τ ↦ -1/τ`.
* `TauCeti.ModularForm.prod_X_sub_C_siegelFunction_pow_twelve_smul`: the cubic with roots
  `g₀¹², g₁¹², g₂¹²` is invariant under `SL₂(ℤ)`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber's functions `𝔣, 𝔣₁, 𝔣₂` as eta quotients and
  their transformations under `SL₂(ℤ)`).
* D. S. Kubert, S. Lang, *Modular Units*, Chapter 2, §1.
-/

public section

open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### Eta quotients -/

/-- `g_{(0, 1/2)}(τ) = 2 i (η(2τ) / η(τ))²` on the upper half-plane. -/
theorem siegelFunction_zero_half_eq_eta {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] τ = 2 * I * (η (2 * τ) / η τ) ^ 2 := by
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have he : cexp (π * I * τ / 6) = cexp (π * I * τ / 12) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [siegelFunction_zero_half hτ, eta_two_mul hτ, he]
  field_simp

/-- `g_{(1/2, 0)}(τ) = -(η(τ/2) / η(τ))²` on the upper half-plane. -/
theorem siegelFunction_half_zero_eq_eta {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 0] τ = -(η (τ / 2) / η τ) ^ 2 := by
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have he : cexp (-(π * I * τ / 12)) = cexp (-(π * I * τ / 24)) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [siegelFunction_half_zero hτ, eta_div_two hτ, he]
  field_simp

/-- `g_{(1/2, 1/2)}(τ) = -e^{-π i / 3} (η((τ + 1)/2) / η(τ))²` on the upper half-plane. -/
theorem siegelFunction_half_half_eq_eta {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 1 / 2] τ = -cexp (-(π * I / 3)) * (η ((τ + 1) / 2) / η τ) ^ 2 := by
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have he : cexp (-(π * I / 4)) * cexp (-(π * I * τ / 12)) =
      cexp (-(π * I / 3)) * cexp (π * I / 24) ^ 2 * cexp (-(π * I * τ / 24)) ^ 2 := by
    simp only [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hq : (cexp (π * I / 24) * cexp (-(π * I * τ / 24)) * η τ *
      ∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) / η τ =
      cexp (π * I / 24) * cexp (-(π * I * τ / 24)) *
        ∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1)) := by
    field_simp
  rw [siegelFunction_half_half hτ, eta_add_one_div_two hτ, hq]
  linear_combination (-(∏' n : ℕ, (1 + cexp (π * I * τ) ^ (2 * n + 1))) ^ 2) * he

/-! ### The transformation `τ ↦ -1/τ` -/

/-- `g₀(-1/τ) = -i g₁(τ)` on the upper half-plane, where `g₀ = g_{(0, 1/2)}` and
`g₁ = g_{(1/2, 0)}`. -/
theorem siegelFunction_zero_half_apply_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![0, 1 / 2] (-1 / τ) = -I * siegelFunction ![1 / 2, 0] τ := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have hτ₂ : 0 < (τ / 2).im := by simpa using hτ
  rw [siegelFunction_zero_half_eq_eta (UpperHalfPlane.im_neg_one_div_pos hτ),
    siegelFunction_half_zero_eq_eta hτ,
    show 2 * (-1 / τ) = -1 / (τ / 2) by field_simp, div_pow, div_pow,
    eta_neg_one_div_sq hτ₂, eta_neg_one_div_sq hτ]
  field_simp

/-- `g₁(-1/τ) = i g₀(τ)` on the upper half-plane, where `g₀ = g_{(0, 1/2)}` and
`g₁ = g_{(1/2, 0)}`. -/
theorem siegelFunction_half_zero_apply_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 0] (-1 / τ) = I * siegelFunction ![0, 1 / 2] τ := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hη : η τ ≠ 0 := _root_.ModularForm.eta_ne_zero hτ
  have hτ₂ : 0 < (2 * τ).im := by simpa using hτ
  have hI (x : ℂ) : I * (2 * I * x) = -2 * x := by linear_combination 2 * x * I_sq
  rw [siegelFunction_half_zero_eq_eta (UpperHalfPlane.im_neg_one_div_pos hτ),
    siegelFunction_zero_half_eq_eta hτ,
    hI, show -1 / τ / 2 = -1 / (2 * τ) by field_simp, div_pow, div_pow,
    eta_neg_one_div_sq hτ₂, eta_neg_one_div_sq hτ]
  field_simp

/-- `g₂(-1/τ) = g₂(τ)` on the upper half-plane, where `g₂ = g_{(1/2, 1/2)}`. -/
theorem siegelFunction_half_half_apply_neg_one_div {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction ![1 / 2, 1 / 2] (-1 / τ) = siegelFunction ![1 / 2, 1 / 2] τ := by
  -- Compare `g₀ g₁ g₂ = 2 ζ₈` at `-1/τ` and at `τ`: the factors `g₀ g₁` agree.
  have h₁ :=
    siegelFunction_zero_half_mul_half_zero_mul_half_half (UpperHalfPlane.im_neg_one_div_pos hτ)
  rw [siegelFunction_zero_half_apply_neg_one_div hτ,
    siegelFunction_half_zero_apply_neg_one_div hτ] at h₁
  have h₂ := siegelFunction_zero_half_mul_half_zero_mul_half_half hτ
  have h₀ : siegelFunction ![0, 1 / 2] τ * siegelFunction ![1 / 2, 0] τ ≠ 0 := by
    intro h
    rw [h, zero_mul] at h₂
    exact mul_ne_zero two_ne_zero (exp_ne_zero _) h₂.symm
  refine mul_left_cancel₀ h₀ ?_
  linear_combination h₁ - h₂ + siegelFunction ![0, 1 / 2] τ * siegelFunction ![1 / 2, 0] τ *
    siegelFunction ![1 / 2, 1 / 2] (-1 / τ) * I_sq

/-! ### The action of `SL₂(ℤ)` on the twelfth powers -/

/-- The cubic `(X - g₀¹²)(X - g₁¹²)(X - g₂¹²)` is fixed by `S`. -/
private theorem prod_X_sub_C_siegelFunction_pow_twelve_S_smul (τ : ℍ) :
    (X - C (siegelFunction ![0, 1 / 2] ↑(ModularGroup.S • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 0] ↑(ModularGroup.S • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 1 / 2] ↑(ModularGroup.S • τ) ^ 12)) =
      (X - C (siegelFunction ![0, 1 / 2] τ ^ 12)) * (X - C (siegelFunction ![1 / 2, 0] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 1 / 2] τ ^ 12)) := by
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / τ := by
    rw [modular_S_smul, coe_mk, neg_div, one_div, inv_neg]
  have hI : I ^ 12 = 1 := by rw [show 12 = 4 * 3 by rfl, pow_mul, I_pow_four, one_pow]
  rw [hS, siegelFunction_zero_half_apply_neg_one_div τ.im_pos,
    siegelFunction_half_zero_apply_neg_one_div τ.im_pos,
    siegelFunction_half_half_apply_neg_one_div τ.im_pos, mul_pow, mul_pow, neg_pow, hI,
    show (-1 : ℂ) ^ 12 = 1 by norm_num]
  simp only [one_mul]
  ring

/-- The cubic `(X - g₀¹²)(X - g₁¹²)(X - g₂¹²)` is fixed by `T`. -/
private theorem prod_X_sub_C_siegelFunction_pow_twelve_T_smul (τ : ℍ) :
    (X - C (siegelFunction ![0, 1 / 2] ↑(ModularGroup.T • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 0] ↑(ModularGroup.T • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 1 / 2] ↑(ModularGroup.T • τ) ^ 12)) =
      (X - C (siegelFunction ![0, 1 / 2] τ ^ 12)) * (X - C (siegelFunction ![1 / 2, 0] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 1 / 2] τ ^ 12)) := by
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    rw [modular_T_smul, coe_vadd, add_comm, ofReal_one]
  have h₆ : cexp (π * I / 6) ^ 12 = 1 := by
    rw [← Complex.exp_nat_mul, show ((12 : ℕ) : ℂ) * (π * I / 6) = 2 * π * I by push_cast; ring,
      exp_two_pi_mul_I]
  have h₃ : cexp (-(π * I / 3)) ^ 12 = 1 := by
    rw [← Complex.exp_nat_mul,
      show ((12 : ℕ) : ℂ) * -(π * I / 3) = ((-2 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I]
  rw [hT, siegelFunction_zero_half_apply_add_one, siegelFunction_half_zero_apply_add_one,
    siegelFunction_half_half_apply_add_one τ.im_pos, mul_pow, mul_pow, mul_pow,
    h₆, h₃]
  simp only [one_mul]
  ring

/-- **`SL₂(ℤ)` permutes the twelfth powers of the level-two Siegel functions**: for every
`γ ∈ SL₂(ℤ)` and `τ` in the upper half-plane, the monic cubic `(X - g₀¹²)(X - g₁¹²)(X - g₂¹²)`
takes the same value at `γ τ` as at `τ`, where `g₀ = g_{(0, 1/2)}`, `g₁ = g_{(1/2, 0)}` and
`g₂ = g_{(1/2, 1/2)}`. -/
theorem prod_X_sub_C_siegelFunction_pow_twelve_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (X - C (siegelFunction ![0, 1 / 2] ↑(γ • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 0] ↑(γ • τ) ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 1 / 2] ↑(γ • τ) ^ 12)) =
      (X - C (siegelFunction ![0, 1 / 2] τ ^ 12)) * (X - C (siegelFunction ![1 / 2, 0] τ ^ 12)) *
        (X - C (siegelFunction ![1 / 2, 1 / 2] τ ^ 12)) := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing τ with
  | one => rw [one_smul]
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact prod_X_sub_C_siegelFunction_pow_twelve_S_smul τ
    · exact prod_X_sub_C_siegelFunction_pow_twelve_T_smul τ
  | mul g h _ _ hg hh => rw [mul_smul, hg, hh]
  | inv g _ hg => rw [← hg, smul_inv_smul]

end TauCeti.ModularForm
