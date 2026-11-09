/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.ModularForms.JacobiTheta.QTheta

/-!
# The transformation of Siegel functions under `SL₂(ℤ)`

The Siegel functions `g_r`, `r ∈ ℝ²` (`TauCeti.ModularForm.siegelFunction`), are permuted by
`SL₂(ℤ)` up to twelfth roots of unity: for every `γ ∈ SL₂(ℤ)` there is `ε(γ)` with `ε(γ)¹² = 1`
such that

  `g_r(γ τ) = ε(γ) g_{r γ}(τ)`

for all `r ∈ ℝ²` and all `τ` in the upper half-plane, where `r γ` is the row vector `r` multiplied
on the right by `γ`. The root of unity depends only on `γ`, not on `r`. For the generators
`T = [[1, 1], [0, 1]]` and `S = [[0, -1], [1, 0]]` it is `ε(T) = e^{π i / 6}` and `ε(S) = -i`:

* `g_r(τ + 1) = e^{π i / 6} g_{(r₁, r₁ + r₂)}(τ)` (`siegelFunction_apply_add_one`), and
* `g_r(-1/τ) = -i g_{(r₂, -r₁)}(τ)` (`siegelFunction_apply_neg_one_div`).

The law for `S` is Jacobi's imaginary transformation of the theta product
(`TauCeti.qTheta_exp_neg_one_div`) at `z = r₂ τ - r₁`; the exponential factors of the two Siegel
functions absorb the exponential factor of that transformation exactly. The general law follows
because `S` and `T` generate `SL₂(ℤ)` and the right action `r ↦ r γ` composes correctly.

Together with the translations of `r` by `ℤ²` (`siegelFunction_add_intCast`), this is the input
for deciding when a product of Siegel functions of level `N` is a modular function for `Γ(N)`.

## Main results

* `TauCeti.ModularForm.siegelFunction_apply_neg_one_div`: `g_r(-1/τ) = -i g_{(r₂, -r₁)}(τ)`.
* `TauCeti.ModularForm.exists_siegelFunction_smul_eq_mul`: for every `γ ∈ SL₂(ℤ)` there is a
  twelfth root of unity `ε` with `g_r(γ τ) = ε g_{r γ}(τ)` for all `r` and `τ`.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 (the transformation formula `K 1` of Klein forms and its consequence for Siegel
  functions).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Matrix
open UpperHalfPlane hiding I
open scoped Real MatrixGroups
open TauCeti.Matrix.SpecialLinearGroup

namespace TauCeti.ModularForm

/-- **The transformation `τ ↦ -1/τ`**: `g_r(-1/τ) = -i g_{r S}(τ)` on the upper half-plane, where
`r S = (r₂, -r₁)` is the row vector `r` multiplied on the right by `S = [[0, -1], [1, 0]]`. -/
theorem siegelFunction_apply_neg_one_div (r : Fin 2 → ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    siegelFunction r (-1 / τ) = -I * siegelFunction ![r 1, -r 0] τ := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hw : cexp (2 * π * I * (r 0 * (-1 / τ) + r 1)) =
      cexp (2 * π * I * ((r 1 * τ + ((-r 0 : ℝ) : ℂ)) / τ)) := by
    congr 1
    push_cast
    field_simp
    ring
  simp only [siegelFunction_eq_qTheta, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [hw, qTheta_exp_neg_one_div hτ]
  have he : cexp (π * I * bernoulliFun 2 (r 0) * (-1 / τ)) * cexp (π * I * r 1 * (r 0 - 1)) *
      cexp (π * I * (((r 1 * τ + ((-r 0 : ℝ) : ℂ)) ^ 2 + (r 1 * τ + ((-r 0 : ℝ) : ℂ)) + 1 / 6) / τ +
        τ / 6 - (r 1 * τ + ((-r 0 : ℝ) : ℂ)))) =
      cexp (π * I * bernoulliFun 2 (r 1) * τ) * cexp (π * I * ((-r 0 : ℝ) : ℂ) * (r 1 - 1)) := by
    simp only [← Complex.exp_add, bernoulliFun_two]
    congr 1
    push_cast
    field_simp
    ring
  linear_combination (I * qTheta (cexp (2 * π * I * τ))
    (cexp (2 * π * I * (r 1 * τ + ((-r 0 : ℝ) : ℂ))))) * he

/-- **The transformation of Siegel functions under `SL₂(ℤ)`.** For every `γ ∈ SL₂(ℤ)` there is a
twelfth root of unity `ε` such that `g_r(γ τ) = ε g_{r γ}(τ)` for every `r ∈ ℝ²` and every `τ` in
the upper half-plane, where `r γ` is the row vector `r` multiplied on the right by `γ`. -/
theorem exists_siegelFunction_smul_eq_mul (γ : SL(2, ℤ)) :
    ∃ ε : ℂ, ε ^ 12 = 1 ∧ ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction with
  | one => exact ⟨1, one_pow _, fun r τ ↦ by simp⟩
  | mem g hg =>
    rcases hg with rfl | rfl
    · refine ⟨-I, by rw [neg_pow, I_pow_eq_pow_mod]; norm_num, fun r τ ↦ ?_⟩
      rw [vecMul_map_modularGroup_S, ← siegelFunction_apply_neg_one_div r τ.im_pos,
        modular_S_smul, coe_mk, neg_div, one_div, inv_neg]
    · refine ⟨cexp (π * I / 6), ?_, fun r τ ↦ ?_⟩
      · rw [← Complex.exp_nat_mul, show ((12 : ℕ) : ℂ) * (π * I / 6) = 2 * π * I by push_cast; ring,
          exp_two_pi_mul_I]
      · rw [vecMul_map_modularGroup_T, ← siegelFunction_apply_add_one, modular_T_smul, coe_vadd,
          add_comm, ofReal_one]
  | mul g h _ _ hg hh =>
    obtain ⟨ε, hε, hg⟩ := hg
    obtain ⟨ε', hε', hh⟩ := hh
    exact ⟨ε * ε', by rw [mul_pow, hε, hε', one_mul], fun r τ ↦ by
      rw [mul_smul, hg, hh, SpecialLinearGroup.vecMul_map_mul, mul_assoc]⟩
  | inv g _ hg =>
    obtain ⟨ε, hε, hg⟩ := hg
    have hε₀ : ε ≠ 0 := by rintro rfl; simp at hε
    refine ⟨ε⁻¹, by rw [inv_pow, hε, inv_one], fun r τ ↦ ?_⟩
    have h := hg (r ᵥ* (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) (g⁻¹ • τ)
    rw [smul_inv_smul, SpecialLinearGroup.vecMul_map_inv_vecMul_map] at h
    rw [h, inv_mul_cancel_left₀ hε₀]

end TauCeti.ModularForm
