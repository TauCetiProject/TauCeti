/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DedekindEta.Power
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.NumberTheory.ModularForms.JacobiTheta.QTheta

/-!
# The transformation of Siegel functions under `SL₂(ℤ)`

The Siegel functions `g_r`, `r ∈ ℝ²` (`TauCeti.ModularForm.siegelFunction`), are permuted by
`SL₂(ℤ)` up to explicit twelfth roots of unity: for every `γ = (a b; c d) ∈ SL₂(ℤ)`,

  `g_r(γ τ) = ε(γ)² g_{r γ}(τ)`

for all `r ∈ ℝ²` and all `τ` in the upper half-plane, where `r γ` is the row vector `r` multiplied
on the right by `γ` and `ε(γ) = TauCeti.ModularForm.etaMultiplier γ` is the eta multiplier, so
that `ε(γ)²` is the multiplier of `η²`. The root of unity depends only on `γ`, not on `r`. For the
generators `T = [[1, 1], [0, 1]]` and `S = [[0, -1], [1, 0]]` it is `ε(T)² = e^{π i / 6}` and
`ε(S)² = -i`:

* `g_r(τ + 1) = e^{π i / 6} g_{(r₁, r₁ + r₂)}(τ)` (`siegelFunction_apply_add_one`), and
* `g_r(-1/τ) = -i g_{(r₂, -r₁)}(τ)` (`siegelFunction_apply_neg_one_div`).

The law for `S` is Jacobi's imaginary transformation of the theta product
(`TauCeti.qTheta_exp_neg_one_div`) at `z = r₂ τ - r₁`; the exponential factors of the two Siegel
functions absorb the exponential factor of that transformation exactly. The general law follows
because `S` and `T` generate `SL₂(ℤ)`, the right action `r ↦ r γ` composes correctly and `ε²` is
a character of `SL₂(ℤ)` (`etaMultiplier_mul_sq`).

The Kronecker-symbol form of the eta multiplier then gives the multiplier in closed form, as in
Kubert and Lang: since `c` and `d` are coprime, one of them is odd, and

* `ε(γ)² = exp(π i (b d (1 - c²) + c (a + d - 3)) / 6)` if `c` is odd,
* `ε(γ)² = -i exp(π i (a c (1 - d²) + d (b - c + 3)) / 6)` if `d` is odd.

These exact phases are what is needed to compute the action of `SL₂(ℤ)` on a product of Siegel
functions, and hence the conjugates of their values at CM points. Together with the translations of
`r` by `ℤ²` (`siegelFunction_add_intCast`), this is the input for deciding when a product of
Siegel functions of level `N` is a modular function for `Γ(N)`.

## Main results

* `TauCeti.ModularForm.siegelFunction_apply_neg_one_div`: `g_r(-1/τ) = -i g_{(r₂, -r₁)}(τ)`.
* `TauCeti.ModularForm.siegelFunction_smul_eq_etaMultiplier_sq_mul`:
  `g_r(γ τ) = ε(γ)² g_{r γ}(τ)` for all `γ`, `r` and `τ`.
* `TauCeti.ModularForm.exists_siegelFunction_smul_eq_mul`: in particular the multiplier is a
  twelfth root of unity.
* `TauCeti.ModularForm.siegelFunction_smul_eq_exp_mul_of_odd_c`,
  `TauCeti.ModularForm.siegelFunction_smul_eq_neg_I_mul_exp_mul_of_odd_d`: the transformation law
  with the multiplier in closed form.

## References

* D. S. Kubert, S. Lang, *Modular Units*, Grundlehren der mathematischen Wissenschaften 244,
  Chapter 2, §1 (the transformation formula `K 1` of Klein forms and its consequence for Siegel
  functions, with the multiplier in closed form).
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2,
  Proposition 2.3.
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

/-- **The transformation of Siegel functions under `SL₂(ℤ)`.** For `γ ∈ SL₂(ℤ)`,
`g_r(γ τ) = ε(γ)² g_{r γ}(τ)` for every `r ∈ ℝ²` and every `τ` in the upper half-plane, where `r γ`
is the row vector `r` multiplied on the right by `γ` and `ε(γ)` is the eta multiplier, so that
`ε(γ)²` is the multiplier of `η²`. -/
theorem siegelFunction_smul_eq_etaMultiplier_sq_mul (γ : SL(2, ℤ)) (r : Fin 2 → ℝ) (τ : ℍ) :
    siegelFunction r ↑(γ • τ) = etaMultiplier γ ^ 2 *
      siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing r τ with
  | one => simp
  | mem g hg =>
    rcases hg with rfl | rfl
    · rw [etaMultiplier_S, ← Complex.exp_natCast_mul,
        show ((2 : ℕ) : ℂ) * -(π * I / 4) = -π / 2 * I by push_cast; ring,
        exp_neg_pi_div_two_mul_I, vecMul_map_modularGroup_S,
        ← siegelFunction_apply_neg_one_div r τ.im_pos, modular_S_smul, coe_mk, neg_div, one_div,
        inv_neg]
    · rw [etaMultiplier_T, ← Complex.exp_natCast_mul,
        show ((2 : ℕ) : ℂ) * (π * I / 12) = π * I / 6 by push_cast; ring,
        vecMul_map_modularGroup_T, ← siegelFunction_apply_add_one, modular_T_smul, coe_vadd,
        add_comm, ofReal_one]
  | mul g h _ _ hg hh =>
    rw [mul_smul, hg, hh, SpecialLinearGroup.vecMul_map_mul, etaMultiplier_mul_sq, mul_assoc]
  | inv g _ hg =>
    have h := hg (r ᵥ* (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) (g⁻¹ • τ)
    rw [smul_inv_smul, SpecialLinearGroup.vecMul_map_inv_vecMul_map] at h
    have hmul : etaMultiplier g⁻¹ ^ 2 * etaMultiplier g ^ 2 = 1 := by
      rw [← etaMultiplier_mul_sq, inv_mul_cancel, etaMultiplier_one, one_pow]
    rw [h, ← mul_assoc, hmul, one_mul]

/-- The multiplier in the transformation law of the Siegel functions is a twelfth root of unity:
for every `γ ∈ SL₂(ℤ)` there is `ε` with `ε¹² = 1` and `g_r(γ τ) = ε g_{r γ}(τ)` for every `r`
and `τ`. -/
theorem exists_siegelFunction_smul_eq_mul (γ : SL(2, ℤ)) :
    ∃ ε : ℂ, ε ^ 12 = 1 ∧ ∀ (r : Fin 2 → ℝ) (τ : ℍ), siegelFunction r ↑(γ • τ) =
      ε * siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ :=
  ⟨etaMultiplier γ ^ 2, by rw [← pow_mul, etaMultiplier_pow_twentyFour],
    siegelFunction_smul_eq_etaMultiplier_sq_mul γ⟩

/-- **The transformation of Siegel functions, odd `c`** (Kubert–Lang): for
`γ = (a b; c d) ∈ SL₂(ℤ)` with `c` odd,
`g_r(γ τ) = exp(π i (b d (1 - c²) + c (a + d - 3)) / 6) g_{r γ}(τ)`. -/
theorem siegelFunction_smul_eq_exp_mul_of_odd_c (γ : SL(2, ℤ)) (hc : Odd (γ 1 0))
    (r : Fin 2 → ℝ) (τ : ℍ) :
    siegelFunction r ↑(γ • τ) = cexp (π * I *
      ((γ 0 1 * γ 1 1 * (1 - γ 1 0 ^ 2) + γ 1 0 * (γ 0 0 + γ 1 1 - 3) : ℤ) : ℂ) / 6) *
        siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ := by
  rw [siegelFunction_smul_eq_etaMultiplier_sq_mul, etaMultiplier_sq_eq_exp_of_odd_c γ hc]

/-- **The transformation of Siegel functions, odd `d`** (Kubert–Lang): for
`γ = (a b; c d) ∈ SL₂(ℤ)` with `d` odd,
`g_r(γ τ) = -i exp(π i (a c (1 - d²) + d (b - c + 3)) / 6) g_{r γ}(τ)`. -/
theorem siegelFunction_smul_eq_neg_I_mul_exp_mul_of_odd_d (γ : SL(2, ℤ)) (hd : Odd (γ 1 1))
    (r : Fin 2 → ℝ) (τ : ℍ) :
    siegelFunction r ↑(γ • τ) = -I * cexp (π * I *
      ((γ 0 0 * γ 1 0 * (1 - γ 1 1 ^ 2) + γ 1 1 * (γ 0 1 - γ 1 0 + 3) : ℤ) : ℂ) / 6) *
        siegelFunction (r ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ)) τ := by
  rw [siegelFunction_smul_eq_etaMultiplier_sq_mul, etaMultiplier_sq_eq_neg_I_mul_exp_of_odd_d γ hd]

end TauCeti.ModularForm
