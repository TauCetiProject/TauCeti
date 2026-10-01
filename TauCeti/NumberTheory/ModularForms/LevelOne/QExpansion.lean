/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Low-order `q`-expansion coefficients at level one

Mathlib records the constant and linear `q`-coefficients of `E₄`, `E₆` and `Δ`.  This file
continues them to the `q²` and `q³` terms,
`E₄ = 1 + 240 q + 2160 q² + 6720 q³ + ⋯`, `E₆ = 1 - 504 q - 16632 q² - 122976 q³ + ⋯` and
`Δ = q - 24 q² + 252 q³ + ⋯`, and records that `Δ` is asymptotic to `q` at `i∞`.  These are the
coefficients the `q`-expansion of the modular invariant `j = E₄³ / Δ` is computed from.

The Eisenstein coefficients are `240 σ₃(n)` and `-504 σ₅(n)` (Mathlib's
`EisensteinSeries.E_qExpansion_coeff`).  The coefficients of `Δ` are read off the identity
`1728 Δ = E₄³ - E₆²`, transported to `q`-expansions.

## Main results

* `TauCeti.ModularForm.qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq`: the `q`-expansion of `Δ`
  is `(E₄³ - E₆²) / 1728`, computed on power series.
* `TauCeti.ModularForm.discriminant_qExpansion_coeff_two`,
  `TauCeti.ModularForm.discriminant_qExpansion_coeff_three`: `τ(2) = -24` and `τ(3) = 252`.
* `TauCeti.ModularForm.tendsto_discriminant_div_qParam_atImInfty`: `Δ / q → 1` at `i∞`.

## References

* J.-P. Serre, *A Course in Arithmetic*, VII.4 — the expansions of `E₄`, `E₆` and `Δ`.
-/

public noncomputable section

open UpperHalfPlane ModularForm EisensteinSeries Filter Topology
open scoped ArithmeticFunction.sigma MatrixGroups

namespace TauCeti.ModularForm

/-- The `q²`-coefficient of `E₄` is `240 σ₃(2) = 2160`. -/
theorem E₄_qExpansion_coeff_two : (qExpansion 1 E₄).coeff 2 = 2160 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel,
    show σ 3 2 = 9 by decide]

/-- The `q³`-coefficient of `E₄` is `240 σ₃(3) = 6720`. -/
theorem E₄_qExpansion_coeff_three : (qExpansion 1 E₄).coeff 3 = 6720 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel,
    show σ 3 3 = 28 by decide]

/-- The `q²`-coefficient of `E₆` is `-504 σ₅(2) = -16632`. -/
theorem E₆_qExpansion_coeff_two : (qExpansion 1 E₆).coeff 2 = -16632 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel,
    show σ 5 2 = 33 by decide]

/-- The `q³`-coefficient of `E₆` is `-504 σ₅(3) = -122976`. -/
theorem E₆_qExpansion_coeff_three : (qExpansion 1 E₆).coeff 3 = -122976 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel,
    show σ 5 3 = 244 by decide]

/-- The `q`-expansion of the discriminant is `(E₄³ - E₆²) / 1728`, the power-series form of
Mathlib's `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`. -/
theorem qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq :
    qExpansion 1 discriminant = (1728 : ℂ)⁻¹ • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  have h : (1728 : ℂ) • ⇑CuspForm.discriminant = ⇑(E₄.pow 3) - ⇑(E₆.pow 2) := by
    rw [ModularForm.coe_pow, ModularForm.coe_pow]
    funext z
    simp [CuspForm.coe_discriminant, discriminant_eq_E₄_cube_sub_E₆_sq, mul_div_cancel₀]
  have h1728 := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ)
    CuspForm.discriminant
  rw [h, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL] at h1728
  rw [h1728, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul, CuspForm.coe_discriminant]

/-- The constant coefficient of the discriminant vanishes: `Δ` is a cusp form. -/
theorem discriminant_qExpansion_coeff_zero : (qExpansion 1 discriminant).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL

/-- The `q²`-coefficient of the discriminant is Ramanujan's `τ(2) = -24`. -/
theorem discriminant_qExpansion_coeff_two : (qExpansion 1 discriminant).coeff 2 = -24 := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₆_qExpansion_coeff_two,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

/-- The `q³`-coefficient of the discriminant is Ramanujan's `τ(3) = 252`. -/
theorem discriminant_qExpansion_coeff_three : (qExpansion 1 discriminant).coeff 3 = 252 := by
  rw [qExpansion_discriminant_eq_E₄_cube_sub_E₆_sq]
  simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E₄_qExpansion_coeff_two, E₆_qExpansion_coeff_two,
    E₄_qExpansion_coeff_three, E₆_qExpansion_coeff_three,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]
  norm_num

/-- The discriminant is asymptotic to `q` at `i∞`: `Δ / q → 1`. -/
theorem tendsto_discriminant_div_qParam_atImInfty :
    Tendsto (fun τ ↦ discriminant τ / Function.Periodic.qParam 1 τ) atImInfty (𝓝 1) := by
  simpa [discriminant_qExpansion_coeff_one] using
    TauCeti.UpperHalfPlane.tendsto_div_qParam_atImInfty one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL)
      (ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
        one_mem_strictPeriods_SL)
      discriminant_qExpansion_coeff_zero

end TauCeti.ModularForm
