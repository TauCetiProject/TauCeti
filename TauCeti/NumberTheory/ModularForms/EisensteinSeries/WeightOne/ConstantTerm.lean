/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LValues
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Bernoulli
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Normalized
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Constant terms of normalized weight-one Eisenstein series

The normalized series has constant coefficient
`-(δ(φ) B₁,ψ + δ(ψ) B₁,φ) / 2`, where `δ` detects modulus one.
For primitive characters of opposite parity this coefficient is nonzero exactly when
one character has modulus one. This is the nonvanishing input for detecting Eisenstein
series by their constant terms at cusps.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §4.8.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4.
-/

public noncomputable section

open Complex ZMod ModularForm
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.EisensteinSeries

variable {u v N : ℕ} [NeZero u] [NeZero v] [NeZero N]
    (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The constant coefficient in the normalization whose first coefficient is one. Both
characters can contribute, unlike in weights greater than one. -/
theorem qExpansion_normalizedCharE1MF_coeff_zero (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharE1MF ψ φ huv)).coeff 0 =
      -((if v = 1 then ψ.generalizedBernoulli 1 else 0) +
        if u = 1 then φ.generalizedBernoulli 1 else 0) / 2 := by
  have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  have hg := DirichletCharacter.gaussSum_ne_zero_of_isPrimitive hv hφ.inv
    (isPrimitive_stdAddChar v)
  rw [normalizedCharE1MF_def, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, qExpansion_charE1MF_coeff_zero ψ φ huv hpar hφ, smul_eq_mul]
  field_simp [hv, hg, Real.pi_ne_zero, I_ne_zero]

/-- For primitive characters of opposite parity, the constant term at infinity is nonzero
exactly when one of the characters has modulus one. -/
theorem qExpansion_normalizedCharE1MF_coeff_zero_ne_zero_iff (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharE1MF ψ φ huv)).coeff 0 ≠ 0 ↔ u = 1 ∨ v = 1 := by
  rw [qExpansion_normalizedCharE1MF_coeff_zero ψ φ huv hpar hφ]
  by_cases hu : u = 1
  · subst u
    have hodd : φ.Odd := by
      rw [DirichletCharacter.Odd]
      simpa only [DirichletCharacter.modOne_eq_one', one_mul] using hpar
    have hv : v ≠ 1 := by
      intro hv
      subst v
      norm_num [DirichletCharacter.modOne_eq_one'] at hpar
    simp [hv, φ.generalizedBernoulli_one_ne_zero hφ hodd]
  · by_cases hv : v = 1
    · subst v
      have hodd : ψ.Odd := by
        rw [DirichletCharacter.Odd]
        simpa only [DirichletCharacter.modOne_eq_one', mul_one] using hpar
      simp [hu, ψ.generalizedBernoulli_one_ne_zero hψ hodd]
    · simp [hu, hv]

/-- Level raising leaves the Bernoulli constant term unchanged. -/
theorem qExpansion_normalizedCharE1MFRaise_coeff_zero {t : ℕ} (htuv : t * (u * v) ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharE1MFRaise ψ φ t htuv)).coeff 0 =
      -((if v = 1 then ψ.generalizedBernoulli 1 else 0) +
        if u = 1 then φ.generalizedBernoulli 1 else 0) / 2 := by
  let : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  rw [qExpansion_normalizedCharE1MFRaise, PowerSeries.coeff_expand]
  simp only [dvd_zero, ↓reduceIte, Nat.zero_div]
  exact qExpansion_normalizedCharE1MF_coeff_zero ψ φ dvd_rfl hpar hφ

end TauCeti.EisensteinSeries
