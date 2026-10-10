/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Normalized
public import TauCeti.NumberTheory.DirichletCharacter.LValues
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Bernoulli constant coefficients of character Eisenstein series

The normalized character Eisenstein series has constant coefficient `-Bₖ,φ / (2k)` when
the first character has modulus one, and zero otherwise. Together with its twisted-divisor
positive coefficients this gives the full Fourier expansion. A positive level raise preserves
the constant coefficient.

The identification uses the integer-indexed character sum evaluated in
`DirichletCharacter.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli`, together with the
primitive Gauss-sum product. The parity condition cancels the signs in the normalization.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Theorem 4.5.1.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 4, equation (4.1).
-/

public noncomputable section

open Complex AddChar ZMod ModularForm
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.EisensteinSeries

variable {u v N t k : ℕ} [NeZero N]
  (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The constant coefficient of the normalized character Eisenstein series is
`-Bₖ,φ / (2k)` when the first modulus is one, and zero otherwise. Primitivity is needed
only for the second character. -/
-- Rewrite before simplification normalizes a concrete weight's dependent integer cast.
@[simp↓]
theorem qExpansion_normalizedCharEisensteinSeriesMF_coeff_zero
    (hk : 3 ≤ (k : ℤ)) (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = (-1) ^ (k : ℤ)) (hφ : φ.IsPrimitive) :
    haveI : NeZero v := NeZero.of_dvd ((dvd_mul_left v u).trans huv)
    (qExpansion 1 (normalizedCharEisensteinSeriesMF ψ φ hk huv)).coeff 0 =
      if u = 1 then -φ.generalizedBernoulli k / (2 * (k : ℂ)) else 0 := by
  let _ : NeZero v := NeZero.of_dvd ((dvd_mul_left v u).trans huv)
  rw [normalizedCharEisensteinSeriesMF_def, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul,
    qExpansion_charEisensteinSeriesMF_coeff ψ φ hk huv hpar]
  simp only [ite_true, smul_eq_mul]
  split_ifs with hu
  · subst u
    have hψ : ψ 0 = 1 := by
      rw [Subsingleton.elim (0 : ZMod 1) 1, map_one]
    have hψneg : ψ (-1) = 1 := by
      rw [Subsingleton.elim (-1 : ZMod 1) 1, map_one]
    have hφpar : φ (-1) = (-1 : ℂ) ^ k := by
      simpa only [hψneg, one_mul, zpow_natCast] using hpar
    simp only [hψ, one_mul]
    -- The primitive Gauss product supplies both nonvanishing factors.
    have hprod :=
      DirichletCharacter.gaussSum_mul_gaussSum_inv_eq_neg_one_mul_card_of_isPrimitive hφ
      (ZMod.isPrimitive_stdAddChar v)
    rw [ZMod.card, hφpar] at hprod
    have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
    have hprod0 : gaussSum φ stdAddChar * gaussSum φ⁻¹ stdAddChar ≠ 0 := by
      rw [hprod]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hv
    have hτ : gaussSum φ stdAddChar ≠ 0 :=
      left_ne_zero_of_mul hprod0
    have hτinv : gaussSum φ⁻¹ stdAddChar ≠ 0 := right_ne_zero_of_mul hprod0
    have hf : ((k - 1).factorial : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hA : (-2 * π * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hC : 2 * (-2 * π * I) ^ k / ((k - 1).factorial * (v : ℂ) ^ k) *
        gaussSum φ⁻¹ stdAddChar ≠ 0 := by
      exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hA))
        (mul_ne_zero hf (pow_ne_zero _ hv))) hτinv
    rw [inv_mul_eq_iff_eq_mul₀ hC]
    apply mul_left_cancel₀ hτ
    -- Evaluate the integer row sum before simplifying the normalization scalar.
    rw [φ.gaussSum_mul_tsum_inv_pow_eq_generalizedBernoulli hφ (by omega)]
    have hfac : (k.factorial : ℂ) = (k : ℂ) * (k - 1).factorial := by
      exact_mod_cast (Nat.mul_factorial_pred (by omega : k ≠ 0)).symm
    have hpower : (-2 * π * I : ℂ) ^ k * (-1 : ℂ) ^ k = (2 * π * I) ^ k := by
      rw [← mul_pow]
      congr 1
      ring
    have hpowv : (v : ℂ) ^ k = (v : ℂ) ^ (k - 1) * v := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    -- The Gauss product and the parity sign cancel the normalization factor.
    symm
    calc
      _ = (2 * (-2 * π * I) ^ k / ((k - 1).factorial * (v : ℂ) ^ k) *
          (gaussSum φ stdAddChar * gaussSum φ⁻¹ stdAddChar)) *
            (-φ.generalizedBernoulli k / (2 * (k : ℂ))) := by ring
      _ = _ := by
        rw [hprod, hfac, hpowv]
        have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
        linear_combination -φ.generalizedBernoulli k * hpower
  · rw [ψ.map_zero' hu, zero_mul, mul_zero]

/-- A raised normalized character Eisenstein series has the same Bernoulli constant
coefficient as the base series. -/
-- Rewrite before the level-raise equation and the dependent weight index are normalized.
@[simp↓]
theorem qExpansion_normalizedCharEisensteinSeriesMFRaise_coeff_zero
    (hk : 3 ≤ (k : ℤ)) (htuv : t * (u * v) ∣ N)
    (hpar : ψ (-1) * φ (-1) = (-1) ^ (k : ℤ)) (hφ : φ.IsPrimitive) :
    haveI : NeZero v := NeZero.of_dvd ((dvd_mul_left v u).trans
      ((dvd_mul_left (u * v) t).trans htuv))
    (qExpansion 1 (normalizedCharEisensteinSeriesMFRaise ψ φ t hk htuv)).coeff 0 =
      if u = 1 then -φ.generalizedBernoulli k / (2 * (k : ℂ)) else 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [qExpansion_normalizedCharEisensteinSeriesMFRaise]
  simpa using qExpansion_normalizedCharEisensteinSeriesMF_coeff_zero ψ φ hk dvd_rfl hpar hφ

end TauCeti.EisensteinSeries
