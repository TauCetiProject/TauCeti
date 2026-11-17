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

For weight `k ≥ 3` and characters satisfying `ψ(-1) φ(-1) = (-1)ᵏ`, the normalized character
Eisenstein series has constant coefficient `-Bₖ,φ / (2k)` when the first character has modulus
one, and zero otherwise. The second character `φ` must be primitive; the first character `ψ`
need not be primitive.

Together with the twisted-divisor positive coefficients, this identifies the full Fourier
expansion. A positive level raise preserves the constant coefficient.

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
    simp only [hψ, one_mul]
    exact φ.inv_normalization_mul_tsum_eq_generalizedBernoulli (by omega) hφ
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
