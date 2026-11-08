/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.QExpansion
import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.ModularForms.QExpansion.Positive
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Normalized weight-one Eisenstein series and character exchange

Normalize the weight-one Eisenstein series with character to have first Fourier coefficient
one. Its positive coefficients are the symmetric twisted divisor sums
`σ₀^{ψ,φ}(n) = ∑_{d ∣ n} ψ(n / d) φ(d)`. For primitive `ψ` and `φ` of opposite parity,
exchanging the characters therefore gives the same modular form, including the constant term.
The same relation holds after every level raise. This identifies the duplicate generators
which must be removed when counting the weight-one Eisenstein series.

The normalization follows `normalizedCharEisensteinSeriesMF` in the higher-weight theory;
the analytic input is `qExpansion_charE1MF_coeff_of_isPrimitive`. No formula for the constant
coefficient is needed for character exchange: positive Fourier coefficients determine a modular
form of nonzero weight.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.8.
* [T. Miyake, *Modular forms*][miyake1989], §7.1.
-/

public noncomputable section

open Complex ZMod ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

namespace TauCeti.EisensteinSeries

variable {u v N t : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ u) (φ : DirichletCharacter ℂ v)

/-- The weight-one character Eisenstein series scaled by the inverse of its expected first
coefficient. For primitive `φ` and opposite character parity, this coefficient is nonzero and
the resulting series has first Fourier coefficient one. -/
def normalizedCharE1MF (huv : u * v ∣ N) : ModularForm ((Gamma1 N).map (mapGL ℝ)) 1 := by
  let _ : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  exact (2 * (-2 * π * I) / v * gaussSum φ⁻¹ stdAddChar)⁻¹ • charE1MF ψ φ huv

/-- The defining normalization as a scalar multiple of the raw weight-one series. -/
theorem normalizedCharE1MF_def (huv : u * v ∣ N) :
    haveI : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
    normalizedCharE1MF ψ φ huv =
      (2 * (-2 * π * I) / v * gaussSum φ⁻¹ stdAddChar)⁻¹ • charE1MF ψ φ huv := (rfl)

/-- The positive Fourier coefficients of a normalized weight-one character Eisenstein series
are the twisted divisor sums of exponent zero. -/
theorem qExpansion_normalizedCharE1MF_coeff (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (normalizedCharE1MF ψ φ huv)).coeff n =
      DirichletCharacter.twistedDivisorSum 0 ψ φ n := by
  let _ : NeZero v := NeZero.of_dvd (dvd_of_mul_left_dvd huv)
  have hv : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  have hg := DirichletCharacter.gaussSum_ne_zero_of_isPrimitive hφ.inv
    (isPrimitive_stdAddChar v)
  have hscale : 2 * (-2 * π * I) / v * gaussSum φ⁻¹ stdAddChar ≠ 0 := by
    exact mul_ne_zero (div_ne_zero (by simp [Real.pi_ne_zero]) hv) hg
  rw [normalizedCharE1MF_def, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul,
    qExpansion_charE1MF_coeff_of_isPrimitive ψ φ huv hpar hφ hn,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hscale, one_mul]

/-- The first Fourier coefficient of the normalized series is one. -/
@[simp]
theorem qExpansion_normalizedCharE1MF_coeff_one (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharE1MF ψ φ huv)).coeff 1 = 1 := by
  rw [qExpansion_normalizedCharE1MF_coeff ψ φ huv hpar hφ one_ne_zero,
    DirichletCharacter.twistedDivisorSum_one]

/-- The normalized weight-one character Eisenstein series is nonzero. -/
theorem normalizedCharE1MF_ne_zero (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    normalizedCharE1MF ψ φ huv ≠ 0 := by
  intro hzero
  have h := qExpansion_normalizedCharE1MF_coeff_one ψ φ huv hpar hφ
  simp only [hzero, FunLike.coe_zero, qExpansion_zero, map_zero, zero_ne_one] at h

/-- Normalization preserves the nebentypus of the weight-one series. -/
theorem normalizedCharE1MF_mem_modFormCharSpace (huv : u * v ∣ N) :
    normalizedCharE1MF ψ φ huv ∈ modFormCharSpace 1
      (ψ.changeLevel (dvd_of_mul_right_dvd huv) *
        φ.changeLevel (dvd_of_mul_left_dvd huv)).toUnitHom := by
  rw [normalizedCharE1MF_def]
  exact (modFormCharSpace 1 _).smul_mem _ (charE1MF_mem_modFormCharSpace ψ φ huv)

/-- Exchanging primitive characters of opposite parity does not change the normalized
weight-one Eisenstein series. This equality includes the constant coefficient. -/
theorem normalizedCharE1MF_comm (huv : u * v ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) :
    normalizedCharE1MF ψ φ huv = normalizedCharE1MF φ ψ (by rwa [mul_comm]) := by
  apply TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) one_ne_zero
  intro n hn
  have hpar' : φ (-1) * ψ (-1) = -1 := (mul_comm _ _).trans hpar
  rw [qExpansion_normalizedCharE1MF_coeff ψ φ huv hpar hφ hn.ne',
    qExpansion_normalizedCharE1MF_coeff φ ψ _ hpar' hψ hn.ne',
    DirichletCharacter.twistedDivisorSum_zero_comm]

/-- The level raise `E₁^{ψ,φ,t}(z) = E₁^{ψ,φ}(tz)` of the normalized series, at any level
`N` divisible by `t u v`. -/
def normalizedCharE1MFRaise (t : ℕ) (htuv : t * (u * v) ∣ N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) 1 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  exact ModularForm.levelRaise t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)
    (normalizedCharE1MF ψ φ dvd_rfl)

/-- The normalized raised series is the same scalar multiple of the raw raised series. -/
theorem normalizedCharE1MFRaise_eq_smul (htuv : t * (u * v) ∣ N) :
    haveI : NeZero v := NeZero.of_dvd ((dvd_mul_left v u).trans
      (dvd_of_mul_left_dvd htuv))
    normalizedCharE1MFRaise ψ φ t htuv =
      (2 * (-2 * π * I) / v * gaussSum φ⁻¹ stdAddChar)⁻¹ • charE1MFRaise ψ φ t htuv := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  let _ : NeZero v := NeZero.of_dvd ((dvd_mul_left v u).trans (dvd_of_mul_left_dvd htuv))
  rw [normalizedCharE1MFRaise, normalizedCharE1MF_def, charE1MFRaise_eq_levelRaise]
  simpa only [ModularForm.levelRaiseₗ_apply] using
    (ModularForm.levelRaiseₗ t (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv)).map_smul
      (2 * (-2 * π * I) / v * gaussSum φ⁻¹ stdAddChar)⁻¹ (charE1MF ψ φ dvd_rfl)

/-- Evaluation of the normalized level raise at a point of the upper half-plane. -/
@[simp]
theorem normalizedCharE1MFRaise_apply (htuv : t * (u * v) ∣ N) (z : ℍ) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    normalizedCharE1MFRaise ψ φ t htuv z = normalizedCharE1MF ψ φ dvd_rfl (scaleGL t • z) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharE1MFRaise, ModularForm.levelRaise_apply]

/-- Raising by one is restriction from the natural level `u v`. -/
@[simp]
theorem normalizedCharE1MFRaise_one (huv : u * v ∣ N) :
    haveI : NeZero (u * v) := NeZero.of_dvd huv
    normalizedCharE1MFRaise ψ φ 1 (by simpa using huv) =
      ModularForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd huv)
        (normalizedCharE1MF ψ φ dvd_rfl) := by
  rw [normalizedCharE1MFRaise, ModularForm.levelRaise_one]

/-- Raising substitutes `q ↦ q^t` in the normalized weight-one series. -/
@[simp]
theorem qExpansion_normalizedCharE1MFRaise (htuv : t * (u * v) ∣ N) :
    haveI : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
    haveI : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
    qExpansion 1 (normalizedCharE1MFRaise ψ φ t htuv) =
      (qExpansion 1 (normalizedCharE1MF ψ φ dvd_rfl)).expand t (NeZero.ne t) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharE1MFRaise]
  exact ModularForm.qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) _ _

/-- The `q`-expansion of a raised normalized weight-one Eisenstein series is supported on the
multiples of `t`, without primitivity or parity assumptions. -/
theorem isSupportedOnDvd_qExpansion_normalizedCharE1MFRaise (htuv : t * (u * v) ∣ N) :
    PowerSeries.IsSupportedOnDvd t (qExpansion 1 (normalizedCharE1MFRaise ψ φ t htuv)) := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharE1MFRaise]
  exact ModularForm.isSupportedOnDvd_qExpansion_levelRaise
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)
    (Gamma1_map_le_conjAct_scaleGL_of_dvd htuv) _

/-- The positive coefficients of the raised series are the twisted divisor sums at `n / t`
when `t ∣ n`, and zero otherwise. -/
theorem qExpansion_normalizedCharE1MFRaise_coeff (htuv : t * (u * v) ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) {n : ℕ} (hn : n ≠ 0) :
    (qExpansion 1 (normalizedCharE1MFRaise ψ φ t htuv)).coeff n =
      if t ∣ n then DirichletCharacter.twistedDivisorSum 0 ψ φ (n / t) else 0 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  let _ : NeZero (u * v) := NeZero.of_dvd (dvd_of_mul_left_dvd htuv)
  rw [normalizedCharE1MFRaise, ModularForm.qExpansion_levelRaise_coeff
    (TauCeti.one_mem_strictPeriods_Gamma1_map (u * v))
    (TauCeti.one_mem_strictPeriods_Gamma1_map N)]
  split_ifs with htn
  · exact qExpansion_normalizedCharE1MF_coeff ψ φ dvd_rfl hpar hφ
      (Nat.div_ne_zero_iff.mpr ⟨NeZero.ne t, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) htn⟩)
  · rfl

/-- The normalized level raise has coefficient one at its first supported index `t`. -/
theorem qExpansion_normalizedCharE1MFRaise_coeff_self (htuv : t * (u * v) ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    (qExpansion 1 (normalizedCharE1MFRaise ψ φ t htuv)).coeff t = 1 := by
  let _ : NeZero t := NeZero.of_dvd (dvd_of_mul_right_dvd htuv)
  rw [qExpansion_normalizedCharE1MFRaise_coeff ψ φ htuv hpar hφ (NeZero.ne t)]
  rw [ite_eq_left (dvd_refl t), Nat.div_self (NeZero.pos t),
    DirichletCharacter.twistedDivisorSum_one]

/-- Every normalized level raise of a primitive, parity-compatible series is nonzero. -/
theorem normalizedCharE1MFRaise_ne_zero (htuv : t * (u * v) ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hφ : φ.IsPrimitive) :
    normalizedCharE1MFRaise ψ φ t htuv ≠ 0 := by
  intro hzero
  have h := qExpansion_normalizedCharE1MFRaise_coeff_self ψ φ htuv hpar hφ
  simp only [hzero, FunLike.coe_zero, qExpansion_zero, map_zero, zero_ne_one] at h

/-- The normalized level raise has nebentypus `ψφ` at its target level. -/
theorem normalizedCharE1MFRaise_mem_modFormCharSpace (htuv : t * (u * v) ∣ N) :
    normalizedCharE1MFRaise ψ φ t htuv ∈ modFormCharSpace 1
      (ψ.changeLevel ((dvd_mul_right u v).trans (dvd_of_mul_left_dvd htuv)) *
        φ.changeLevel ((dvd_mul_left v u).trans (dvd_of_mul_left_dvd htuv))).toUnitHom := by
  rw [normalizedCharE1MFRaise_eq_smul]
  exact (modFormCharSpace 1 _).smul_mem _ (charE1MFRaise_mem_modFormCharSpace ψ φ htuv)

/-- The character-exchange relation persists under every level raise. -/
theorem normalizedCharE1MFRaise_comm (htuv : t * (u * v) ∣ N)
    (hpar : ψ (-1) * φ (-1) = -1) (hψ : ψ.IsPrimitive) (hφ : φ.IsPrimitive) :
    normalizedCharE1MFRaise ψ φ t htuv =
      normalizedCharE1MFRaise φ ψ t (by rwa [mul_comm v u]) := by
  apply TauCeti.ModularForm.eq_of_forall_pos_qExpansion_coeff_eq one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) one_ne_zero
  intro n hn
  have hpar' : φ (-1) * ψ (-1) = -1 := (mul_comm _ _).trans hpar
  rw [qExpansion_normalizedCharE1MFRaise_coeff ψ φ htuv hpar hφ hn.ne',
    qExpansion_normalizedCharE1MFRaise_coeff φ ψ _ hpar' hψ hn.ne',
    DirichletCharacter.twistedDivisorSum_zero_comm]

end TauCeti.EisensteinSeries
