/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.SpecialFunctions.Complex.CpowCharacter
public import TauCeti.Geometry.Lie.Exponential.Units.Complex

import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Data.SignType.Basic
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Continuous characters of `ℝˣ` and `ℂˣ`

This file classifies the continuous homomorphisms `ℝˣ → ℂˣ` and `ℂˣ → ℂˣ`, the quasi-characters
of the two archimedean local fields. Every continuous character of `ℝˣ` is
`x ↦ |x| ^ s * sgn(x) ^ ε` with `s : ℂ` and `ε : ZMod 2`, and every continuous character of `ℂˣ`
is `z ↦ |z| ^ s * (z / |z|) ^ k` with `s : ℂ` and `k : ℤ`. In both cases the parameters are
unique, and multiplying characters adds them. The exponents `s` are complex: the unitary
characters `x ↦ |x| ^ (i t)` form a continuous family that no integer or sign data can record.
These are the archimedean components of Hecke characters, and their parameters are the data of an
infinity type at the real and complex places.

The analytic input is `TauCeti.existsUnique_eq_expUnitHom_complex`: every continuous homomorphism
from the additive real line to `ℂˣ` is `t ↦ exp (t * s)`, with no differentiability hypothesis.
It reads off the exponent `s` of a character from its restriction to the positive reals, and the
angular frequency `k` of a character of `ℂˣ` from its restriction to the unit circle.

## Main definitions

* `TauCeti.realSignCharacter`: the sign character of `ℝˣ`.
* `TauCeti.complexAngularCharacter`: the character `z ↦ z / |z|` of `ℂˣ`.
* `TauCeti.realUnitsCharacter s ε`: the character `x ↦ |x| ^ s * sgn(x) ^ ε` of `ℝˣ`.
* `TauCeti.complexUnitsCharacter s k`: the character `z ↦ |z| ^ s * (z / |z|) ^ k` of `ℂˣ`.
* `TauCeti.realUnitsCharacterEquiv`: `Multiplicative (ℂ × ZMod 2) ≃* (ℝˣ →ₜ* ℂˣ)`.
* `TauCeti.complexUnitsCharacterEquiv`: `Multiplicative (ℂ × ℤ) ≃* (ℂˣ →ₜ* ℂˣ)`.

## Main results

* `TauCeti.existsUnique_eq_expUnitHom_complex`: continuous homomorphisms `ℝ → ℂˣ` are
  exponentials.
* `TauCeti.realUnitsCharacter_comp_expUnitHom`, `TauCeti.realUnits_ext`: restriction to the
  positive reals and extensionality for characters of `ℝˣ`.
* `TauCeti.exists_eq_realUnitsCharacter`, `TauCeti.realUnitsCharacter_injective2`: the
  classification of the continuous characters of `ℝˣ`.
* `TauCeti.complexUnitsCharacter_comp_expUnitHom_one`,
  `TauCeti.complexUnitsCharacter_comp_expUnitHom_I`, `TauCeti.complexUnits_ext`: restriction to
  the positive reals and unit circle and extensionality for characters of `ℂˣ`.
* `TauCeti.exists_eq_complexUnitsCharacter`, `TauCeti.complexUnitsCharacter_injective2`: the
  classification of the continuous characters of `ℂˣ`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §2.3.
-/

public section
noncomputable section

namespace TauCeti

open Complex

/-! ### The basic characters -/

/-- The sign character `x ↦ sgn x` of `ℝˣ`, with values `±1` in `ℂˣ`. -/
def realSignCharacter : ℝˣ →ₜ* ℂˣ where
  toMonoidHom := Units.map ((SignType.castHom : SignType →*₀ ℂ).toMonoidHom.comp
    (signHom : ℝ →*₀ SignType).toMonoidHom)
  continuous_toFun := by
    refine Units.isEmbedding_val₀.continuous_iff.mpr ?_
    simp only [Units.map_comp, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_comp,
      Function.comp_def, Units.coe_map, MonoidHom.coe_mk, ZeroHom.toFun_eq_coe,
      MonoidWithZeroHom.toZeroHom_coe, signHom_apply, OneHom.coe_mk, SignType.castHom_apply,
      ← SignType.map_cast ofRealHom, sign_eq_div_abs, ofRealHom_eq_coe]
    exact continuous_ofReal.comp <|
      Units.continuous_val.div (continuous_abs.comp Units.continuous_val) fun x ↦
        abs_ne_zero.2 x.ne_zero

/-- Evaluating the sign character at `x` gives the sign of `x`. -/
@[simp]
theorem coe_realSignCharacter_apply (x : ℝˣ) :
    (realSignCharacter x : ℂ) = (SignType.sign (x : ℝ) : ℂ) :=
  by simp [realSignCharacter]

/-- The angular character `z ↦ z / |z|` of `ℂˣ`. -/
def complexAngularCharacter : ℂˣ →ₜ* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) <| by simp
  map_one' := Units.ext <| by simp
  map_mul' z w := Units.ext <| by simp [mul_div_mul_comm]
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr <|
    Units.continuous_val.div (continuous_ofReal.comp (continuous_norm.comp Units.continuous_val))
      fun z ↦ by simp

/-- Evaluating the angular character at `z` gives `z / |z|`. -/
@[simp]
theorem coe_complexAngularCharacter_apply (z : ℂˣ) :
    (complexAngularCharacter z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) :=
  (rfl)

/-! ### Characters of `ℝˣ` -/

/-- The character `x ↦ |x| ^ s * sgn(x) ^ ε` of `ℝˣ`, for a complex exponent `s` and a parity
`ε : ZMod 2`. -/
def realUnitsCharacter (s : ℂ) (ε : ZMod 2) : ℝˣ →ₜ* ℂˣ :=
  normCpowCharacter ℝ s * realSignCharacter ^ ε.val

/-- Evaluating `realUnitsCharacter s ε` at `x` gives `|x| ^ s * sgn(x) ^ ε`. -/
@[simp]
theorem coe_realUnitsCharacter_apply (s : ℂ) (ε : ZMod 2) (x : ℝˣ) :
    (realUnitsCharacter s ε x : ℂ) =
      ((|(x : ℝ)| : ℝ) : ℂ) ^ s * (SignType.sign (x : ℝ) : ℂ) ^ ε.val := by
  simp [realUnitsCharacter]

/-- With parity `0`, `realUnitsCharacter s 0` is the norm-power character `x ↦ |x| ^ s`. -/
@[simp]
theorem realUnitsCharacter_zero_right (s : ℂ) : realUnitsCharacter s 0 = normCpowCharacter ℝ s := by
  simp [realUnitsCharacter]

/-- With exponent `0`, `realUnitsCharacter 0 ε` is the power `sgn ^ ε` of the sign character. -/
@[simp]
theorem realUnitsCharacter_zero_left (ε : ZMod 2) :
    realUnitsCharacter 0 ε = realSignCharacter ^ ε.val := by
  rw [realUnitsCharacter, normCpowCharacter_zero]
  exact one_mul (realSignCharacter ^ ε.val)

/-- The sign character has order two. -/
@[simp]
theorem realSignCharacter_sq : realSignCharacter ^ 2 = 1 :=
  ContinuousMonoidHom.ext fun x ↦ Units.ext <| by
    rcases lt_or_gt_of_ne x.ne_zero with h | h <;> simp [h]

/-- Adding parameters multiplies the characters of `ℝˣ`. -/
@[simp]
theorem realUnitsCharacter_add (s t : ℂ) (ε η : ZMod 2) :
    realUnitsCharacter (s + t) (ε + η) = realUnitsCharacter s ε * realUnitsCharacter t η := by
  rw [realUnitsCharacter, realUnitsCharacter, realUnitsCharacter, normCpowCharacter_add,
    ZMod.val_add, ← pow_eq_pow_mod _ realSignCharacter_sq, pow_add]
  exact mul_mul_mul_comm (normCpowCharacter ℝ s) _ _ _

/-- Restricting `realUnitsCharacter s ε` to the positive reals gives `expUnitHom s`; the sign
parameter is invisible on the identity component. -/
theorem realUnitsCharacter_comp_expUnitHom (s : ℂ) (ε : ZMod 2) :
    (realUnitsCharacter s ε).comp (expUnitHom (1 : ℝ)) = expUnitHom s := by
  refine ContinuousMonoidHom.ext fun t ↦ Units.ext ?_
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective t
  rw [ContinuousMonoidHom.comp_toFun, coe_realUnitsCharacter_apply, coe_expUnitHom_real,
    coe_expUnitHom_complex]
  simp [Real.exp_pos, -ofReal_exp, ofReal_exp_cpow]

/-- Evaluating `realUnitsCharacter s ε` at `-1` gives `(-1) ^ ε`; the exponent `s` is invisible
there. -/
theorem realUnitsCharacter_neg_one (s : ℂ) (ε : ZMod 2) :
    (realUnitsCharacter s ε (-1) : ℂ) = (-1) ^ ε.val := by
  simp

/-- Continuous characters of `ℝˣ` agree once they agree at `-1` and on the positive reals. -/
theorem realUnits_ext {χ ψ : ℝˣ →ₜ* ℂˣ} (hneg : χ (-1) = ψ (-1))
    (hexp : χ.comp (expUnitHom (1 : ℝ)) = ψ.comp (expUnitHom 1)) : χ = ψ := by
  have hexp' (t : ℝ) : χ (expUnitHom (1 : ℝ) (.ofAdd t)) = ψ (expUnitHom (1 : ℝ) (.ofAdd t)) :=
    DFunLike.congr_fun hexp (.ofAdd t)
  refine ContinuousMonoidHom.ext fun x ↦ ?_
  have habs : Real.exp (Real.log |(x : ℝ)|) = |(x : ℝ)| := Real.exp_log (abs_pos.2 x.ne_zero)
  rcases lt_or_gt_of_ne x.ne_zero with h | h
  · have hx : x = -1 * expUnitHom (1 : ℝ) (.ofAdd (Real.log |(x : ℝ)|)) :=
      Units.ext (by rw [Units.val_mul, coe_expUnitHom_real, mul_one, habs, abs_of_neg h]; simp)
    rw [hx, map_mul, map_mul, hneg, hexp']
  · have hx : x = expUnitHom (1 : ℝ) (.ofAdd (Real.log |(x : ℝ)|)) :=
      Units.ext (by rw [coe_expUnitHom_real, mul_one, habs, abs_of_pos h])
    rw [hx, hexp']

/-- **Every continuous character of `ℝˣ` is `x ↦ |x| ^ s * sgn(x) ^ ε`.** -/
theorem exists_eq_realUnitsCharacter (χ : ℝˣ →ₜ* ℂˣ) :
    ∃ (s : ℂ) (ε : ZMod 2), χ = realUnitsCharacter s ε := by
  obtain ⟨s, hs, -⟩ := existsUnique_eq_expUnitHom_complex (χ.comp (expUnitHom 1))
  have hsq : (χ (-1) : ℂ) * χ (-1) = 1 := by
    rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
  rcases mul_self_eq_one_iff.1 hsq with h | h
  · refine ⟨s, 0, realUnits_ext (Units.ext ?_) (by rw [hs, realUnitsCharacter_comp_expUnitHom])⟩
    rw [h, realUnitsCharacter_neg_one]
    simp
  · refine ⟨s, 1, realUnits_ext (Units.ext ?_) (by rw [hs, realUnitsCharacter_comp_expUnitHom])⟩
    rw [h, realUnitsCharacter_neg_one, ZMod.val_one, pow_one]

/-- The exponent and the parity of `x ↦ |x| ^ s * sgn(x) ^ ε` are jointly determined by the
character. -/
theorem realUnitsCharacter_injective2 : Function.Injective2 realUnitsCharacter := by
  intro s t ε η h
  have hs : s = t := expUnitHom_injective <| by
    rw [← realUnitsCharacter_comp_expUnitHom s ε, h, realUnitsCharacter_comp_expUnitHom]
  have hε : ((-1 : ℂ)) ^ ε.val = (-1) ^ η.val := by
    rw [← realUnitsCharacter_neg_one s, ← realUnitsCharacter_neg_one t, h]
  refine ⟨hs, ?_⟩
  have key (e : ZMod 2) : e = 0 ∨ e = 1 := by decide +revert
  rcases key ε with rfl | rfl <;> rcases key η with rfl | rfl
  all_goals first | rfl | norm_num [ZMod.val_one] at hε

/-- Two characters `x ↦ |x| ^ s * sgn(x) ^ ε` agree exactly when their parameters do. -/
@[simp]
theorem realUnitsCharacter_inj {s t : ℂ} {ε η : ZMod 2} :
    realUnitsCharacter s ε = realUnitsCharacter t η ↔ s = t ∧ ε = η := by
  exact realUnitsCharacter_injective2.eq_iff

/-- **Classification of the continuous characters of `ℝˣ`.** The continuous characters of `ℝˣ`
are exactly the characters `x ↦ |x| ^ s * sgn(x) ^ ε`, for unique `s : ℂ` and `ε : ZMod 2`,
and multiplying characters adds their parameters. -/
def realUnitsCharacterEquiv : Multiplicative (ℂ × ZMod 2) ≃* (ℝˣ →ₜ* ℂˣ) :=
  MulEquiv.ofBijective
    ({ toFun p := realUnitsCharacter p.toAdd.1 p.toAdd.2
       map_one' := by simp
       map_mul' _ _ := realUnitsCharacter_add _ _ _ _ } : Multiplicative (ℂ × ZMod 2) →* _)
    ⟨realUnitsCharacter_injective2.uncurry.comp Multiplicative.toAdd.injective, fun χ ↦
      let ⟨s, ε, h⟩ := exists_eq_realUnitsCharacter χ
      ⟨.ofAdd (s, ε), h.symm⟩⟩

/-- The classification equivalence sends `(s, ε)` to `x ↦ |x| ^ s * sgn(x) ^ ε`. -/
@[simp]
theorem realUnitsCharacterEquiv_apply (s : ℂ) (ε : ZMod 2) :
    realUnitsCharacterEquiv (.ofAdd (s, ε)) = realUnitsCharacter s ε :=
  (rfl)

/-- The inverse classification equivalence recovers the parameters of a real-units character. -/
@[simp]
theorem realUnitsCharacterEquiv_symm_apply (s : ℂ) (ε : ZMod 2) :
    realUnitsCharacterEquiv.symm (realUnitsCharacter s ε) = .ofAdd (s, ε) :=
  (MulEquiv.symm_apply_eq realUnitsCharacterEquiv).2 rfl

/-! ### Characters of `ℂˣ` -/

/-- The character `z ↦ |z| ^ s * (z / |z|) ^ k` of `ℂˣ`, for a complex exponent `s` and an
angular frequency `k : ℤ`. -/
def complexUnitsCharacter (s : ℂ) (k : ℤ) : ℂˣ →ₜ* ℂˣ :=
  normCpowCharacter ℂ s * complexAngularCharacter ^ k

/-- Evaluating `complexUnitsCharacter s k` at `z` gives `|z| ^ s * (z / |z|) ^ k`. -/
@[simp]
theorem coe_complexUnitsCharacter_apply (s : ℂ) (k : ℤ) (z : ℂˣ) :
    (complexUnitsCharacter s k z : ℂ) = (‖(z : ℂ)‖ : ℂ) ^ s * ((z : ℂ) / ‖(z : ℂ)‖) ^ k := by
  simp [complexUnitsCharacter]

/-- With angular frequency `0`, `complexUnitsCharacter s 0` is the norm-power character
`z ↦ |z| ^ s`. -/
@[simp]
theorem complexUnitsCharacter_zero_right (s : ℂ) :
    complexUnitsCharacter s 0 = normCpowCharacter ℂ s := by
  simp [complexUnitsCharacter]

/-- With exponent `0`, `complexUnitsCharacter 0 k` is the power `(z / |z|) ^ k` of the angular
character. -/
@[simp]
theorem complexUnitsCharacter_zero_left (k : ℤ) :
    complexUnitsCharacter 0 k = complexAngularCharacter ^ k := by
  rw [complexUnitsCharacter, normCpowCharacter_zero]
  exact one_mul (complexAngularCharacter ^ k)

/-- Adding parameters multiplies the characters of `ℂˣ`. -/
@[simp]
theorem complexUnitsCharacter_add (s t : ℂ) (k l : ℤ) :
    complexUnitsCharacter (s + t) (k + l) =
      complexUnitsCharacter s k * complexUnitsCharacter t l := by
  rw [complexUnitsCharacter, complexUnitsCharacter, complexUnitsCharacter, normCpowCharacter_add,
    zpow_add]
  exact mul_mul_mul_comm (normCpowCharacter ℂ s) _ _ _

/-- Restricting `complexUnitsCharacter s k` to the positive reals gives `expUnitHom s`; the
angular frequency is invisible there. -/
theorem complexUnitsCharacter_comp_expUnitHom_one (s : ℂ) (k : ℤ) :
    (complexUnitsCharacter s k).comp (expUnitHom (1 : ℂ)) = expUnitHom s := by
  refine ContinuousMonoidHom.ext fun t ↦ Units.ext ?_
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective t
  rw [ContinuousMonoidHom.comp_toFun, coe_complexUnitsCharacter_apply, coe_expUnitHom_complex,
    coe_expUnitHom_complex]
  simp [← ofReal_exp, ofReal_exp_cpow]

/-- Restricting `complexUnitsCharacter s k` to the standard parametrization of the unit circle
gives `expUnitHom (k * I)`; the modulus exponent is invisible there. -/
theorem complexUnitsCharacter_comp_expUnitHom_I (s : ℂ) (k : ℤ) :
    (complexUnitsCharacter s k).comp (expUnitHom I) = expUnitHom (k * I) := by
  refine ContinuousMonoidHom.ext fun t ↦ Units.ext ?_
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective t
  rw [ContinuousMonoidHom.comp_toFun, coe_complexUnitsCharacter_apply, coe_expUnitHom_complex,
    coe_expUnitHom_complex]
  simp [← exp_int_mul]
  ring_nf

/-- Continuous characters of `ℂˣ` agree once they agree on the positive reals and on the unit
circle. -/
theorem complexUnits_ext {χ ψ : ℂˣ →ₜ* ℂˣ}
    (hpos : χ.comp (expUnitHom (1 : ℂ)) = ψ.comp (expUnitHom 1))
    (hcirc : χ.comp (expUnitHom I) = ψ.comp (expUnitHom I)) : χ = ψ := by
  refine ContinuousMonoidHom.ext fun z ↦ ?_
  have hz : z = expUnitHom (1 : ℂ) (.ofAdd (Real.log ‖(z : ℂ)‖)) *
      expUnitHom I (.ofAdd (arg z)) := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_expUnitHom_complex, coe_expUnitHom_complex, mul_one, ← ofReal_exp,
      Real.exp_log (norm_pos_iff.2 z.ne_zero), norm_mul_exp_arg_mul_I]
  rw [hz, map_mul, map_mul]
  exact congrArg₂ (· * ·) (DFunLike.congr_fun hpos _) (DFunLike.congr_fun hcirc _)

/-- **Every continuous character of `ℂˣ` is `z ↦ |z| ^ s * (z / |z|) ^ k`.** -/
theorem exists_eq_complexUnitsCharacter (χ : ℂˣ →ₜ* ℂˣ) :
    ∃ (s : ℂ) (k : ℤ), χ = complexUnitsCharacter s k := by
  obtain ⟨s, hs, -⟩ := existsUnique_eq_expUnitHom_complex (χ.comp (expUnitHom 1))
  obtain ⟨a, ha, -⟩ := existsUnique_eq_expUnitHom_complex (χ.comp (expUnitHom I))
  -- The circle parameter `a` is an integer multiple of `I`, since `exp (2 * π * I) = 1`.
  have h2pi : exp (2 * Real.pi * a) = 1 := by
    have h := DFunLike.congr_fun ha (.ofAdd (2 * Real.pi))
    have hone : expUnitHom I (.ofAdd (2 * Real.pi)) = 1 := Units.ext <| by
      rw [coe_expUnitHom_complex, Units.val_one, ofReal_mul, ofReal_ofNat, exp_two_pi_mul_I]
    rw [ContinuousMonoidHom.comp_toFun, hone, map_one] at h
    have h' := congrArg Units.val h
    rwa [coe_expUnitHom_complex, Units.val_one, eq_comm, ofReal_mul, ofReal_ofNat] at h'
  obtain ⟨k, hk⟩ := exp_eq_one_iff.1 h2pi
  have hak : a = k * I := by
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
    apply mul_left_cancel₀ hpi
    rw [hk]
    ring
  refine ⟨s, k, complexUnits_ext ?_ ?_⟩
  · rw [hs, complexUnitsCharacter_comp_expUnitHom_one]
  · rw [ha, hak, complexUnitsCharacter_comp_expUnitHom_I]

/-- The exponent and the angular frequency of `z ↦ |z| ^ s * (z / |z|) ^ k` are jointly
determined by the character. -/
theorem complexUnitsCharacter_injective2 : Function.Injective2 complexUnitsCharacter := by
  intro s t k l h
  have hs : s = t := expUnitHom_injective <| by
    rw [← complexUnitsCharacter_comp_expUnitHom_one s k, h,
      complexUnitsCharacter_comp_expUnitHom_one]
  have hk : (k : ℂ) * I = l * I := expUnitHom_injective <| by
    rw [← complexUnitsCharacter_comp_expUnitHom_I s k, h, complexUnitsCharacter_comp_expUnitHom_I]
  exact ⟨hs, by exact_mod_cast mul_right_cancel₀ I_ne_zero hk⟩

/-- Two characters `z ↦ |z| ^ s * (z / |z|) ^ k` agree exactly when their parameters do. -/
@[simp]
theorem complexUnitsCharacter_inj {s t : ℂ} {k l : ℤ} :
    complexUnitsCharacter s k = complexUnitsCharacter t l ↔ s = t ∧ k = l := by
  exact complexUnitsCharacter_injective2.eq_iff

/-- **Classification of the continuous characters of `ℂˣ`.** The continuous characters of `ℂˣ`
are exactly the characters `z ↦ |z| ^ s * (z / |z|) ^ k`, for unique `s : ℂ` and `k : ℤ`, and
multiplying characters adds their parameters. -/
def complexUnitsCharacterEquiv : Multiplicative (ℂ × ℤ) ≃* (ℂˣ →ₜ* ℂˣ) :=
  MulEquiv.ofBijective
    ({ toFun p := complexUnitsCharacter p.toAdd.1 p.toAdd.2
       map_one' := by simp
       map_mul' _ _ := complexUnitsCharacter_add _ _ _ _ } : Multiplicative (ℂ × ℤ) →* _)
    ⟨complexUnitsCharacter_injective2.uncurry.comp Multiplicative.toAdd.injective, fun χ ↦
      let ⟨s, k, h⟩ := exists_eq_complexUnitsCharacter χ
      ⟨.ofAdd (s, k), h.symm⟩⟩

/-- The classification equivalence sends `(s, k)` to `z ↦ |z| ^ s * (z / |z|) ^ k`. -/
@[simp]
theorem complexUnitsCharacterEquiv_apply (s : ℂ) (k : ℤ) :
    complexUnitsCharacterEquiv (.ofAdd (s, k)) = complexUnitsCharacter s k :=
  (rfl)

/-- The inverse classification equivalence recovers the parameters of a complex-units
character. -/
@[simp]
theorem complexUnitsCharacterEquiv_symm_apply (s : ℂ) (k : ℤ) :
    complexUnitsCharacterEquiv.symm (complexUnitsCharacter s k) = .ofAdd (s, k) :=
  (MulEquiv.symm_apply_eq complexUnitsCharacterEquiv).2 rfl

end TauCeti
