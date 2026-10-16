/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.ArchimedeanCharacter
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Shift
public import TauCeti.NumberTheory.NumberField.Global.InfinityType.Basic
public import TauCeti.NumberTheory.NumberField.Global.Places.Connected

import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# The infinity type of a Hecke character

Let `χ` be a Hecke character of a number field `K`.  Restricting `χ` along the embedding of the
units of an archimedean completion `K_w` into the idele class group gives a continuous character
of `K_wˣ`, the **component of `χ` at `w`**.  Transporting it along `K_w ≃ ℝ` at a real place and
along `K_w ≃ ℂ` at a complex place (the identification extending the embedding `w.embedding`
chosen by Mathlib), the classification of continuous characters of `ℝˣ` and `ℂˣ` writes these
components uniquely as

* `x ↦ |x| ^ s_w * sgn(x) ^ ε_w` at a real place, with `s_w : ℂ` and `ε_w : ZMod 2`, and
* `z ↦ |z| ^ s_w * (z / |z|) ^ k_w` at a complex place, with `s_w : ℂ` and `k_w : ℤ`.

These parameters form the **infinity type** `χ.infinityType : ContinuousInfinityType K`.  The
exponents are complex: the norm character `‖·‖ ^ s` has exponent `s` at every real place and
`2 * s` at every complex place, because the normalized absolute value at a complex place is the
square of the usual one.  In particular `‖·‖ ^ s` has finite order only for `s = 0`, while a Hecke
character of finite order has vanishing exponents and angular frequencies, so its infinity type is
a `FiniteOrderInfinityType`: signs at the real places and nothing else.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter.infiniteComponent`: the character of `K_wˣ`
  obtained by restricting a Hecke character.
* `TauCeti.GlobalNumberFields.HeckeCharacter.realComponent`,
  `TauCeti.GlobalNumberFields.HeckeCharacter.complexComponent`: the components at real and
  complex places as characters of `ℝˣ` and `ℂˣ`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.infinityType`: the continuous infinity type of a
  Hecke character.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.infinityType_eq_iff`: the infinity type is the
  unique continuous infinity type whose parameters describe every real and complex component.
* `TauCeti.GlobalNumberFields.HeckeCharacter.infinityType_mul`: multiplying Hecke characters adds
  their infinity types.
* `TauCeti.GlobalNumberFields.HeckeCharacter.infinityType_normPow`: the infinity type of the norm
  character `‖·‖ ^ s`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.exists_finiteOrderInfinityType`: the infinity type of
  a finite-order Hecke character comes from a finite-order infinity type.
* `TauCeti.GlobalNumberFields.HeckeCharacter.isFiniteOrder_normPow_iff`: `‖·‖ ^ s` has finite
  order exactly when `s = 0`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.re_realExponent_infinityType`,
  `TauCeti.GlobalNumberFields.HeckeCharacter.re_complexExponent_infinityType`: the real parts of the
  modulus exponents are the shift `σ` of `χ` at every real place and `2 * σ` at every complex
  place, since `|χ| = ‖·‖ ^ σ`.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §2.3 and §3.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField NNReal

namespace TauCeti.GlobalNumberFields

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-! ### Archimedean components -/

/-- The **component of a Hecke character `χ` at an infinite place `w`**: the continuous character
of `K_wˣ` obtained by composing `χ` with the embedding of `K_wˣ` into the idele class group. -/
def infiniteComponent (χ : HeckeCharacter K) (w : InfinitePlace K) : w.Completionˣ →ₜ* ℂˣ :=
  χ.comp ⟨IdeleClassGroup.ofCompletion (𝓞 K) K w, IdeleClassGroup.continuous_ofCompletion _ _ w⟩

/-- The component of `χ` at `w` evaluates `χ` on the idele class concentrated at `w`. -/
@[simp]
theorem infiniteComponent_apply (χ : HeckeCharacter K) (w : InfinitePlace K)
    (u : w.Completionˣ) :
    χ.infiniteComponent w u = χ (IdeleClassGroup.ofCompletion (𝓞 K) K w u) :=
  (rfl)

/-- The trivial Hecke character has trivial components. -/
@[simp]
theorem infiniteComponent_one (w : InfinitePlace K) :
    (1 : HeckeCharacter K).infiniteComponent w = 1 :=
  (rfl)

/-- Components of a product of Hecke characters are the products of the components. -/
@[simp]
theorem infiniteComponent_mul (χ ψ : HeckeCharacter K) (w : InfinitePlace K) :
    (χ * ψ).infiniteComponent w = χ.infiniteComponent w * ψ.infiniteComponent w :=
  (rfl)

/-- Components of the inverse of a Hecke character are the inverses of the components. -/
@[simp]
theorem infiniteComponent_inv (χ : HeckeCharacter K) (w : InfinitePlace K) :
    χ⁻¹.infiniteComponent w = (χ.infiniteComponent w)⁻¹ :=
  (rfl)

/-- Components of a power of a Hecke character are the powers of the components. -/
@[simp]
theorem infiniteComponent_pow (χ : HeckeCharacter K) (n : ℕ) (w : InfinitePlace K) :
    (χ ^ n).infiniteComponent w = χ.infiniteComponent w ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- The **component of a Hecke character at a real place `w`**, as a character of `ℝˣ`: the
component at `w` transported along the isomorphism `ℝ ≃ K_w` inverse to the real extension
embedding. -/
def realComponent (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsReal}) :
    ℝˣ →ₜ* ℂˣ :=
  (χ.infiniteComponent w.1).comp
    (Units.mapContinuousMulEquiv (continuousMulEquivRealOfIsReal w.2)).symm

/-- The component of `χ` at a real place `w` evaluates the component of `χ` at `w` on the unit of
`K_w` corresponding to a real unit. -/
@[simp]
theorem realComponent_apply (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsReal})
    (x : ℝˣ) :
    χ.realComponent w x = χ.infiniteComponent w.1
      ((Units.mapContinuousMulEquiv (continuousMulEquivRealOfIsReal w.2)).symm x) :=
  (rfl)

/-- The **component of a Hecke character at a complex place `w`**, as a character of `ℂˣ`: the
component at `w` transported along the isomorphism `ℂ ≃ K_w` inverse to the extension of
`w.embedding`. -/
def complexComponent (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsComplex}) :
    ℂˣ →ₜ* ℂˣ :=
  (χ.infiniteComponent w.1).comp
    (Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex w.2)).symm

/-- The component of `χ` at a complex place `w` evaluates the component of `χ` at `w` on the unit
of `K_w` corresponding to a complex unit. -/
@[simp]
theorem complexComponent_apply (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsComplex})
    (z : ℂˣ) :
    χ.complexComponent w z = χ.infiniteComponent w.1
      ((Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex w.2)).symm z) :=
  (rfl)

/-- The trivial Hecke character has trivial real components. -/
@[simp]
theorem realComponent_one (w : {w : InfinitePlace K // w.IsReal}) :
    (1 : HeckeCharacter K).realComponent w = 1 :=
  (rfl)

/-- Real components of a product of Hecke characters are the products of the real components. -/
@[simp]
theorem realComponent_mul (χ ψ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsReal}) :
    (χ * ψ).realComponent w = χ.realComponent w * ψ.realComponent w :=
  (rfl)

/-- Real components of the inverse of a Hecke character are the inverses of the real
components. -/
@[simp]
theorem realComponent_inv (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsReal}) :
    χ⁻¹.realComponent w = (χ.realComponent w)⁻¹ :=
  (rfl)

/-- Real components of a power of a Hecke character are the powers of the real components. -/
@[simp]
theorem realComponent_pow (χ : HeckeCharacter K) (n : ℕ) (w : {w : InfinitePlace K // w.IsReal}) :
    (χ ^ n).realComponent w = χ.realComponent w ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- The trivial Hecke character has trivial complex components. -/
@[simp]
theorem complexComponent_one (w : {w : InfinitePlace K // w.IsComplex}) :
    (1 : HeckeCharacter K).complexComponent w = 1 :=
  (rfl)

/-- Complex components of a product of Hecke characters are the products of the complex
components. -/
@[simp]
theorem complexComponent_mul (χ ψ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsComplex}) :
    (χ * ψ).complexComponent w = χ.complexComponent w * ψ.complexComponent w :=
  (rfl)

/-- Complex components of the inverse of a Hecke character are the inverses of the complex
components. -/
@[simp]
theorem complexComponent_inv (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsComplex}) :
    χ⁻¹.complexComponent w = (χ.complexComponent w)⁻¹ :=
  (rfl)

/-- Complex components of a power of a Hecke character are the powers of the complex
components. -/
@[simp]
theorem complexComponent_pow (χ : HeckeCharacter K) (n : ℕ)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (χ ^ n).complexComponent w = χ.complexComponent w ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-! ### The infinity type -/

/-- The **infinity type** of a Hecke character `χ`: at a real place `w` the parameters `(s, ε)`
with `χ.realComponent w = |·| ^ s * sgn ^ ε`, and at a complex place `w` the parameters `(s, k)`
with `χ.complexComponent w = |·| ^ s * (· / |·|) ^ k`.  The exponents `s` are complex. -/
def infinityType (χ : HeckeCharacter K) : ContinuousInfinityType K where
  realExponent w := (realUnitsCharacterEquiv.symm (χ.realComponent w)).toAdd.1
  realParity w := (realUnitsCharacterEquiv.symm (χ.realComponent w)).toAdd.2
  complexExponent w := (complexUnitsCharacterEquiv.symm (χ.complexComponent w)).toAdd.1
  complexAngularFrequency w := (complexUnitsCharacterEquiv.symm (χ.complexComponent w)).toAdd.2

/-- The component of `χ` at a real place `w` is `x ↦ |x| ^ s * sgn(x) ^ ε`, for the real
modulus exponent `s` and parity `ε` of the infinity type of `χ` at `w`. -/
theorem realComponent_eq (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsReal}) :
    χ.realComponent w =
      realUnitsCharacter (χ.infinityType.realExponent w) (χ.infinityType.realParity w) := by
  obtain ⟨s, ε, h⟩ := exists_eq_realUnitsCharacter (χ.realComponent w)
  simp only [infinityType, h, realUnitsCharacterEquiv_symm_apply, toAdd_ofAdd]

/-- The component of `χ` at a complex place `w` is `z ↦ |z| ^ s * (z / |z|) ^ k`, for the
complex modulus exponent `s` and angular frequency `k` of the infinity type of `χ` at `w`. -/
theorem complexComponent_eq (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsComplex}) :
    χ.complexComponent w = complexUnitsCharacter (χ.infinityType.complexExponent w)
      (χ.infinityType.complexAngularFrequency w) := by
  obtain ⟨s, k, h⟩ := exists_eq_complexUnitsCharacter (χ.complexComponent w)
  simp only [infinityType, h, complexUnitsCharacterEquiv_symm_apply, toAdd_ofAdd]

/-- **Characterization of the infinity type.**  A continuous infinity type `t` is the infinity
type of `χ` exactly when its parameters describe every real and every complex component of
`χ`. -/
theorem infinityType_eq_iff {χ : HeckeCharacter K} {t : ContinuousInfinityType K} :
    χ.infinityType = t ↔
      (∀ w, χ.realComponent w = realUnitsCharacter (t.realExponent w) (t.realParity w)) ∧
        ∀ w, χ.complexComponent w =
          complexUnitsCharacter (t.complexExponent w) (t.complexAngularFrequency w) := by
  refine ⟨fun h ↦ h ▸ ⟨χ.realComponent_eq, χ.complexComponent_eq⟩, fun ⟨hr, hc⟩ ↦ ?_⟩
  have hr' w := realUnitsCharacter_inj.1 ((χ.realComponent_eq w).symm.trans (hr w))
  have hc' w := complexUnitsCharacter_inj.1 ((χ.complexComponent_eq w).symm.trans (hc w))
  ext w
  exacts [(hr' w).1, (hr' w).2, (hc' w).1, (hc' w).2]

/-- The trivial Hecke character has the zero infinity type. -/
@[simp]
theorem infinityType_one : (1 : HeckeCharacter K).infinityType = 0 :=
  infinityType_eq_iff.2 ⟨fun _ ↦ by simp, fun _ ↦ by simp⟩

/-- **Multiplying Hecke characters adds their infinity types.** -/
@[simp]
theorem infinityType_mul (χ ψ : HeckeCharacter K) :
    (χ * ψ).infinityType = χ.infinityType + ψ.infinityType :=
  infinityType_eq_iff.2
    ⟨fun w ↦ by simp [χ.realComponent_eq, ψ.realComponent_eq],
      fun w ↦ by simp [χ.complexComponent_eq, ψ.complexComponent_eq]⟩

/-- The infinity type of a power of a Hecke character is the corresponding multiple. -/
@[simp]
theorem infinityType_pow (χ : HeckeCharacter K) (n : ℕ) :
    (χ ^ n).infinityType = n • χ.infinityType := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, infinityType_mul, ih, succ_nsmul]

/-- The infinity type of the inverse of a Hecke character is the negated infinity type. -/
@[simp]
theorem infinityType_inv (χ : HeckeCharacter K) : χ⁻¹.infinityType = -χ.infinityType :=
  eq_neg_of_add_eq_zero_left <| by rw [← infinityType_mul, inv_mul_cancel, infinityType_one]

/-! ### Characters of finite order -/

/-- **The infinity type of a finite-order Hecke character.**  Its modulus exponents and complex
angular frequencies vanish, so it is the continuous infinity type of its real parities. -/
theorem infinityType_eq_toContinuous_realParity {χ : HeckeCharacter K}
    (hχ : χ.IsFiniteOrder) :
    χ.infinityType = FiniteOrderInfinityType.toContinuous χ.infinityType.realParity := by
  obtain ⟨n, hn, hχn⟩ := isOfFinOrder_iff_pow_eq_one.1 hχ
  have h := congrArg infinityType hχn
  rw [infinityType_pow, infinityType_one] at h
  ext w
  · simpa [hn.ne'] using congrArg (fun t : ContinuousInfinityType K ↦ t.realExponent w) h
  · simp
  · simpa [hn.ne'] using congrArg (fun t : ContinuousInfinityType K ↦ t.complexExponent w) h
  · simpa [hn.ne'] using
      congrArg (fun t : ContinuousInfinityType K ↦ t.complexAngularFrequency w) h

/-- The infinity type of a Hecke character of finite order is a finite-order infinity type:
signs at the real places, with no modulus exponents and no complex angular frequencies. -/
theorem exists_finiteOrderInfinityType {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    ∃ ε : FiniteOrderInfinityType K, χ.infinityType = FiniteOrderInfinityType.toContinuous ε :=
  ⟨_, infinityType_eq_toContinuous_realParity hχ⟩

/-! ### The norm characters -/

/-- The component of the norm character `‖·‖ ^ s` at an infinite place `w` sends `u` to
`|u|_w ^ s`, for the normalized absolute value `|·|_w` of `K_w`. -/
theorem coe_infiniteComponent_normPow_apply (s : ℂ) (w : InfinitePlace K) (u : w.Completionˣ) :
    ((normPow K s).infiniteComponent w u : ℂ) =
      ((completionNormalizedAbsValue w u : ℝ) : ℂ) ^ s := by
  simp [IdeleClassGroup.ofCompletion_apply]

/-- The component of the norm character `‖·‖ ^ s` at a real place is `x ↦ |x| ^ s`. -/
@[simp]
theorem realComponent_normPow (s : ℂ) (w : {w : InfinitePlace K // w.IsReal}) :
    (normPow K s).realComponent w = normCpowCharacter ℝ s := by
  ext x
  simp [completionNormalizedAbsValue_of_isReal _ w.2]

/-- The component of the norm character `‖·‖ ^ s` at a complex place is `z ↦ |z| ^ (2 * s)`,
since the normalized absolute value of a complex place is the square of the usual one. -/
@[simp]
theorem complexComponent_normPow (s : ℂ) (w : {w : InfinitePlace K // w.IsComplex}) :
    (normPow K s).complexComponent w = normCpowCharacter ℂ (2 * s) := by
  ext z
  simp [completionNormalizedAbsValue_of_isComplex _ w.2, ofReal_pow_cpow (norm_nonneg _)]

/-- **The infinity type of the norm character `‖·‖ ^ s`**: modulus exponent `s` and parity `0` at
every real place, and modulus exponent `2 * s` and angular frequency `0` at every complex place,
since the normalized absolute value of a complex place is the square of the usual one. -/
theorem infinityType_normPow (s : ℂ) :
    (normPow K s).infinityType =
      { realExponent := fun _ ↦ s
        realParity := 0
        complexExponent := fun _ ↦ 2 * s
        complexAngularFrequency := 0 } :=
  infinityType_eq_iff.2 ⟨fun w ↦ by simp, fun w ↦ by simp⟩

/-- **The norm character `‖·‖ ^ s` has finite order exactly when `s = 0`.**  For `s ≠ 0` its
modulus exponents at the infinite places are nonzero, although for purely imaginary `s` its
shift vanishes. -/
theorem isFiniteOrder_normPow_iff {s : ℂ} : (normPow K s).IsFiniteOrder ↔ s = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ normPow_zero (K := K) ▸ IsOfFinOrder.one⟩
  have ht := infinityType_eq_toContinuous_realParity h
  rw [infinityType_normPow] at ht
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  rcases w.isReal_or_isComplex with hw | hw
  · simpa using congrArg (fun t : ContinuousInfinityType K ↦ t.realExponent ⟨w, hw⟩) ht
  · simpa using congrArg (fun t : ContinuousInfinityType K ↦ t.complexExponent ⟨w, hw⟩) ht

/-! ### Absolute values of the components and the shift -/

/-- **The absolute value of an infinite component is the shift-th power of the normalized
absolute value.** -/
theorem norm_infiniteComponent_apply (χ : HeckeCharacter K) (w : InfinitePlace K)
    (u : w.Completionˣ) :
    ‖(χ.infiniteComponent w u : ℂ)‖ = completionNormalizedAbsValue w u ^ χ.shift := by
  rw [infiniteComponent_apply, norm_apply_eq_rpow_shift,
    IdeleClassGroup.ofCompletion_apply, ideleClassNorm_mk, coe_ideleNorm_ofCompletion]

/-- **The absolute value of a real component is the shift-th power of `|x|`.**  At a real place
`w`, the component of `χ` satisfies `|χ_w(x)| = |x| ^ σ`, where `σ` is the shift of `χ`. -/
theorem norm_realComponent_apply (χ : HeckeCharacter K) (w : {w : InfinitePlace K // w.IsReal})
    (x : ℝˣ) : ‖(χ.realComponent w x : ℂ)‖ = |(x : ℝ)| ^ χ.shift := by
  rw [realComponent_apply, norm_infiniteComponent_apply,
    completionNormalizedAbsValue_of_isReal _ w.2]
  simp

/-- **The absolute value of a complex component is the power of `‖z‖` with exponent twice the
shift.**  At a complex place `w`, the component of `χ` satisfies
`|χ_w(z)| = |z| ^ (2 * σ)`, where `σ` is the shift of `χ`, since the normalized absolute value of
a complex place is the square of the usual one. -/
theorem norm_complexComponent_apply (χ : HeckeCharacter K)
    (w : {w : InfinitePlace K // w.IsComplex}) (z : ℂˣ) :
    ‖(χ.complexComponent w z : ℂ)‖ = ‖(z : ℂ)‖ ^ (2 * χ.shift) := by
  rw [complexComponent_apply, norm_infiniteComponent_apply,
    completionNormalizedAbsValue_of_isComplex _ w.2]
  simp only [Units.symm_mapContinuousMulEquiv, Units.mapContinuousMulEquiv_apply, Units.coe_map,
    MonoidHom.coe_ofClass, ContinuousMulEquiv.coe_toMulEquiv,
    norm_continuousMulEquivComplexOfIsComplex_symm]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- **The real part of a real modulus exponent is the shift.**  The infinity type of `χ` has a
complex exponent `s_w` at each real place `w`; its real part is the shift of `χ`, independently
of `w`. -/
@[simp]
theorem re_realExponent_infinityType (χ : HeckeCharacter K)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (χ.infinityType.realExponent w).re = χ.shift := by
  have h := χ.norm_realComponent_apply w (Units.mk0 2 two_ne_zero)
  rw [realComponent_eq, norm_coe_realUnitsCharacter_apply, Units.val_mk0, abs_two] at h
  exact (Real.rpow_right_inj two_pos (by norm_num)).1 h

/-- **The real part of a complex modulus exponent is twice the shift.**  The infinity type of
`χ` has a complex exponent `s_w` at each complex place `w`; its real part is `2 * σ` for the shift
`σ` of `χ`, independently of `w`. -/
@[simp]
theorem re_complexExponent_infinityType (χ : HeckeCharacter K)
    (w : {w : InfinitePlace K // w.IsComplex}) :
    (χ.infinityType.complexExponent w).re = 2 * χ.shift := by
  have h := χ.norm_complexComponent_apply w (Units.mk0 2 two_ne_zero)
  rw [complexComponent_eq, norm_coe_complexUnitsCharacter_apply, Units.val_mk0,
    Complex.norm_two] at h
  exact (Real.rpow_right_inj two_pos (by norm_num)).1 h

end HeckeCharacter

end TauCeti.GlobalNumberFields
