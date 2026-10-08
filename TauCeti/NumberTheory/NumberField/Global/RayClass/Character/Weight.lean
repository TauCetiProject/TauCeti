/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Weight
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Basic
import TauCeti.NumberTheory.NumberField.Global.RayClass.Finite

/-!
# Ideal weights of ray class characters

A ray class character is defined on the ray class group of its modulus. Extending its induced
evaluation `χ.onIdeals` on prime-to integral ideals by zero on the remaining ideals gives a
completely multiplicative ideal weight. Its bad primes are
exactly the prime divisors of the finite part of the modulus. Finiteness of the ray class group
also makes the weight unitary, so its norm coefficients can be used in the Dirichlet series of
arithmetic characters.

The trivial character extends to the indicator of ideals prime to the modulus, which is generally
different from the everywhere-good unitary weight. Pointwise products still commute with the
extension.

The zero extension here is the usual convention for the Dirichlet series of a ray class
character. See Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section

open NumberField IsDedekindDomain
open scoped NumberField

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

open Classical in
/-- Extend the induced evaluation `χ.onIdeals` on prime-to integral ideals by zero on all other
ideals. -/
noncomputable def toMultiplicativeIdealWeight (χ : RayClassCharacter 𝔪) :
    TauCeti.MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun I := if h : Ideal.IsPrimeTo I 𝔪.support then
          (χ.onIdeals ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
            (Ideal.isPrimeTo_iff.mp h)⟩ : ℂ) else 0
      map_zero' := by simp
      map_one' := by
        simp only [Ideal.one_eq_top, Ideal.isPrimeTo_top, dite_true]
        have htop : (⟨⊤, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
            (Ideal.isPrimeTo_iff.mp Ideal.isPrimeTo_top)⟩ : integralIdealsPrimeTo 𝔪) = 1 :=
          Subtype.ext (by simp [Ideal.one_eq_top])
        rw [htop, map_one]
        rfl
      map_mul' I J := by
        classical
        by_cases hI : Ideal.IsPrimeTo I 𝔪.support <;>
          by_cases hJ : Ideal.IsPrimeTo J 𝔪.support
        · have hIJ : Ideal.IsPrimeTo (I * J) 𝔪.support :=
            Ideal.isPrimeTo_mul_iff.mpr ⟨hI, hJ⟩
          simp only [hI, hJ, hIJ, dite_true]
          exact_mod_cast map_mul χ.onIdeals
            ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
              (Ideal.isPrimeTo_iff.mp hI)⟩
            ⟨J, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
              (Ideal.isPrimeTo_iff.mp hJ)⟩
        · have hIJ : ¬ Ideal.IsPrimeTo (I * J) 𝔪.support :=
            fun h ↦ hJ (Ideal.isPrimeTo_mul_iff.mp h).2
          simp [hIJ, hJ]
        · have hIJ : ¬ Ideal.IsPrimeTo (I * J) 𝔪.support :=
            fun h ↦ hI (Ideal.isPrimeTo_mul_iff.mp h).1
          simp [hIJ, hI]
        · have hIJ : ¬ Ideal.IsPrimeTo (I * J) 𝔪.support :=
            fun h ↦ hI (Ideal.isPrimeTo_mul_iff.mp h).1
          simp [hIJ, hI] }
  finite_setOf_apply_eq_zero := by
    convert 𝔪.support.finite_toSet using 1
    ext 𝔭
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    -- Reduce the FunLike coercion to the defining value of the homomorphism.
    change (if h : Ideal.IsPrimeTo 𝔭.asIdeal 𝔪.support then
        (χ.onIdeals ⟨𝔭.asIdeal, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
          (Ideal.isPrimeTo_iff.mp h)⟩ : ℂ) else 0) = 0 ↔ 𝔭 ∈ 𝔪.support
    by_cases h : 𝔭 ∈ 𝔪.support
    · have hbad : ¬ Ideal.IsPrimeTo 𝔭.asIdeal 𝔪.support :=
        fun hg ↦ (Ideal.isPrimeTo_asIdeal_iff.mp hg) (by simpa using h)
      simp [h, hbad]
    · have hgood : Ideal.IsPrimeTo 𝔭.asIdeal 𝔪.support :=
        Ideal.isPrimeTo_asIdeal_iff.mpr h
      simp [h, hgood]

/-- On an ideal prime to the modulus, the extended weight equals the character value. -/
@[simp]
theorem toMultiplicativeIdealWeight_apply_of_isPrimeTo (χ : RayClassCharacter 𝔪)
    {I : Ideal (𝓞 K)} (hI : Ideal.IsPrimeTo I 𝔪.support) :
    χ.toMultiplicativeIdealWeight I =
      (χ.onIdeals ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
        (Ideal.isPrimeTo_iff.mp hI)⟩ : ℂ) := by
  classical
  -- Reduce the FunLike coercion to the defining value of the homomorphism.
  change (if h : Ideal.IsPrimeTo I 𝔪.support then
      (χ.onIdeals ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
        (Ideal.isPrimeTo_iff.mp h)⟩ : ℂ) else 0) = _
  simp [hI]

/-- The extended character vanishes on ideals meeting the finite part of its modulus. -/
@[simp]
theorem toMultiplicativeIdealWeight_apply_of_not_isPrimeTo (χ : RayClassCharacter 𝔪)
    {I : Ideal (𝓞 K)} (hI : ¬ Ideal.IsPrimeTo I 𝔪.support) :
    χ.toMultiplicativeIdealWeight I = 0 := by
  classical
  -- Reduce the FunLike coercion to the defining value of the homomorphism.
  change (if h : Ideal.IsPrimeTo I 𝔪.support then
      (χ.onIdeals ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
        (Ideal.isPrimeTo_iff.mp h)⟩ : ℂ) else 0) = 0
  simp [hI]

/-- The bad primes of the ideal weight are precisely the finite primes of the modulus. -/
@[simp]
theorem badPrimes_toMultiplicativeIdealWeight (χ : RayClassCharacter 𝔪) :
    χ.toMultiplicativeIdealWeight.badPrimes = 𝔪.support := by
  ext 𝔭
  simp only [TauCeti.MultiplicativeIdealWeight.mem_badPrimes]
  by_cases h : 𝔭 ∈ 𝔪.support
  · have hbad : ¬ Ideal.IsPrimeTo 𝔭.asIdeal 𝔪.support :=
      fun hg ↦ (Ideal.isPrimeTo_asIdeal_iff.mp hg) (by simpa using h)
    simp [h, toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hbad]
  · have hgood : Ideal.IsPrimeTo 𝔭.asIdeal 𝔪.support :=
      Ideal.isPrimeTo_asIdeal_iff.mpr (by simpa using h)
    simp [h, toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hgood]

/-- The trivial ray class character gives the indicator weight away from the modulus. -/
@[simp]
theorem toMultiplicativeIdealWeight_one :
    toMultiplicativeIdealWeight (1 : RayClassCharacter 𝔪) =
      TauCeti.MultiplicativeIdealWeight.ofBadPrimes 𝔪.support 𝔪.support.finite_toSet := by
  ext I
  by_cases hI : Ideal.IsPrimeTo I 𝔪.support
  · rw [toMultiplicativeIdealWeight_apply_of_isPrimeTo _ hI,
      TauCeti.MultiplicativeIdealWeight.ofBadPrimes_apply]
    simp [hI]
  · rw [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo _ hI,
      TauCeti.MultiplicativeIdealWeight.ofBadPrimes_apply]
    simp [hI]

/-- Pointwise multiplication of ray class characters agrees with multiplication of ideal
weights, including at ideals meeting the modulus. -/
@[simp]
theorem toMultiplicativeIdealWeight_mul (χ ψ : RayClassCharacter 𝔪) :
    toMultiplicativeIdealWeight (χ * ψ) =
      χ.toMultiplicativeIdealWeight * ψ.toMultiplicativeIdealWeight := by
  ext I
  by_cases hI : Ideal.IsPrimeTo I 𝔪.support
  · simp [toMultiplicativeIdealWeight_apply_of_isPrimeTo, hI,
      TauCeti.MultiplicativeIdealWeight.mul_apply, MonoidHom.mul_apply]
  · simp [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo, hI,
      TauCeti.MultiplicativeIdealWeight.mul_apply]

/-- Distinct ray class characters have distinct ideal weights: evaluation on the prime-to
integral ideals already determines a ray class character. -/
theorem toMultiplicativeIdealWeight_injective :
    Function.Injective (toMultiplicativeIdealWeight (𝔪 := 𝔪)) := by
  intro χ ψ h
  apply RayClassCharacter.ext
  intro I
  apply Units.ext
  have hI : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) 𝔪.support :=
    Ideal.isPrimeTo_iff.mpr (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp I.2)
  have hval := congrArg (fun w : TauCeti.MultiplicativeIdealWeight K ↦
    w (I : Ideal (𝓞 K))) h
  simpa only [toMultiplicativeIdealWeight_apply_of_isPrimeTo (hI := hI)] using hval

/-- A ray class character gives a unitary ideal weight, extended by zero at bad primes. -/
noncomputable def toUnitaryIdealWeight (χ : RayClassCharacter 𝔪) :
    TauCeti.UnitaryIdealWeight K :=
  TauCeti.UnitaryIdealWeight.ofPowEqOne χ.toMultiplicativeIdealWeight
    (n := Nat.card (RayClassGroup 𝔪)) Nat.card_pos.ne' (fun 𝔭 h𝔭 ↦ by
      have hgood : Ideal.IsPrimeTo 𝔭.asIdeal 𝔪.support :=
        Ideal.isPrimeTo_asIdeal_iff.mpr (by simpa [badPrimes_toMultiplicativeIdealWeight] using h𝔭)
      rw [toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hgood]
      rw [onIdeals_apply, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one',
        map_one, Units.val_one])

/-- The underlying multiplicative weight of the unitary extension. -/
@[simp]
theorem val_toUnitaryIdealWeight (χ : RayClassCharacter 𝔪) :
    χ.toUnitaryIdealWeight.1 = χ.toMultiplicativeIdealWeight := by
  simp [toUnitaryIdealWeight]

/-- The unitary extension respects pointwise multiplication of characters. -/
@[simp]
theorem toUnitaryIdealWeight_mul (χ ψ : RayClassCharacter 𝔪) :
    (χ * ψ).toUnitaryIdealWeight = χ.toUnitaryIdealWeight * ψ.toUnitaryIdealWeight := by
  apply Subtype.ext
  simp

/-- Increasing the modulus restricts the induced character's ideal weight away from the finite
primes of the larger modulus. -/
theorem toUnitaryIdealWeight_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) :
    (induced h χ).toUnitaryIdealWeight =
      χ.toUnitaryIdealWeight.restrictAway 𝔫.support 𝔫.support.finite_toSet := by
  apply Subtype.ext
  ext I
  by_cases hI : Ideal.IsPrimeTo I 𝔫.support
  · have hI𝔪 : Ideal.IsPrimeTo I 𝔪.support := hI.mono (Modulus.support_mono h)
    rw [TauCeti.UnitaryIdealWeight.val_restrictAway,
      TauCeti.MultiplicativeIdealWeight.restrictAway_apply]
    simp only [hI, ite_true]
    rw [val_toUnitaryIdealWeight, val_toUnitaryIdealWeight,
      toMultiplicativeIdealWeight_apply_of_isPrimeTo _ hI,
      toMultiplicativeIdealWeight_apply_of_isPrimeTo _ hI𝔪,
      onIdeals_induced]
    congr 2
    exact Subtype.ext (coe_integralIdealsPrimeToInclusion h _)
  · rw [TauCeti.UnitaryIdealWeight.val_restrictAway,
      TauCeti.MultiplicativeIdealWeight.restrictAway_apply]
    simp only [hI, ite_false]
    rw [val_toUnitaryIdealWeight,
      toMultiplicativeIdealWeight_apply_of_not_isPrimeTo _ hI]

/-- The unitary extensions distinguish ray class characters. -/
theorem toUnitaryIdealWeight_injective :
    Function.Injective (toUnitaryIdealWeight (𝔪 := 𝔪)) := by
  intro χ ψ h
  apply toMultiplicativeIdealWeight_injective
  simpa only [← val_toUnitaryIdealWeight] using congrArg Subtype.val h

end TauCeti.GlobalNumberFields.RayClassCharacter
