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
different from the everywhere-good unitary weight, except at the trivial modulus
(`toUnitaryIdealWeight_one`). Pointwise products still commute with the extension.

The zero extension here is the usual convention for the Dirichlet series of a ray class
character. See Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section

open NumberField IsDedekindDomain
open scoped NumberField

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- Extend the induced evaluation `χ.onIdeals` on prime-to integral ideals by zero on all other
ideals. -/
noncomputable def toMultiplicativeIdealWeight (χ : RayClassCharacter 𝔪) :
    TauCeti.MultiplicativeIdealWeight K :=
  TauCeti.MultiplicativeIdealWeight.ofIntegralIdealsAway 𝔪.support χ.onIdeals

/-- On an ideal prime to the modulus, the extended weight equals the character value. -/
@[simp]
theorem toMultiplicativeIdealWeight_apply_of_isPrimeTo (χ : RayClassCharacter 𝔪)
    {I : Ideal (𝓞 K)} (hI : Ideal.IsPrimeTo I 𝔪.support) :
    χ.toMultiplicativeIdealWeight I =
      (χ.onIdeals ⟨I, NumberFieldArithmetic.mem_integralIdealsAway_iff.mpr
        (Ideal.isPrimeTo_iff.mp hI)⟩ : ℂ) :=
  TauCeti.MultiplicativeIdealWeight.ofIntegralIdealsAway_apply_of_isPrimeTo χ.onIdeals hI

/-- The extended character vanishes on ideals meeting the finite part of its modulus. -/
@[simp]
theorem toMultiplicativeIdealWeight_apply_of_not_isPrimeTo (χ : RayClassCharacter 𝔪)
    {I : Ideal (𝓞 K)} (hI : ¬ Ideal.IsPrimeTo I 𝔪.support) :
    χ.toMultiplicativeIdealWeight I = 0 :=
  TauCeti.MultiplicativeIdealWeight.ofIntegralIdealsAway_apply_of_not_isPrimeTo χ.onIdeals hI

/-- The bad primes of the ideal weight are precisely the finite primes of the modulus. -/
@[simp]
theorem badPrimes_toMultiplicativeIdealWeight (χ : RayClassCharacter 𝔪) :
    χ.toMultiplicativeIdealWeight.badPrimes = 𝔪.support :=
  TauCeti.MultiplicativeIdealWeight.badPrimes_ofIntegralIdealsAway χ.onIdeals

/-- The trivial ray class character gives the indicator weight away from the modulus. -/
@[simp]
theorem toMultiplicativeIdealWeight_one :
    toMultiplicativeIdealWeight (1 : RayClassCharacter 𝔪) =
      TauCeti.MultiplicativeIdealWeight.ofBadPrimes 𝔪.support 𝔪.support.finite_toSet := by
  have h1 : (1 : RayClassCharacter 𝔪).onIdeals = 1 := by ext; simp
  rw [toMultiplicativeIdealWeight, h1,
    TauCeti.MultiplicativeIdealWeight.ofIntegralIdealsAway_one]

/-- Pointwise multiplication of ray class characters agrees with multiplication of ideal
weights, including at ideals meeting the modulus. -/
@[simp]
theorem toMultiplicativeIdealWeight_mul (χ ψ : RayClassCharacter 𝔪) :
    toMultiplicativeIdealWeight (χ * ψ) =
      χ.toMultiplicativeIdealWeight * ψ.toMultiplicativeIdealWeight := by
  have hmul : (χ * ψ).onIdeals = χ.onIdeals * ψ.onIdeals := by ext; simp
  rw [toMultiplicativeIdealWeight, hmul,
    TauCeti.MultiplicativeIdealWeight.ofIntegralIdealsAway_mul]
  rfl

/-- The inverse character gives the conjugate ideal weight, including at ideals meeting the
modulus, where both weights vanish. -/
@[simp]
theorem toMultiplicativeIdealWeight_inv (χ : RayClassCharacter 𝔪) :
    toMultiplicativeIdealWeight χ⁻¹ = χ.toMultiplicativeIdealWeight.conj := by
  ext I
  rw [MultiplicativeIdealWeight.conj_apply]
  by_cases hI : I.IsPrimeTo 𝔪.support
  · simp only [toMultiplicativeIdealWeight_apply_of_isPrimeTo _ hI, onIdeals_apply,
      MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    refine Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one ?_
      (Nat.card_pos (α := RayClassGroup 𝔪)).ne')
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  · simp [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo _ hI]

/-- Distinct ray class characters have distinct ideal weights: evaluation on the prime-to
integral ideals already determines a ray class character. -/
theorem toMultiplicativeIdealWeight_injective :
    Function.Injective (toMultiplicativeIdealWeight (𝔪 := 𝔪)) :=
  fun _ _ h ↦ RayClassCharacter.ext
    (DFunLike.congr_fun (TauCeti.MultiplicativeIdealWeight.ofIntegralIdealsAway_injective _ h))

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
    χ.toUnitaryIdealWeight.val = χ.toMultiplicativeIdealWeight := by
  simp [toUnitaryIdealWeight]

/-- At the trivial modulus, the trivial ray class character gives the everywhere-good trivial
unitary ideal weight. -/
@[simp]
theorem toUnitaryIdealWeight_one :
    (1 : RayClassCharacter (Modulus.one K)).toUnitaryIdealWeight = 1 := by
  apply Subtype.ext
  ext I
  by_cases hI : I = ⊥ <;> simp [Modulus.support_one, hI, Ideal.isPrimeTo_iff]

/-- The unitary extension respects pointwise multiplication of characters. -/
@[simp]
theorem toUnitaryIdealWeight_mul (χ ψ : RayClassCharacter 𝔪) :
    (χ * ψ).toUnitaryIdealWeight = χ.toUnitaryIdealWeight * ψ.toUnitaryIdealWeight := by
  apply Subtype.ext
  simp

/-- The ideal weight of the inverse character is the conjugate ideal weight. -/
@[simp]
theorem toUnitaryIdealWeight_inv (χ : RayClassCharacter 𝔪) :
    χ⁻¹.toUnitaryIdealWeight = χ.toUnitaryIdealWeight.conj := by
  apply Subtype.ext
  simp [UnitaryIdealWeight.val_conj]

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

/-- The extended weight of `χ` takes the same value on principal ideals `(a)` and `(b)` whenever
`a ≠ 0`, `b ≠ 0`, `b - a ∈ 𝔪.finitePart`, and `a`, `b` have the same strict sign at every real
place of `𝔪.infinitePart`. -/
theorem toMultiplicativeIdealWeight_span_eq_of_sub_mem (χ : RayClassCharacter 𝔪) {a b : 𝓞 K}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hsub : b - a ∈ 𝔪.finitePart)
    (hsign : ∀ w ∈ 𝔪.infinitePart,
      0 < InfinitePlace.embedding_of_isReal w.property (a : K) *
        InfinitePlace.embedding_of_isReal w.property (b : K)) :
    χ.toMultiplicativeIdealWeight (Ideal.span {b}) =
      χ.toMultiplicativeIdealWeight (Ideal.span {a}) := by
  by_cases ha : (Ideal.span {a}).IsPrimeTo 𝔪.support
  · have hb : (Ideal.span {b}).IsPrimeTo 𝔪.support :=
      (isPrimeTo_span_iff_of_sub_mem ha0 hb0 hsub).mpr ha
    rw [toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hb,
      toMultiplicativeIdealWeight_apply_of_isPrimeTo χ ha, onIdeals_apply, onIdeals_apply,
      idealClass_span_eq_of_sub_mem _ _ hsub hsign]
  · have hb : ¬ (Ideal.span {b}).IsPrimeTo 𝔪.support :=
      mt (isPrimeTo_span_iff_of_sub_mem ha0 hb0 hsub).mp ha
    rw [toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hb,
      toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ ha]

/-- **Periodicity of a ray class weight on positive natural integers.** For `k ≥ 1`, shifting `k`
by `Ideal.absNorm 𝔪.finitePart` leaves `χ.toMultiplicativeIdealWeight (Ideal.span {(k : 𝓞 K)})`
unchanged. -/
theorem toMultiplicativeIdealWeight_span_natCast_add_absNorm (χ : RayClassCharacter 𝔪) {k : ℕ}
    (hk : 1 ≤ k) :
    χ.toMultiplicativeIdealWeight (Ideal.span {((k + Ideal.absNorm 𝔪.finitePart : ℕ) : 𝓞 K)}) =
      χ.toMultiplicativeIdealWeight (Ideal.span {(k : 𝓞 K)}) := by
  refine χ.toMultiplicativeIdealWeight_span_eq_of_sub_mem (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega)) ?_ fun w _ ↦ ?_
  · push_cast
    rw [add_sub_cancel_left]
    exact Ideal.absNorm_mem 𝔪.finitePart
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hsumpos : (0 : ℝ) < (k + Ideal.absNorm 𝔪.finitePart : ℕ) := by exact_mod_cast (by omega)
    simpa using mul_pos hkpos hsumpos

end TauCeti.GlobalNumberFields.RayClassCharacter
